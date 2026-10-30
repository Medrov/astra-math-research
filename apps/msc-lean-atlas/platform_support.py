"""Small native process and file-lock primitives for Windows and POSIX."""
from __future__ import annotations

import errno
import os
from pathlib import Path
import signal
import subprocess
import time


def lock_file(stream, *, blocking=True):
    """Lock the first byte on Windows, or the whole file with POSIX flock.

    All atlas users of a lock file follow this same convention. A byte-range
    lock can extend beyond EOF, so existing empty lock files need no rewrite.
    """
    if os.name != 'nt':
        import fcntl
        flags = fcntl.LOCK_EX | (0 if blocking else fcntl.LOCK_NB)
        fcntl.flock(stream, flags)
        return
    import msvcrt
    stream.seek(0)
    while True:
        try:
            msvcrt.locking(stream.fileno(), msvcrt.LK_NBLCK, 1)
            return
        except OSError as error:
            if error.errno not in (errno.EACCES, errno.EAGAIN, errno.EDEADLK):
                raise
            if not blocking:
                raise BlockingIOError(error.errno, 'Lock is held by another worker') from error
            time.sleep(0.05)


def unlock_file(stream):
    if os.name != 'nt':
        import fcntl
        fcntl.flock(stream, fcntl.LOCK_UN)
        return
    import msvcrt
    stream.seek(0)
    msvcrt.locking(stream.fileno(), msvcrt.LK_UNLCK, 1)


def process_exists(pid):
    """Query liveness without sending a signal on Windows.

    Unknown/access-denied outcomes raise OSError so the caller can conservatively
    retain ownership. Windows os.kill(pid, 0) must never be used as a probe.
    """
    if os.name != 'nt':
        os.kill(pid, 0)
        return True
    import ctypes
    from ctypes import wintypes
    kernel = ctypes.WinDLL('kernel32', use_last_error=True)
    kernel.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
    kernel.OpenProcess.restype = wintypes.HANDLE
    kernel.GetExitCodeProcess.argtypes = [wintypes.HANDLE, ctypes.POINTER(wintypes.DWORD)]
    kernel.GetExitCodeProcess.restype = wintypes.BOOL
    kernel.CloseHandle.argtypes = [wintypes.HANDLE]
    kernel.CloseHandle.restype = wintypes.BOOL
    handle = kernel.OpenProcess(0x1000, False, pid)  # PROCESS_QUERY_LIMITED_INFORMATION
    if not handle:
        error = ctypes.get_last_error()
        if error == 87:  # ERROR_INVALID_PARAMETER: no process with this PID
            return False
        raise ctypes.WinError(error)
    try:
        code = wintypes.DWORD()
        if not kernel.GetExitCodeProcess(handle, ctypes.byref(code)):
            raise ctypes.WinError(ctypes.get_last_error())
        return code.value == 259  # STILL_ACTIVE
    finally:
        kernel.CloseHandle(handle)


def terminate_process_tree(process, timeout=3):
    """Stop this owned worker and its descendants, then reap the worker."""
    if process.poll() is not None:
        return
    if os.name == 'nt':
        taskkill = Path(os.environ.get('SystemRoot', r'C:\Windows')) / 'System32' / 'taskkill.exe'
        try:
            subprocess.run([str(taskkill), '/PID', str(process.pid), '/T', '/F'],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                           timeout=timeout, creationflags=subprocess.CREATE_NO_WINDOW)
        except (OSError, subprocess.TimeoutExpired):
            if process.poll() is None:
                process.kill()
        if process.poll() is None:
            process.kill()
        process.wait(timeout=timeout)
        return
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        process.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait(timeout=timeout)
