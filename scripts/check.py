#!/usr/bin/env python3
"""Fail-closed, full-project wrapper around the unchanged historical verifier.

Use a prepared Lean/mathlib installation. This script does not install tools or
fetch dependencies. Run it from any working directory; paths below are relative
to this copy of the repository, not to a historical author's machine.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import uuid


ROOT = Path(__file__).resolve().parents[1]
EXPECTED_MATHLIB = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
FILES = [
    "MathResearch/MinimalAInfinity.lean",
    "MathResearch/AlbertObstruction.lean",
    "MathResearch/AlbertMatrix.lean",
    "MathResearch/Derivations.lean",
    "MathResearch/AssociativeBridge.lean",
    "MathResearch/TripleBridge.lean",
    "MathResearch/ProbeLowerBound.lean",
    "MathResearch/AlbertSpectralGeometry.lean",
    "MathResearch/SpectralDefect.lean",
    "MathResearch/OctonionIncidence.lean",
    "MathResearch.lean",
]
IGNORED_DIRS = {".lake", ".git", ".venv", "node_modules", "__pycache__"}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def utc_now():
    return datetime.now(timezone.utc).isoformat()


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def atomic_json(path, value):
    """Publish either a complete JSON object or the previous complete object."""
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w", encoding="utf-8", dir=path.parent,
            prefix=".verification-", suffix=".tmp", delete=False,
        ) as stream:
            temporary = Path(stream.name)
            json.dump(value, stream, ensure_ascii=False, indent=2)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def discover_sources():
    found = []
    for folder, directories, names in os.walk(ROOT):
        directories[:] = [name for name in directories if name not in IGNORED_DIRS]
        # Application fixtures have their own verifier and are outside this
        # unchanged 11-module mathematical package.
        if Path(folder) == ROOT and "apps" in directories:
            directories.remove("apps")
        found.extend(str((Path(folder) / name).relative_to(ROOT))
                     for name in names if name.endswith(".lean"))
    return sorted(found)


def git_revision(folder):
    return subprocess.run(
        ["git", "-C", str(folder), "rev-parse", "HEAD"],
        check=True, capture_output=True, text=True,
    ).stdout.strip()


def prepared_mathlib(path):
    """The preserved verifier expects mathlib and its dependencies as siblings."""
    if not path.is_dir():
        raise RuntimeError("Prepared mathlib not found. Run lake update and lake exe cache get first.")
    revision = git_revision(path)
    if revision != EXPECTED_MATHLIB:
        raise RuntimeError(f"Wrong mathlib revision: {revision}; expected {EXPECTED_MATHLIB}")
    if not (path / ".lake/build/lib/lean").is_dir():
        raise RuntimeError("mathlib build cache not found. Run lake exe cache get first.")
    manifest = json.loads((path / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        dependency = path.parent / package["name"]
        # Cache downloads need not build an unused inherited package (for
        # example Cli). Any actually imported missing module still fails Lean.
        if not package.get("inherited", False) and not (dependency / ".lake/build/lib/lean").is_dir():
            raise RuntimeError(
                "Missing sibling dependency cache: " + package["name"]
                + ". Use the standard project lake update / cache get layout."
            )
        if package.get("type") == "git" and git_revision(dependency) != package["rev"]:
            raise RuntimeError("Dependency revision differs from pinned mathlib manifest: " + package["name"])


def parser():
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--lean", type=Path,
                        help="Prepared Lean executable; defaults to lean on PATH (4.19.0 required).")
    result.add_argument("--mathlib", type=Path, default=ROOT / ".lake/packages/mathlib",
                        help="Prepared pinned mathlib checkout, with sibling dependency caches.")
    return result


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if argv in (["--help"], ["-h"]):
        parser().print_help()
        return 0
    logs = ROOT / "verification"
    logs.mkdir(parents=True, exist_ok=True)
    certificate = logs / "verification.json"
    report = {
        "success": False,
        "status": "incomplete",
        "run_id": uuid.uuid4().hex,
        "started_at_utc": utc_now(),
        "requested_files": FILES,
        "results": [],
        "theorem_count": 0,
        "external_checker": "not run",
        "wrapper_sha256": digest(Path(__file__)),
    }
    # Invalidate a previous success before parsing arguments or checking tools.
    # The child writes only inside its temporary workspace. An exception, failed
    # preflight or killed wrapper therefore cannot expose an old success as new.
    atomic_json(certificate, report)
    try:
        args = parser().parse_args(argv)
        discovered = discover_sources()
        if discovered != sorted(FILES):
            raise RuntimeError("Expected exactly the canonical eleven Lean sources; found: " + repr(discovered))
        hashes = {relative: digest(ROOT / relative) for relative in FILES}
        verifier = ROOT / "scripts/verify.py"
        verifier_hash = digest(verifier)
        lean = args.lean
        if lean is None:
            located = shutil.which("lean")
            if located is None:
                raise RuntimeError("Lean not on PATH. Prepare the toolchain or pass --lean.")
            lean = Path(located)
        # Keep an elan shim's basename: resolving its symlink can execute elan
        # rather than lean. The preserved verifier itself checks --version.
        lean = lean.expanduser().absolute()
        if not lean.is_file() or not os.access(lean, os.X_OK):
            raise RuntimeError("Lean executable is missing or not executable.")
        mathlib = args.mathlib.expanduser().resolve()
        prepared_mathlib(mathlib)
        work = ROOT / ".lake/check-runs"
        work.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="run-", dir=work) as directory:
            stage = Path(directory)
            for relative in FILES + ["scripts/verify.py", "lean-toolchain"]:
                target = stage / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / relative, target)
            run = subprocess.run(
                [sys.executable, str(stage / "scripts/verify.py"),
                 "--lean", str(lean), "--mathlib", str(mathlib)],
                cwd=stage,
            )
            staged_report = stage / "verification/verification.json"
            if staged_report.is_file():
                child = json.loads(staged_report.read_text())
                child.update({key: report[key] for key in
                              ("run_id", "started_at_utc", "wrapper_sha256")})
                report = child
            for relative in FILES:
                name = Path(relative).stem + ".log"
                source = stage / "verification" / name
                if source.is_file():
                    shutil.copyfile(source, logs / name)
            if run.returncode != 0:
                raise RuntimeError(f"Verifier exited with code {run.returncode}; inspect the current run's logs.")
            if not report.get("success") or not report.get("full_project_coverage"):
                raise RuntimeError("Verifier did not report a complete successful check.")
            if report.get("requested_files") != FILES or report.get("discovered_project_lean_files") != sorted(FILES):
                raise RuntimeError("Verifier certificate does not cover exactly the eleven canonical sources.")
            if report.get("verifier_sha256") != verifier_hash or digest(verifier) != verifier_hash:
                raise RuntimeError("Verifier changed during this check.")
            if discover_sources() != discovered:
                raise RuntimeError("The set of project Lean sources changed during this check.")
            results = report.get("results", [])
            if [item["file"] for item in results] != FILES:
                raise RuntimeError("Verifier result list is incomplete or reordered.")
            for item in results:
                relative = item["file"]
                if item.get("exit_code") != 0 or item.get("forbidden_axiom_seen"):
                    raise RuntimeError("A compilation or axiom audit failed: " + relative)
                if not set(item.get("reported_axioms", [])) <= ALLOWED_AXIOMS:
                    raise RuntimeError("Unexpected proof dependencies: " + relative)
                if item.get("sha256") != hashes[relative] or digest(ROOT / relative) != hashes[relative]:
                    raise RuntimeError("Project source changed during this check: " + relative)
                if digest(logs / Path(item["log"]).name) != item["log_sha256"]:
                    raise RuntimeError("Copied log hash mismatch: " + relative)
                built = Path(".lake/build/lib/lean") / Path(relative).with_suffix(".olean")
                if digest(stage / built) != item["olean_sha256"]:
                    raise RuntimeError("Compiled object hash mismatch: " + relative)
                target = ROOT / built
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(stage / built, target)
        report.update({"success": True, "status": "complete", "checked_at_utc": utc_now(),
                       "wrapper_method": "fresh isolated source snapshot; unchanged verifier; full coverage and hash checks"})
        atomic_json(certificate, report)
        print(f"PASS: {len(FILES)} Lean files; {report['theorem_count']} theorem/lemma declarations.")
        print("Certificate: verification/verification.json")
        return 0
    except (Exception, KeyboardInterrupt, SystemExit) as error:
        report.update({"success": False, "status": "failed", "checked_at_utc": utc_now(),
                       "error": str(error) or type(error).__name__})
        atomic_json(certificate, report)
        print("FAIL: " + report["error"], file=sys.stderr)
        return 130 if isinstance(error, KeyboardInterrupt) else 1


if __name__ == "__main__":
    raise SystemExit(main())
