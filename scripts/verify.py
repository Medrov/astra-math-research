"""Compile the MathResearch proof files against an existing, read-only Lean/mathlib installation.

The argument paths are recorded in verification.json. No download, external build,
native_decide, or changes to the borrowed installation are performed.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time
from datetime import datetime, timezone

parser = argparse.ArgumentParser()
parser.add_argument("--lean", required=True, type=Path)
parser.add_argument("--mathlib", required=True, type=Path)
parser.add_argument("--files", nargs="*")
args = parser.parse_args()
root = Path(__file__).resolve().parents[1]
started_at_utc = datetime.now(timezone.utc).isoformat()
build = root / ".lake/build/lib/lean"
build.mkdir(parents=True, exist_ok=True)
mathlib = args.mathlib.resolve()
paths = [build, root, mathlib / ".lake/build/lib/lean"]
for package in json.loads((mathlib / "lake-manifest.json").read_text(encoding="utf-8"))["packages"]:
    lib = mathlib.parent / package["name"] / ".lake/build/lib/lean"
    if lib.is_dir():
        paths.append(lib)
env = os.environ.copy()
env["LEAN_PATH"] = os.pathsep.join(str(p) for p in paths)
version = subprocess.run([str(args.lean), "--version"], capture_output=True, text=True, check=True).stdout.strip()
mathlib_revision = subprocess.run(
    ["git", "-C", str(mathlib), "rev-parse", "HEAD"],
    capture_output=True, text=True, check=True,
).stdout.strip()
expected_revision = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
if mathlib_revision != expected_revision:
    raise SystemExit(f"Wrong mathlib revision: {mathlib_revision}; expected {expected_revision}")
if "version 4.19.0," not in version:
    raise SystemExit(f"Wrong Lean version: {version}")
files = args.files or [
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
discovered_files = []
for folder, directories, names in os.walk(root):
    directories[:] = [name for name in directories if name not in {'.lake', '.git', '.tooling', 'node_modules'}]
    discovered_files.extend((Path(folder) / name).relative_to(root).as_posix()
                            for name in names if name.endswith('.lean'))
discovered_files.sort()
full_project_coverage = set(files) == set(discovered_files)
if not args.files and not full_project_coverage:
    raise SystemExit(f"Default verification list differs from project Lean sources: {discovered_files}")
logs = root / "verification"
logs.mkdir(exist_ok=True)
results = []
for relative in files:
    source = root / relative
    if not source.is_file():
        raise SystemExit(f"Missing proof source: {source}")
    text = source.read_text(encoding="utf-8")
    source_hash_before = hashlib.sha256(source.read_bytes()).hexdigest()
    # Comments may describe forbidden constructs. Scan executable lines as well.
    code = re.sub(r"/-.*?-/", "", text, flags=re.S)
    code = re.sub(r"--[^\n]*", "", code)
    forbidden = re.findall(r"(?m)^\s*(?:axiom\s|opaque\s)|\b(?:sorry|admit|native_decide|unsafe)\b", code)
    if forbidden:
        raise SystemExit(f"Forbidden construct in {relative}: {forbidden}")
    declarations = re.findall(r"(?m)^\s*(?:(?:private|protected)\s+)?(?:theorem|lemma)\s+([^\s:(]+)", code)
    axiom_commands = re.findall(r"(?m)^\s*#print\s+axioms\s+([^\s]+)", code)
    printed_names = {name.rsplit(".", 1)[-1] for name in axiom_commands}
    missing_audits = sorted(set(declarations) - printed_names)
    if missing_audits:
        raise SystemExit(f"Theorems without axiom audit in {relative}: {missing_audits}")
    target = build / Path(relative).with_suffix(".olean")
    target.parent.mkdir(parents=True, exist_ok=True)
    command = [str(args.lean), "-o", str(target), str(source)]
    print(f"Checking {relative} ...", flush=True)
    started = time.monotonic()
    log_path = logs / (Path(relative).stem + ".log")
    with log_path.open("w", encoding="utf-8") as log_stream:
        run = subprocess.run(command, env=env, cwd=root,
                             stdout=log_stream, stderr=subprocess.STDOUT, text=True)
    elapsed = time.monotonic() - started
    source_hash_after = hashlib.sha256(source.read_bytes()).hexdigest()
    if source_hash_before != source_hash_after:
        raise SystemExit(f"Source changed during compilation: {relative}")
    output = log_path.read_text(encoding="utf-8")
    reported_axioms = {
        name.strip()
        for group in re.findall(r"depends on axioms: \[([^\]]*)\]", output)
        for name in group.split(",") if name.strip()
    }
    unexpected_axioms = sorted(reported_axioms - {"propext", "Classical.choice", "Quot.sound"})
    bad_axioms = bool(unexpected_axioms)
    result = {
        "file": relative,
        "theorem_count": len(declarations),
        "theorems": declarations,
        "axiom_audit_commands": len(axiom_commands),
        "sha256": source_hash_after,
        "source_unchanged_during_compilation": True,
        "command": command,
        "olean_sha256": hashlib.sha256(target.read_bytes()).hexdigest() if run.returncode == 0 else None,
        "exit_code": run.returncode,
        "elapsed_seconds": round(elapsed, 3),
        "forbidden_axiom_seen": bad_axioms,
        "reported_axioms": sorted(reported_axioms),
        "unexpected_axioms": unexpected_axioms,
        "log": str((logs / (Path(relative).stem + ".log")).relative_to(root)),
        "axiom_output": output,
        "log_sha256": hashlib.sha256(log_path.read_bytes()).hexdigest(),
    }
    results.append(result)
    print(f"{relative}: exit={run.returncode}, seconds={elapsed:.3f}", flush=True)
    if output:
        print(output if len(output) <= 6000 else output[:6000] + "\n[Full output in log file]", flush=True)
    if run.returncode or bad_axioms:
        break
report = {
    "started_at_utc": started_at_utc,
    "checked_at_utc": datetime.now(timezone.utc).isoformat(),
    "lean_version": version,
    "lean_binary": str(args.lean.resolve()),
    "mathlib_root": str(mathlib),
    "mathlib_revision": mathlib_revision,
    "method": "fresh source elaboration and kernel type checking; printed dependency axioms",
    "external_checker": "not run",
    "requested_files": files,
    "discovered_project_lean_files": discovered_files,
    "full_project_coverage": full_project_coverage,
    "verifier_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    "results": results,
    "theorem_count": sum(r["theorem_count"] for r in results),
    "success": len(results) == len(files) and all(r["exit_code"] == 0 and not r["forbidden_axiom_seen"] for r in results),
}
(logs / "verification.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
raise SystemExit(0 if report["success"] else 1)
