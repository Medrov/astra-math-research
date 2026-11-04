"""Replay the exact published example, without models or network access.

From the repository root: lake env python apps/msc-lean-atlas/examples/fibonacci_composition/verify.py
Only the Python standard library is required. Generated files go to the ignored
application verification directory, never into this package or historical runs.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
import uuid


PACKAGE = Path(__file__).resolve().parent
APP = PACKAGE.parents[1]
REPO = APP.parents[1]
PAYLOAD = ("Candidate.lean", "Contract.lean", "Axioms.lean", "contract.json",
           "verification-reference.json")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def check_package():
    provenance = read_json(PACKAGE / "provenance.json")
    expected = provenance["files_sha256"]
    if set(expected) != set(PAYLOAD):
        raise ValueError("The published package manifest has an unexpected file set.")
    actual = {name: sha(PACKAGE / name) for name in PAYLOAD}
    if actual != expected:
        raise ValueError("Published file hashes do not match; no proof was checked.")
    contract = read_json(PACKAGE / "contract.json")
    obligations = contract["required_obligations"]
    if (len(obligations) != 4 or len({o["target"] for o in obligations}) != 4
            or contract["target"] != provenance["expected"]["primary_target"]):
        raise ValueError("Expected the exact primary target and four distinct obligations.")
    expected_contract = "import Candidate\nuniverse u v w\nset_option autoImplicit false\n"
    for goal in [contract, *obligations]:
        expected_contract += f"example : (\n{goal['statement']}\n) := @{goal['target']}\n"
    if (PACKAGE / "Contract.lean").read_text(encoding="utf-8") != expected_contract:
        raise ValueError("Contract.lean does not contain exactly the five expected type checks.")
    return provenance, contract, actual


def git_revision(folder):
    result = subprocess.run(["git", "-C", str(folder), "rev-parse", "HEAD"],
                            capture_output=True, text=True, encoding="utf-8", timeout=15)
    if result.returncode:
        raise ValueError(f"Cannot verify the pinned checkout of {folder.name}.")
    return result.stdout.strip()


def prepare_environment(provenance, work):
    pinned = provenance["environment"]
    if (REPO / "lean-toolchain").read_text().strip() != pinned["lean_toolchain"]:
        raise ValueError("The repository Lean toolchain differs from the published example.")
    manifest = read_json(REPO / "lake-manifest.json")
    packages = manifest["packages"]
    mathlib = next(p for p in packages if p["name"] == "mathlib")
    if mathlib["rev"] != pinned["mathlib_revision"]:
        raise ValueError("The repository mathlib pin differs from the published example.")
    paths, revisions = [work], {}
    for package in packages:
        folder = REPO / manifest["packagesDir"] / package["name"]
        revision = git_revision(folder)
        if revision != package["rev"]:
            raise ValueError(f"Dependency revision mismatch: {package['name']}.")
        revisions[package["name"]] = revision
        cache = folder / ".lake/build/lib/lean"
        if cache.is_dir():
            paths.append(cache)
        elif package["name"] == "mathlib":
            raise ValueError("Missing mathlib cache; prepare it with lake exe cache get.")
    env = os.environ.copy()
    # Never import a historical Candidate.olean or ambient user Lean modules.
    env["LEAN_PATH"] = os.pathsep.join(str(p) for p in paths)
    return env, revisions


def execute(lean, args, work, env, report):
    started = time.monotonic()
    entry = {"command": ["lean", *args], "exit_code": None}
    try:
        result = subprocess.run([lean, *args], cwd=work, env=env,
                                capture_output=True, text=True, encoding="utf-8",
                                errors="replace", timeout=120)
        entry.update(exit_code=result.returncode, stdout=result.stdout, stderr=result.stderr)
    except subprocess.TimeoutExpired:
        entry.update(timeout=True, stdout="", stderr="Lean exceeded the 120-second command limit.")
    finally:
        entry["elapsed_seconds"] = round(time.monotonic() - started, 3)
        report["checks"].append(entry)
    if entry["exit_code"] != 0:
        raise RuntimeError("Failed check: " + " ".join(entry["command"]))
    return entry["stdout"]


def parse_axioms(stdout, expected):
    observed = {}
    for line in stdout.splitlines():
        match = re.fullmatch(r"'([^']+)' depends on axioms: \[([^]]*)\]", line.strip())
        if not match:
            raise ValueError("Unexpected literal #print axioms output; audit is incomplete.")
        name, raw = match.groups()
        if name in observed:
            raise ValueError("Duplicate theorem in axiom output.")
        axioms = [a.strip() for a in raw.split(",") if a.strip()]
        if set(axioms) - set(expected["allowed_axioms"]):
            raise ValueError(f"Unexpected logical axiom dependency of {name}.")
        observed[name] = axioms
    if set(observed) != set(expected["audited_theorems"]):
        raise ValueError("Missing or unexpected theorem in literal axiom audit.")
    return observed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default=os.environ.get("ATLAS_LEAN") or shutil.which("lean"),
                        help="Lean executable; default: ATLAS_LEAN or the current Lake environment.")
    parser.add_argument("--output", type=Path,
                        help="Parent directory for a fresh workspace; default: app/verification/fibonacci-composition.")
    parser.add_argument("--check-only", action="store_true",
                        help="Check package hashes and exact contract text only; do not invoke Lean.")
    args = parser.parse_args()
    try:
        provenance, contract, hashes = check_package()
    except (OSError, ValueError, KeyError) as error:
        print(str(error), file=sys.stderr)
        return 1
    if args.check_only:
        print(json.dumps(dict(package_integrity=True, required_obligations=4, lean_invoked=False)))
        return 0
    if not args.lean:
        print("Lean is unavailable. Use lake env python or supply --lean /path/to/lean.", file=sys.stderr)
        return 1
    lean = shutil.which(args.lean) or str(Path(args.lean).expanduser().resolve())
    output = (args.output or APP / "verification/fibonacci-composition").resolve()
    if output == PACKAGE or PACKAGE in output.parents:
        print("Generated artifacts must be outside the example package.", file=sys.stderr)
        return 1
    work = output / (datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ-") + uuid.uuid4().hex[:8])
    work.mkdir(parents=True)
    report = dict(kind="fresh_portable_example_replay", success=False,
                  started_at=datetime.now(timezone.utc).isoformat(), model_calls=0,
                  source_sha256=hashes, checks=[], required_obligations=4,
                  semantic_review="not_repeated", source_application_status="not_verified",
                  novelty="not_assessed", seed=None,
                  methodology="deterministic replay of available proof; not rediscovery")
    try:
        env, revisions = prepare_environment(provenance, work)
        version = execute(lean, ["--version"], work, env, report).strip()
        expected_version = provenance["environment"]["lean_version"]
        if not re.search(r"\bversion " + re.escape(expected_version) + r"(?:,|\))", version):
            raise ValueError("Lean executable version does not match the published pin.")
        report["environment"] = dict(lean_version=version, dependency_revisions=revisions,
                                     dependency_cache="reused; not rebuilt")
        for name in ("Candidate.lean", "Contract.lean", "Axioms.lean"):
            shutil.copyfile(PACKAGE / name, work / name)
        execute(lean, ["-o", "Candidate.olean", "Candidate.lean"], work, env, report)
        execute(lean, ["-o", "Contract.olean", "Contract.lean"], work, env, report)
        stdout = execute(lean, ["Axioms.lean"], work, env, report)
        report["axioms"] = parse_axioms(stdout, provenance["expected"])
        report.update(success=True, target_preserved=True, obligations_passed=True,
                      obligations=[dict(id=o["id"], target=o["target"], ok=True)
                                   for o in contract["required_obligations"]])
    except (OSError, ValueError, KeyError, RuntimeError, subprocess.SubprocessError) as error:
        report["error"] = str(error)
    report["finished_at"] = datetime.now(timezone.utc).isoformat()
    (work / "verification.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n",
                                            encoding="utf-8")
    print(json.dumps(dict(success=report["success"], report=str(work / "verification.json")), ensure_ascii=False))
    return 0 if report["success"] else 1


if __name__ == "__main__":
    sys.exit(main())
