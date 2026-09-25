#!/usr/bin/env python3
"""Run the project's Lean, lint, axiom, and paper-map checks."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import tomllib


ROOT = Path(__file__).resolve().parents[1]
AUDIT = ROOT / ".audit"
ANSI = re.compile(r"\x1b\[[0-9;]*[A-Za-z]")
WARNING = re.compile(r"(^|\s)warning:|⚠", re.MULTILINE)
LEAN_TEST_OPTIONS = [
    "-DautoImplicit=false", "-Dlinter.mathlibStandardSet=true",
    "-Dlinter.style.header=true", "-Dlinter.style.longFile=1500",
    "-DwarningAsError=true",
]


def source_hashes() -> dict[str, str]:
    """Record inputs independently of the current Git staging state."""
    files = [ROOT / name for name in [
        "T3.lean", "Challenge.lean", "Solution.lean", "lean-toolchain", "lakefile.toml",
        "lake-manifest.json", "formalization.yaml", "comparator.json",
        "requirements-palomar.txt", "LICENSE", "scripts/palomar-schema/LICENSE",
        "scripts/palomar-schema/PALOMAR-LICENSE",
    ]]
    paper_map = tomllib.loads((ROOT / "docs/paper-map.toml").read_text())
    files.extend(ROOT / source["path"] for source in
                 [paper_map["source"], *paper_map.get("archived_sources", [])])
    for directory, suffix in [("T3", ".lean"), ("Tests", ".lean"),
                              ("scripts", ".py"), ("scripts", ".sh"), ("scripts", ".json"),
                              ("docs", ".toml"), ("docs", ".md")]:
        files.extend((ROOT / directory).rglob(f"*{suffix}"))
    return {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(files)}


def run_step(name: str, command: list[str], env: dict[str, str]) -> dict:
    print(f"[{name}] {' '.join(command)}", flush=True)
    started = time.monotonic()
    result = subprocess.run(command, cwd=ROOT, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False)
    output = ANSI.sub("", result.stdout)
    (AUDIT / f"{name}.log").write_text(output)
    warnings = len(WARNING.findall(output))
    record = {"name": name, "command": command, "exit_code": result.returncode,
              "warnings": warnings, "seconds": round(time.monotonic() - started, 3)}
    if result.returncode or warnings:
        print(output[-16000:], end="", flush=True)
        print(f"[{name}] FAILED: exit={result.returncode}, warnings={warnings}", flush=True)
    else:
        print(f"[{name}] passed ({record['seconds']}s)", flush=True)
    return record


def main() -> int:
    AUDIT.mkdir(exist_ok=True)
    env = os.environ.copy()
    env["NO_COLOR"] = "1"
    env["T3_DECLARATIONS_JSON"] = str(AUDIT / "declarations.json")
    # A failed axiom check must never leave an earlier manifest available to the paper-map check.
    (AUDIT / "declarations.json").unlink(missing_ok=True)
    before = source_hashes()
    report = {"schema_version": 1, "inputs": before, "steps": [], "passed": False}
    report_path = AUDIT / "checks.json"
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    steps = [
        ("palomar-metadata", [sys.executable, "scripts/check_palomar_metadata.py"]),
        ("paper-map-fixtures", [sys.executable, "scripts/test_paper_map.py"]),
        ("build", ["lake", "build"]),
        ("imports", ["lake", "exe", "mk_all", "--check", "--lib", "T3"]),
        ("environment-lint", ["lake", "lint", "--", "--no-build", "T3"]),
        ("text-lint", ["lake", "env", "lean", *LEAN_TEST_OPTIONS, "Tests/TextLint.lean"]),
        ("axioms", ["lake", "env", "lean", *LEAN_TEST_OPTIONS, "Tests/Axioms.lean"]),
        ("paper-map", [sys.executable, "scripts/paper_map.py", "--check",
                       "--declarations-json", str(AUDIT / "declarations.json")]),
    ]
    for name, command in steps:
        record = run_step(name, command, env)
        report["steps"].append(record)
        report_path.write_text(json.dumps(report, indent=2) + "\n")
        if record["exit_code"] or record["warnings"]:
            return 1
    report["inputs_unchanged"] = before == source_hashes()
    report["passed"] = report["inputs_unchanged"]
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    if not report["passed"]:
        print("Inputs changed during the checks; rerun on a stable snapshot.", file=sys.stderr)
        return 1
    print("All checks passed with zero warnings; report: .audit/checks.json")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
