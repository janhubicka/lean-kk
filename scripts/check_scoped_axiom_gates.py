#!/usr/bin/env python3
"""Build and independently check all standalone Kk/*AxiomAudit.lean sources.

Run only after fetching the pinned Lean dependencies and Mathlib cache.
Unlike the central Kk.lean gate, this compiles every standalone scoped audit
and verifies the actual transitive axiom report for every named endpoint.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import subprocess
import sys

from scripts.audit_module_coverage import masked_code
from scripts.check_axiom_report import audit

REQUESTED = re.compile(r"(?m)^[ \t]*#print[ \t]+axioms[ \t]+(\S+)")


def discover(repo: Path) -> list[Path]:
    return sorted((repo / "Kk").glob("*AxiomAudit.lean"))


def check_one(source: str, report: str) -> list[str]:
    clean = masked_code(source)
    requested = REQUESTED.findall(clean)
    if not requested:
        return ["standalone audit source has no #print axioms command"]
    return audit(clean, report)


def run(repo: Path, results: Path) -> int:
    files = discover(repo)
    if not files:
        print("FAIL: no standalone Kk/*AxiomAudit.lean modules", file=sys.stderr)
        return 1
    results.mkdir(parents=True, exist_ok=True)
    modules = [".".join(path.relative_to(repo).with_suffix("").parts)
               for path in files]
    print("Building", len(modules), "standalone scoped audit modules", flush=True)
    compile_run = subprocess.run(["lake", "build", *modules], cwd=repo,
                                 capture_output=True, text=True)
    (results / "lake-build.log").write_text(
        compile_run.stdout + "\n" + compile_run.stderr, encoding="utf-8")
    if compile_run.returncode:
        print("FAIL: scoped Lake build", file=sys.stderr)
        print("\n".join((compile_run.stdout + compile_run.stderr).splitlines()[-70:]),
              file=sys.stderr)
        return 1
    report_count = 0
    failures: list[tuple[str, list[str]]] = []
    for i, path in enumerate(files, 1):
        rel = path.relative_to(repo)
        source = path.read_text(encoding="utf-8")
        result = subprocess.run(["lake", "env", "lean", str(rel)],
                                cwd=repo, capture_output=True, text=True)
        output = result.stdout + "\n" + result.stderr
        (results / (path.stem + ".log")).write_text(output, encoding="utf-8")
        issues = check_one(source, output) if result.returncode == 0 else [
            "Lean exited " + str(result.returncode),
            "\n".join(output.splitlines()[-25:]),
        ]
        if issues:
            failures.append((str(rel), issues))
            print("FAIL", rel, issues[:3], flush=True)
        else:
            count = len(REQUESTED.findall(masked_code(source)))
            report_count += count
            if i % 20 == 0 or i == len(files):
                print("Verified", i, "/", len(files),
                      "scoped modules; reports so far:", report_count, flush=True)
    if failures:
        print("FAIL: ", len(failures), "of", len(files),
              "scoped module axiom checks", file=sys.stderr)
        return 1
    print("PASS:", len(files), "scoped audit modules and", report_count,
          "exact standard-only transitive-axiom reports")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--reports", type=Path, default=Path("kk-scoped-audit-logs"))
    args = parser.parse_args()
    return run(args.repo.resolve(), args.reports.resolve())


if __name__ == "__main__":
    sys.exit(main())
