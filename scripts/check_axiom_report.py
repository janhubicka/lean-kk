#!/usr/bin/env python3
"""Fail CI unless each named Lean endpoint has exactly the allowed axioms.

Run after: lake env lean scripts/check_axioms.lean | tee axioms.log
This checks the actual transitive axiom reports, not merely the absence
of sorryAx or the name of the theorem being checked.
"""

from collections import Counter
from pathlib import Path
import re
import sys

ALLOWED = frozenset({"propext", "Classical.choice", "Quot.sound"})
REQUESTED = re.compile(r"(?m)^[ \t]*#print[ \t]+axioms[ \t]+(\S+)")
REPORTED = re.compile(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]")
NO_AXIOMS = re.compile(r"'([^']+)'\s+does not depend on any axioms")


def audit(source: str, report: str) -> list[str]:
    expected = Counter(REQUESTED.findall(source))
    observed = []
    invalid = []
    for name, raw_axioms in REPORTED.findall(report):
        observed.append(name)
        axioms = {a.strip() for a in raw_axioms.split(",") if a.strip()}
        extras = sorted(axioms - ALLOWED)
        if extras:
            invalid.append(f"{name}: unapproved transitive axioms {', '.join(extras)}")
    observed.extend(NO_AXIOMS.findall(report))
    actual = Counter(observed)
    issues = []
    if not expected:
        issues.append("no #print axioms commands found in the Lean audit source")
    for name in sorted(expected.keys() | actual.keys()):
        if expected[name] != actual[name]:
            issues.append(
                f"{name}: requested {expected[name]} axiom report(s), "
                f"found {actual[name]}"
            )
    issues.extend(invalid)
    if "sorryAx" in report or "unknownConstant" in report:
        issues.append("Lean report contains sorryAx or unknownConstant")
    return issues


def self_test() -> None:
    src = "#print axioms Kk.alpha\n#print axioms Kk.beta\n"
    good = (
        "'Kk.alpha' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        "'Kk.beta' depends on axioms: [propext, Quot.sound]\n"
    )
    assert audit(src, good) == []
    assert audit(src, good.replace("Quot.sound]", "Hidden.oracle]", 1))
    assert audit(src, good.splitlines()[0] + "\n")
    assert audit(src, good + good.splitlines()[0] + "\n")
    assert audit(src, good.replace("Kk.beta", "Kk.other"))
    assert audit(src, good + "sorryAx")
    assert audit(src, "'Kk.alpha' does not depend on any axioms\n" + good.splitlines()[1]) == []
    print("PASS: axiom-report parser rejects missing/extra/custom-axiom reports")


def main() -> int:
    if len(sys.argv) == 2 and sys.argv[1] == "--self-test":
        self_test()
        return 0
    if len(sys.argv) != 3:
        print("usage: check_axiom_report.py AUDIT.lean axioms.log", file=sys.stderr)
        return 2
    issues = audit(Path(sys.argv[1]).read_text(), Path(sys.argv[2]).read_text())
    if issues:
        for item in issues:
            print("FAIL: " + item, file=sys.stderr)
        return 1
    count = len(REQUESTED.findall(Path(sys.argv[1]).read_text()))
    print(f"PASS: {count} exact transitive-axiom reports; only {', '.join(sorted(ALLOWED))}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
