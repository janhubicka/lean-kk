#!/usr/bin/env python3
"""Auditable import-closure and source-token inventory for every local Lean file.

This is a structural audit, NOT a proof that the mathematics stated in
reachable modules implies the KK-free big Ramsey characterization.
"""
from __future__ import annotations

import argparse
from collections import Counter, deque
import json
from pathlib import Path
import re
import sys

IMPORT = re.compile(r"(?m)^\s*import[ \t]+([^\n]+)$")
RISK = re.compile(r"\b(sorry|admit|axiom|opaque|unsafe)\b")
PRINT = re.compile(r"(?m)^[ \t]*#print[ \t]+axioms[ \t]+(\S+)")
CHECK = re.compile(r"(?m)^[ \t]*#check[ \t]+@?(\S+)")


def masked_code(source: str) -> str:
    """Erase nested Lean comments and string literals while preserving newlines."""
    output: list[str] = []
    i, nested, in_line, in_string = 0, 0, False, False
    while i < len(source):
        ch, pair = source[i], source[i:i+2]
        if in_line:
            if ch == "\n":
                in_line = False
                output.append("\n")
            else:
                output.append(" ")
            i += 1
            continue
        if nested:
            if pair == "/-":
                nested += 1
                output.extend("  ")
                i += 2
            elif pair == "-/":
                nested -= 1
                output.extend("  ")
                i += 2
            else:
                output.append("\n" if ch == "\n" else " ")
                i += 1
            continue
        if in_string:
            if ch == "\\" and i + 1 < len(source):
                output.extend("  ")
                i += 2
            else:
                if ch == '"':
                    in_string = False
                output.append("\n" if ch == "\n" else " ")
                i += 1
            continue
        if pair == "--":
            in_line = True
            output.extend("  ")
            i += 2
        elif pair == "/-":
            nested = 1
            output.extend("  ")
            i += 2
        elif ch == '"':
            in_string = True
            output.append(" ")
            i += 1
        else:
            output.append(ch)
            i += 1
    if nested or in_string:
        raise ValueError("unterminated Lean comment or string")
    return "".join(output)


def analyze(repo: Path) -> dict:
    paths = sorted((repo / "Kk").rglob("*.lean"))
    root = repo / "Kk.lean"
    if not root.exists():
        raise ValueError("missing central root Kk.lean")
    all_paths = [root] + paths + sorted((repo / "scripts").glob("*.lean"))
    files = {".".join(p.relative_to(repo).with_suffix("").parts): p
             for p in all_paths}
    dependencies: dict[str, list[str]] = {}
    flags: list[dict] = []
    for module, path in files.items():
        raw = path.read_text(encoding="utf-8")
        src = masked_code(raw)
        deps = []
        for match in IMPORT.finditer(src):
            deps += match.group(1).split()
        dependencies[module] = deps
        for match in RISK.finditer(src):
            line = src.count("\n", 0, match.start()) + 1
            flags.append({"module": module, "path": str(path.relative_to(repo)),
                          "line": line, "token": match.group(1)})
    seen, stack = set(), deque(["Kk"])
    while stack:
        item = stack.popleft()
        if item in seen:
            continue
        seen.add(item)
        stack.extend(dep for dep in dependencies.get(item, [])
                     if dep in files and dep not in seen)
    local_missing = sorted({dep for module in seen
                            for dep in dependencies.get(module, [])
                            if dep.startswith("Kk.") and dep not in files})
    # The central target does not build every standalone scoped axiom gate.
    source_modules = sorted(x for x in files if x.startswith("Kk."))
    excluded = sorted(x for x in source_modules if x not in seen)
    direct = [x for x in dependencies["Kk"] if x.startswith("Kk.")]
    central = masked_code(root.read_text(encoding="utf-8"))
    central_gate = repo / "scripts/check_axioms.lean"
    gate = masked_code(central_gate.read_text(encoding="utf-8"))
    checks, prints = CHECK.findall(gate), PRINT.findall(gate)
    missing_print = sorted(set(checks) - set(prints))
    report = {
        "root": "Kk",
        "total_kK_modules": len(source_modules),
        "root_direct_local_imports": len(direct),
        "root_reachable_modules_including_root": len(seen),
        "unreachable_local_modules": excluded,
        "unreachable_count": len(excluded),
        "missing_local_imports": local_missing,
        "central_checks": len(checks),
        "central_print_axioms": len(prints),
        "central_check_without_print": missing_print,
        "suspicious_source_tokens": flags,
        "suspicious_token_counts": dict(sorted(Counter(x["token"] for x in flags).items())),
        "scope": ("A successful lake build Kk certifies only reachable imports; "
                  "standalone files outside the closure need their own exact-head "
                  "build. This scan is not a kernel proof, a replacement for "
                  "transitive axiom reports, or global diary verification."),
    }
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    info = analyze(args.repo)
    output = json.dumps(info, indent=2, ensure_ascii=False) + "\n"
    if args.output:
        args.output.write_text(output, encoding="utf-8")
    print("Local Kk source modules:", info["total_kK_modules"])
    print("Root-direct Kk imports:", info["root_direct_local_imports"])
    print("Transitive source modules missing from central Kk target:",
          info["unreachable_count"])
    print("Central #check / #print axioms:",
          info["central_checks"], "/", info["central_print_axioms"])
    print("Direct-only checked names:", len(info["central_check_without_print"]))
    print("Source tokens requiring review:", info["suspicious_token_counts"])
    print("Missing internal module imports:", info["missing_local_imports"])
    print("Uncovered module names:", info["unreachable_local_modules"])
    if info["missing_local_imports"]:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
