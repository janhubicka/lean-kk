# Standalone production module integration — adversarial rationale (22 November 2026)

The independent full-repository structural checker in PR #463 identified
**198** local Kk modules not transitively reached by the default root build:
**142** dedicated AxiomAudit harnesses plus **56** non-harness production modules.

The 56 non-harness modules include previous Track D zero-stage/Plan work,
Track E conditional physical old-prefix/crossing results, Track F marker
fans and code stages, and Track G exact factor-Bad/coordinate transport.
Many were individually exact-head verified on dedicated branches, but do NOT
currently regression-compile with the latest central default Kk target.

This integration adds precisely these 56 imports, with no modification of
any mathematical declaration or existing central axiom report. It should
make every production Kk module reachable in the default transitive closure,
leaving only the 142 scoped standalone *AxiomAudit modules* outside it.

The full integrated build MUST pass at the PR head before merge.
If it fails, inspect the exact failing declaration, repair in English
first if any assumption has changed, and only then amend the Lean proof.

**Scope warning:** Successful central compilation proves typechecking and
dependency integrity of modules, not that each module has sufficient
hypotheses for the global big Ramsey theorem. The 27 manuscript PENDING
claims, especially a coherent resolved H+ copy, common labelled inverse
source orbit and all-history unavoidability, are unaffected. Do not
upgrade any black manuscript theorem or lower-bound marker.
