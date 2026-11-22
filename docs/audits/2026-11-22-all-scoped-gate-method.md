# Exact standard-only transitive checks for standalone scoped modules

22 November 2026. The structural import graph audit found 142 Kk source
modules with names ending in AxiomAudit that are intentionally outside
the default root Kk target. The corresponding production modules have
dedicated proof gates, but a fresh current-main gate for all of these
scoped audit files is missing.

The new Python runner discovers every standalone Kk/*AxiomAudit.lean,
builds the entire discovered set with Lake and then runs each Lean
axiom-audit file directly, not relying on a cached imported report.
Each file's #print axioms requests are compared to the actual Lean
output by the existing adversarial standard-only parser; missing,
duplicate, custom, sorryAx and unknownConstant are fatal.

The workflow reports the exact number of source modules and named
transitive-axiom checks when it completes. A failure here is evidence
of incompatible formalization, not licence to drop the audit.

No global theorem is inferred from compilation. In particular, the
common labelled inverse-source orbit, full Kpt/B3 history, coherent
infinite resolved copy and full BRD characterization remain separate.
No frozen black TeX changes.
