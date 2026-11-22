# Repository-wide Lean coverage audit

This check scans the actual .lean files under Kk/, Kk.lean and scripts/.
It reconstructs the transitive import graph from Kk.lean and reports every
standalone Kk module that the default lake build Kk does NOT reach.

The output also distinguishes 1,017 currently printed axiom reports from
1,065 #check declarations and flags potential explicit proof gaps outside
Lean comments and strings (tokens sorry, admit, axiom, opaque, unsafe).

The report does **not** say all standalone modules are bad: many were
verified in independent exact-head PR CI, and some are axiom-audit harnesses.
Nor does the absence of proof-hole tokens establish that an application
theorem has sufficient hypotheses or implies the paper's main statement.
A complete validation still needs proof-signature/adversarial English audits
and full dependent Kpt diary/orbit realizability.

The gate fails only when a local imported module cannot be resolved. It emits
a self-contained JSON artifact listing the orphan modules and suspicious
tokens for review, rather than silently discarding them or assuming they
were covered by the central build.
