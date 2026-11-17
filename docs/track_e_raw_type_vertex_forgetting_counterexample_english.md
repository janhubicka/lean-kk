# Track E E59 — a finite G+ socle code forgets the distinguished Kpt type vertex

**16 November 2026. Adversarial English counterexample committed BEFORE Lean.**

## Exact data-level issue

The checked successor-tree definition \`FiniteGPlusVertex\`
contains the finite \`FinitePartialCode\` of a genuine finite
L+ partial structure: its size, directed binary, unary,
diagonal and E atoms on the **ordinary finite socle**.
Thus it DOES retain all auxiliary E on the ordinary
coordinates. It does NOT store an extra distinguished
Kpt **type vertex** and its type-relative atoms.

Likewise \`RawPartialTypeNode.ordinaryCode\` explicitly
reads only \`some i\` / \`some j\` entries of the
complete \`PartialTypeWithE\` record. The distinguished
type vertex is \`none\`. Type-to-socle and singleton
type-vertex L facts are not recovered by that forgetful
projection.

In the language with one unary relation and no binary or
diagonal symbols (db=0, du=1, dd=0), take two literal
raw partial types over a ONE-VERTEX ordinary socle.
Both have the same E relation and all ordinary-socle
unary values false. Distinguish them only by the unary
truth value of their **type vertex** \`none\`: false
for T0 and true for T1.

Then

\[
T_0\neq T_1,\qquad
 \operatorname{ordinaryCode}(\langle 1,T_0\rangle)
 =\operatorname{ordinaryCode}(\langle 1,T_1\rangle).
\]

The equality of codes is literal: every ordinary entry,
including every E bit, agrees. The inequality is witnessed
by the unary predicate on \`none\`. This is an elementary
non-injectivity counterexample of the actual **raw
type-to-socle code projection**.

### Critical boundary

This example lives at the type-record level and by
itself does NOT assert both raw types are admissible
in a fixed forbidden family, that both occur as actual
Kpt source nodes in a resolved Henson construction,
or that two actual same-diary occurrences violate the
common labelled orbit theorem.

It only refutes the invalid logical inference:

> equality of selected G+ finite socle codes implies
> equality of every assigned distinguished Kpt source type.

A true global Track-E comparison must additionally
reconstruct the SOURCE type-vertex incidences (including
all dependent old/upper L+ data), perhaps via actual
representing pairs or physical source-closure recipes.
E57 correctly requires separate selected G+ record
hypotheses rather than confusing selected codes with
dependent Kpt node records.

## Hostile checks (12)

1. The ordinary code includes E on its finite socle.
   Do not claim that E is entirely forgotten.
2. Ordinary-code projection intentionally drops the
   distinguished type vertex, not ordinary vertices.
3. \`Option (Fin 1)\` has both \`some 0\` and \`none\`;
   compare only \`none\` to exhibit the difference.
4. Both raw types have the SAME ordinary L atoms.
5. Both raw types have the SAME E table.
6. The unary language has an actual \`Fin 1\` singleton
   predicate so the difference is not an empty symbol.
7. The projection keeps size 1, not an invalid empty
   G+ carrier.
8. Do not elevate arbitrary raw-type examples to
   an unconditional admissible-Kpt counterexample.
9. Do not infer a global failure of the Ramsey
   characterization from this local data loss.
10. No selected inverse-image equality or monoid
    source orbit is concluded by the counterexample.
11. A canonical neutral-cap representative of a G+
    socle code does not necessarily equal the actual
    original Kpt source node of a selected occurrence.
12. Keep the example as a short adversarial regression
    (in a proof-audit note or appendix), not a new
    theorem in the circulation's positive proof chain.

## Verification

Formalize the **raw** data statement separately with
\`RawPartialTypeNode\`, \`PartialTypeWithE\` and
\`ordinaryCode\`. Compile and strict-audit only the
concrete non-injectivity theorem. Keep this independent
from the E57/E58 positive conditional modules.
Do not promote the global orbit proof or edit frozen
black manuscript statements.
