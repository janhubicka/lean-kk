# Track E E57 — physical event trace of named Kpt parameters

**16 November 2026. English proof and adversarial audit committed
before Lean code.** Extension of merged E56 PR #242 and existing
\`Kk.NumericHIndexedUpperRecords\`.

## Purpose: remove an artificial reconstruction oracle

The generic E56 full-event source theorem has a common function
\`recoverOld\` and a separate common function \`recoverUpper\`
on each event frame and named source node. For a **genuine named Kpt
parameter**, we already have the actual raw dependent-L+ ancestors:

\[
  \operatorname{old}(z,c)=\mathrm{kptFullOldAtCut}(z,c),\qquad
  \operatorname{upper}(z,c)=\mathrm{kptFullUpperAtCut}(z,c).
\]

These return \`Option RawPartialTypeNode\`, retaining all ordinary-L
positive and negative atoms, auxiliary E, unary/diagonal information,
and the same-node parent/child relation. Both are \`none\` when z
does not cross c. Their definitions and the crossing theorems
already exist and have source-specific Lean certification.

However the event-indexed record may name parameters which are **not
yet active** at an event. To avoid silently treating inactive
nodes as present, the actual physical parameter trace must have
the following three conditions for every event e and named p:

1. \`R.presentAt e (.inr p) = true\` iff the actual Kpt node
   \`R.parameters p\` belongs to the **complete physical pre-cut
   parameter-closed source** \`Z_R(e)\`.
2. If the presence bit is true, the record's old type equals
   \`kptFullOldAtCut (R.parameters p) (R.eventFrame e).compressedSourceCut\`;
   otherwise its old type is \`none\`.
3. Likewise the upper type equals \`kptFullUpperAtCut\` on present
   nodes and \`none\` on absent nodes.

Call the conjunction \`KptPhysicalParameterTrace\`. It is an explicit
faithfulness condition for the event record; it does not follow
from merely being a \`FullEventIndexedSourceRecord\` nor from
selected graph-age equality.

## E57.1: raw parameter-field determinacy

Given R,S with the same named parameter type, assume:

- \`R.parameters = S.parameters\` as **actual Kpt source nodes**,
- \`R.eventFrame = S.eventFrame\` (particularly the literal source cut),
- both physical-trace faithfulness predicates hold for
  their own complete physical pre-cut sources \`Z_R(e),Z_S(e)\`,
- for each event e and named p, actual membership of these equal
  parameter nodes in \`Z_R(e)\` and \`Z_S(e)\` is equivalent.

Then all three parameter fields agree at every event:
\[
  R.presentAt(e,\operatorname{inr}p)
  =S.presentAt(e,\operatorname{inr}p),
\]
\[
  R.oldAt(e,\operatorname{inr}p)
  =S.oldAt(e,\operatorname{inr}p),\quad
  R.upperAt(e,\operatorname{inr}p)
  =S.upperAt(e,\operatorname{inr}p).
\]

Proof: The physical activity equivalences and membership equivalence
make both presence bits true under exactly the same circumstances;
two Booleans with equivalent \`= true\` statements are equal.
For old/upper data, split on that shared Boolean. In the false
case both types are \`none\`. In the true case equality of the
physical named Kpt node and the *event cut* makes the two actual
raw-ancestor functions literally equal. This is a real
same-Kpt-node fact, not a separate oracle assigning next types.

## E57.2: complete record equality with physical parameter traces

Use merged E56's **used recipe** theorem to derive
\`R.parameters=S.parameters\` from the actual seed, positive and
meet outcomes *occurring in named parameter recipes*. Use the
existing genuine monoid inverse-image/strict prefix-chain lemma
to derive \`R.selected=S.selected\`.

Keep the real event-frame equality and the physical membership
conditions of E57.1. The three parameter fields now agree by
raw Kpt extraction, so **we no longer need generic shared
\`recoverPresent\`, \`recoverOld\` or \`recoverUpper\` functions
for dependent parameters**. Instead, assume explicit equality
only for the **selected labels'** presence and old/upper fields
(these are G+ vertices, not automatically the same type as named
dependent Kpt parameter nodes). Extensionality of the full
event-indexed record gives \`R=S\`.

The premises still require exact *physical* source membership
comparison across occurrences and equality of the selected
inverse-source sets and full event frames. The theorem does not
deduce these from the macrodiary and does not prove a monoid orbit.

## Adversarial checks (20)

1. Never identify a dependent Kpt parameter with a selected G+ vertex
   without an explicit source/prefix representation.
2. Raw \`Option\` types are \`none\` on inactive parameters even if
   the same node would cross the cut in a larger source.
3. Raw old and upper ancestors use the **same** actual Kpt node,
   not independently chosen old and upper type witnesses.
4. A present node of level at or below c has \`none\` for both raw
   crossing types, as verified by the predecessor theorem.
5. The raw dependent types retain auxiliary E, negative ordinary-L,
   unary and diagonal relation atoms.
6. No assumption that the physical crossing relation is functional;
   I2 forks can have multiple distinct nodes.
7. Cut coordinates are literal *source coordinates*, not gaps in two
   unrelated numerical-H enumeration systems.
8. Equal event kind alone does not identify event source cut or
   assigned successor character; require full event-frame equality.
9. The membership agreement is one per *named parameter*; it does
   not follow from equal selected macro graph-age states.
10. Even equal physical bad-cut sets from E55 do not imply per-node
    membership agreement.
11. The \`KptPhysicalParameterTrace\` faithfulness of the actual
    event record is a premise to discharge from Track C, not a
    theorem for arbitrary \`FullEventIndexedSourceRecord\`.
12. Do not swap the raw-upper record with its **ordinary-L reduct**.
13. The physical old and upper records are noncomputable raw-prefix
    functions; this gives no executable diary degree calculator.
14. The selected label's old/upper types are separately assumed
    equal; their G+ to Kpt original representation remains open.
15. Meet recipes must refer to physically compatible SameComponent
    original pairs in both actual sources.
16. Used-recipe equality suffices algebraically; unused atom names
    need not be equal.
17. A bare root is a true actual **original-only** new Kpt seed,
    not its full ancestor prefix pool.
18. Equality of source record fields does not certify completeness
    of the parameter naming; the existing
    \`CoversParameterClosure\` hypothesis is separate.
19. Equality of full records still does not *construct* genuine
    outgoing monoid maps; the existing conditional orbit bridge
    requires them.
20. No unbounded resolved-H+ recursion, uniform labelled carrier,
    upper BRD or lower BRD statement follows.

## Next geometric applications

- Track C must produce the actual complete Kpt pre-cut closures,
  faithful per-event membership/live masks, and source-cut
  normalization; a finite exact index already exists one run at a
  time, but cross-occurrence comparison is open.
- Track D must include full I1/I2/I3/B3 event frames, all auxiliary E
  microcuts, the true K4 10/22 regression and all active dependent
  parameter assignments.
- Track E must independently derive selected-source inverse-image
  equality, selected G+ old/upper assignments and physically
  coherent outgoing MMaps for two occurrences of the *same* diary.
  The full source orbit and upper bound remain PENDING.

## Lean acceptance

New independent module importing E56 and the physical raw
old/upper Kpt source operations. Compile its new explicit theorem
endpoints and check their **exact transitive axioms** in a dedicated
workflow with the strict parser. The ordinary full repository build
is a separate gate. Do not promote manuscript validation marks
until those checks complete successfully; do not change black text.
