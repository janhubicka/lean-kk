# Finite selected fronts and an actual retained-envelope interface

## Scope and starting point

The actual event chronology and retained-role geometry are already proved.
The next step constructs the finite selected lists to which the ordinary
envelope conditions refer. It also constructs a finite retained-level plan
and complete original pool inside an actual finite prefix. The two graph
conditions (positive-source coverage and nonselected old-column zero) will
be derived. Selected canonical-age equality, no-split, and the seed/pool
application data remain explicit.

The actual fair graph is K4-specific. Exact graph consequences use an empty
initial old pool; the actual initial-stage constructor provides it. Pure
finite enumeration and role/level arithmetic need no such graph premise.

## 1. Generic finite selected front

Fix a finite enumerated partial structure A, a role function, a pool
V of names in Fin A.size, and a cut c. Form the finite set of names v
satisfying all three predicates:

1. v belongs to V;
2. c+1 is at most A.freeLevel(v);
3. role(v) is coded true.

Enumerate this finite set increasingly by the standard Finset order
embedding from Fin(cardinality). Its natural-number values are the actual
selected list. Membership in its range is equivalent to the conjunction
above. The enumeration is strictly increasing and injective, has values
below A.size, and every value is strictly above c because freeLevel(v) is
at most v. Empty fronts give Fin 0 without any nonemptiness requirement.
Increasing the cut can only delete members; cardinality is at most the
ambient prefix size. These are finite-list facts, not a uniform diary
record bound.

## 2. Actual graph consequences

Use A=(oneGapPartial actualEventEdge).finitePrefix N and the actual event
role. Assume each name in V has a retained base role and the cut has an
omitted base role. An eligible v is later than c by freeLevel_le. If its
new ordinary bit is positive, the already proved actual-geometry theorem
forces role(v)=coded true, so the range equivalence puts v in the selected
list. This is precisely the envelope's positive-source premise.

If an eligible v is absent from the selected list, the same range
equivalence shows that its retained role is not coded true. The actual
noncode old-column theorem then makes every ordinary bit from p<c to v
false. This is precisely the envelope's nonselected-old-zero premise.
It covers retained dummy names too. No old-zero conclusion is assumed.

The cut condition is an omitted role, not merely an omitted level. The
finite retained plan below provides that implication at meaningful cuts.
Omitted dummy levels are handled by the separately proved zero-row branch.

## 3. Identify the coding front with prescribed originals

The companion CodingSelection construction sets coding-event flags by a
finite set S of original indices, with arbitrary whole-event auxiliary
flags. Its actual role-coordinate theorem identifies coded true exactly
with the addresses a(n)=oneGapAddress(codePosition(n)) for n in S.

Consequently every selected list entry is the address of a unique member
of S. Conversely, the address of n in S occurs whenever it is in the
finite pool and eligible at the cut. Strictly increasing original
addresses make the correspondence injective, so front cardinality is at
most S.card. This includes every retained coded cap that is eligible: a
cap cannot be dropped from S while claiming it has a zero old column.

This correspondence does not assign a legal projected diary. Auxiliary
retention flags remain arbitrary at this layer.

## 4. Construct the finite retained plan

For a coding cap n whose event flag is true, let p=codePosition(n),
top=oneGapAddress(p), and N=top+1. Among ordinary vertex positions q<=p,
retain exactly those whose containing event has flag true. Call this
finite set B. Define the level set I to contain zero and the complete
preceding-gap/meaningful-coordinate pair of each q in B.

Define V to be all names below N with a retained base role. In particular,
dummy roles belong to V whether or not their levels belong to I. For a
meaningful coordinate below N, membership in I is equivalent to retention
of its role. Thus a meaningful c<top omitted from I has an omitted role,
and the preceding graph argument applies.

The cap lies in B in ordinary coordinates, so top belongs to I. All I
levels are at most top, zero belongs to I, and I is finite. Every retained
meaningful vertex retains its preceding gap. The actual free-level formula
then retains every endpoint. A retained level with positive free level
belongs to V; dummy names cause no exception because their roles are
retained. These are derived properties of I and V.

This is an actual finite truncation, not a claim that all globally retained
events occur before the cap. An application wanting all prescribed
originals in this prefix must choose its cap beyond them. A coding cap may
be inserted into the finite original selection; its selected role must
remain visible in all front and age arguments.

The cap's free level is top-1. Thus c<top alone does not imply cap
eligibility at the immediate preceding dummy coordinate. At an omitted
cut c<top, however, the retained free endpoint excludes c=top-1; hence
c+1<=top-1 and the cap belongs to the selected front. This proves actual
cap-front inclusion at every omitted cut below the cap, including omitted
dummy cuts.

For an arbitrary finite requested original set S, choose the fresh cap
index m=S.sup(id)+1 and augment S to S+=insert m S. Every n in S is below
m, so its strictly increasing original address is below the cap. The cap
is outside S and S+ has cardinality S.card+1. Set the coding keep flags
using S+ and leave auxiliary flags arbitrary. This constructs the required
retained cap and includes all requested original coordinates in the finite
prefix and retained levels. The front cardinality is at most S.card+1,
with the cap counted explicitly. This construction also works for empty S.

## 5. Assemble the envelope

Instantiate the generic front with this actual finite A, role and V at
each cut. The plan gives the anchor, cap, level bound, paired endpoints,
retained-pool compatibility and omitted-real-role implication. The actual
geometry plus the constructed front gives positive-source coverage and
nonselected-old-column zero. Forbidden avoidance follows from the actual
K4-free event graph.

Apply oneGap_planned_envelope_of_real_selected_neutrality. The caller still
supplies a seed set X below top, a source pool U with X in its ambient
prefix pool and U contained in V, retained seed levels, selected no-split,
and full canonical selected-age equality at omitted meaningful cuts.
The result is an actual full planned envelope and the exact level range
I union the tail above top.

This assembled theorem does not take the positive-source, other-source
old-zero, free-endpoint or dummy-cut conclusions as assumptions. It also
does not conceal the remaining selected-age/no-split proof inside a new
predicate. Those conditions will appear explicitly in its Lean statement.

## Remaining boundary

Legal projected-diary retention, the meaningful-cut age/no-split proofs,
uniform record bounds, common labelled inverse sources, direct history
occurrence and final Ramsey bounds remain separate. The finite front
construction discharges two ordinary envelope premises and makes the
finite pool/level data concrete; it does not close the entire diary
application obligation.

## Validation checkpoint

Independent pre-code English review passed for the generic front, actual
geometry consequences, finite-original identification and assembled
conditional envelope. The fresh-cap extension and omitted-cut eligibility
argument also passed mathematical review before their implementation.
Local Lean and complete integration gates remain pending at this checkpoint.

## Final finite-front integration checkpoint — 27 November 2026

This completed checkpoint supersedes pending validation language above.
The normal new-module target passed (3,619 jobs), the default project build
passed (4,129 jobs), all four focused Lean audits and strict parsers passed,
and the central audit accepted all 1,470 exact names, including every one
of the 76 new endpoints. All 1,394 inherited names and axiom sets are
preserved. Only `propext`, `Classical.choice` and `Quot.sound` appear, with
fourteen central names axiom-free. Parser tests, source/import coverage
and diff checks pass. See the [completion report](finite_selected_front_completion_20261127.md)
and [source-hash/axiom evidence](audits/2026-11-27-finite-selected-front-completion.json)
for the precise conditional envelope and remaining application obligations.
