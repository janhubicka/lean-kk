# Track B: automatic saturated cover chain and exact unit drops
22 November 2026. English proof and adversarial audit *before* new Lean.

## Theorem (finite ordinary-graph ages)

Let ell>=2, let D be a finite set of future sorts, and let A<=P be genuine
integer-witness graph ages on all nonempty admissible supports (size<=ell-1).
There are finitely many age functions between A and P, because each takes
values in {1,...,ell-1} on a finite support set. Thus there exists a
saturated chain P=A_0 > A_1 > ... > A_m=A whose successive pairs are covers
in the genuine-age poset.

To construct it, when A<P select a maximal genuine H in [A,P), necessarily
covered by P. Iterate from H. The strictly decreasing rank
  rank(F)=sum_{nonempty admissible T} F(T)
forces termination. Equivalently strong-induct on the finite gap
  gap(A,P)=sum_T (P(T)-A(T)),
splitting any non-cover interval at a strict intermediate genuine age.

## Theorem (every changed coordinate in a cover has a unit drop)

Suppose lower ⋖ upper and lower(S)<upper(S). Define the raw table B by
B(S)=upper(S)-1 and B(T)=upper(T) otherwise. The genuine lower age is
below B. Set H=G_B, the *integer-witness* canonicalization. The
greatest-age theorem gives lower<=H<=B<=upper; H(S)<upper(S), so the cover
forces H=lower.

Take a normalized witness w saturating upper(S). Its total on S is
upper(S)>0; hence some j in S has w_j>0. Decrease w_j by one, leaving
all other coordinates unchanged. This new normalized w' respects every
upper bound (all support weights weakly decrease), and its value on S is
exactly upper(S)-1, so it also respects B. The finite canonicalizer
therefore satisfies H(S)>=upper(S)-1. Since H(S)<=B(S)=upper(S)-1,
we conclude upper(S)=lower(S)+1. **The argument works for every changed
S, not just a uniquely minimal changed support.**

In particular set r=ell-1-lower(S). Since upper(S)=lower(S)+1<=ell-1
and lower(S)>=1, we have 0<r<ell and
ell=lower(S)+r+1.

## Physical implementation and current verified contracts

For each cover choose a changed support S and its positive r. The
existing one-cover Henson lemma inserts an actual clique of r original
vertices, isolated from the *entire* old original prefix (both
adjacency directions), with positive columns exactly on S and with
all genuine enumeration gaps assigned zero future columns.

Its exact raw update is
  B_new(U)=min(B_old(U),lower(S)) if U subset S,
           B_old(U) otherwise.
Because lower is monotone, lower(U)<=lower(S) for U subset S.
Therefore lower<=B_new. At S equality holds, as the previous
canonical upper age was strictly larger; the new canonical age lies
between lower and upper and is not upper. Cover minimality makes it
exactly lower. No claim B_old=upper is made.

The existing `PhysicalCanonicalCoverHistory` theorem iterates every
**supplied** sequence of such physical stages. Combining the two
order-theoretic results with that theorem removes the *supplied
saturated chain* hypothesis from the finite ordinary-graph construction.
For the prospective controlled pre-age C constructed by Track B,
C<=P is already verified from the complete original columns, so
no target age needs to be assumed as a free parameter.

This produces a finite physical sequence and exact final canonical
age, not a prescribed countable numerical-H+ diary.

## Hostile audit / precise limitations

* The intermediate functions must be genuine integer-witness ages:
  merely monotone raw bounds do not suffice.
* The clipped bound B need NOT itself be an age; canonicalization is
  indispensable. It must be above the genuine lower age, ensuring
  positivity of the canonicalizer.
* A coordinate may be lowered only where the upper witness is positive.
  That coordinate exists from upper(S)>=1 and witness equality.
* A clique block affects all sub-supports of S, not merely S itself.
  Target monotonicity is needed to protect the lower age.
* There is no strict cover if there are no admissible supports (d=0),
  or if ell=2 (all genuine ages are identically 1).
* A cover stage has r>=1, which gives a real reserved vertex and a
  monotone actual original cutoff.
* Every already committed selected, reserved or parameter original
  must be below the starting protected cutoff; a future top witness
  outside it cannot be silently re-labelled as an old column.
* Finite stage-local numerical-H top embeddings do NOT automatically
  form one coherent selected embedding. Nor does an ordinary cover
  chain classify all intermediate parameter-closed I1/I2/I3/B3 cuts.
* The full Kpt/L+/E records, relative continuation tests,
  cross-occurrence labelled inverse-source orbit and infinite diary
  remain separate. In particular the known K4 auxiliary B3
  counterexample still applies.

## Independent bounded checks (not Lean evidence)

Enumerate every raw table with values 1,...,ell-1 on each admissible
support, compute its normalized-vector canonicalizer, deduplicate
genuine ages and test all covers. Every changed coordinate of every
cover has unit drop in the enumerated domains:

| d | ell | ages | covers | failures |
| -: | -: | -: | -: | -: |
| 2 | 4 | 13 | 18 | 0 |
| 3 | 4 | 103 | 242 | 0 |
| 4 | 3 | 113 | 318 | 0 |
| 3 | 5 | 378 | 1066 | 0 |

Lean verification still needed for automatic cover-chain existence,
the unit-drop witness-decrement argument, extraction of physical
support/block sizes and composition with the existing finite history.

## Explicit physical chronological certificate (stacked continuation)

The composition need not discard its intermediate stages. Define a typed
`PhysicalGeneratedCoverPath(E,d,ell,k)` with a stop constructor (the same
complete column at the same cutoff) and an advance constructor containing:

* one actual genuine age cover `middle ⋖ upper` and a changed support
  `T`, with the now-derived unit drop and positive block-size identity;
* one actual reserved clique `Q` and cutoff `mid`, all vertices of
  `Q` in `[b,mid)`, and complete two-direction anticompleteness to
  **every** original earlier than `b`;
* the exact column `cmid = supportBlockGappedColumn b Q T c`, preserving
  every already committed column, and the exact canonical next age;
* a stage-local `HasUniformPositiveSupportStage` at fixed numeric
  generation parameter `k`, with a recursive tail starting from exactly
  `mid,cmid,middle` in the *same* original graph `E`.

Induction on the automatically produced abstract `AgeCoverChain` inserts
one real block per cover using the previously verified Henson one-cover
constructor. A companion induction on the generated physical path derives
monotone cutoffs, retention of the complete initial columns, and final age
`target`. This is stronger as a *proof certificate* than merely producing
an endpoint of the right age. There is no fixed supplied sequence of
intermediate ages or changed supports.

**Hostile boundaries:** All stage-local finite numerical-H witnesses remain
existential and may use different embeddings. A previously chosen selected
top witness is not protected unless its original address is already in the
old cutoff with its positive future bits, whose neutrality must then be
proved. The certificate concerns the ordinary canonical age at block
cutoffs, not all numeric-H parameter/free cuts *inside* the blocks. The
K4 auxiliary-B3 microcut obstruction still applies. Only a later true
Kpt/I1–I3/B3 source theorem and common labelled inverse-source orbit can
upgrade the finite cover path to a prescribed resolved diary.
