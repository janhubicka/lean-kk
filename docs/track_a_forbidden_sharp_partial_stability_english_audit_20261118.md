# Track A: forbidden-clique improvement of physical partial-block stability (English-first audit)

18 November 2026. **Unformalized new strengthening.** Do NOT promote a Lean validation marker before an exact-head kernel proof and standard-only transitive axiom check. All statements here concern actual finite ordinary binary L, not auxiliary Kpt E/B3.

## Input from already checked Track A

For a nonempty support U of GIVEN later top originals j(t)>b, put

P_U = {i<b : E(i,j(t)) for all t in U},
S_U = {i in P_U : E(i,b)},
p_U = clique-cap_E(P_U), c_U = clique-cap_E(S_U).

Assume E is symmetric and loopless. The exact partial-cut RAW event criterion, proved in `Kk/PartialNumericRawSupportEvents.lean`, states that a strict drop between g<=h<=k is equivalent to

(1) E(b,j(t)) for every t in U;
(2) c_U=p_U;
(3) g<=p_U<h;
(4) p_U<ell-1.

Previously established stability starts at g>=ell-1, using only (3),(4).

## New forbidden-clique obstruction

**Lemma.** Let ell>=3. Suppose the original E is K_ell-free in the genuine sense (there is no distinct ell-element E clique); U is nonempty; every j(t)>b; b is U-eligible; and c_U=p_U. Then

    p_U + 2 <= ell-1,
    equivalently p_U <= ell-3.

**Proof.** Choose some t0 in U; admissible IntegerGraphSupport is nonempty. A finite maximum E-clique C in S_U has size c_U=p_U. Every member i of C satisfies i<b<j(t0), so C, b and j(t0) are all distinct. Within C all edges hold. By membership in S_U all edges from i to b hold. By membership in P_U all edges from i to j(t0) hold. By eligibility the edge b--j(t0) holds. Symmetry supplies both edge orientations. Thus C union {b,j(t0)} is an actual E-clique of size p_U+2. K_ell-freeness forces p_U+2<ell, giving the bound. No age shadow is used. QED.

The conclusion is stronger than raw non-saturation p_U<ell-1. It uses actual original K_ell-freeness, not merely a numerical bound on a support function. If the old underlying original graph is not explicitly known to be K_ell-free, this strengthening MUST NOT be used.

## Strengthened finite ordinary-L age theorem

**Theorem (proposed).** Under the exact assumptions of existing `finiteNumericH_partial_actual_raw_stable_after_ell_pred`, additionally suppose ell>=3, E is loopless and genuinely K_ell-free, and

    ell-2 <= g <= h <= k.

Then the *entire* real physical partial raw support functions agree at g and h; hence so do canonical integer ages and feasible normalized integer clique vectors.

**Proof.** Fix U. Old raw monotonicity gives Raw_h(U)<=Raw_g(U). If strict, the actual event criterion gives eligibility, c_U=p_U and g<=p_U. The new lemma gives p_U<=ell-3, while g>=ell-2, contradiction. Therefore equality holds at every nonempty admissible support. Extensionality and deterministic canonicalization give the remaining claims. QED.

For ell=2, genuine K_2-freeness rules out eligibility E(b,j(t)) for any nonempty support U, so there are NO raw events at any partial cut; the stable-from-zero conclusion holds separately. For ell=0,1, support types are empty, hence raw function equality is vacuous (but this is not the ordinary Henson parameter regime).

## Sharpness: a genuine K4-free example

Let ell=4, k>=2, b=1, one later top original j(0)=2, and E the undirected triangle on original vertices {0,1,2}, with all other original vertices isolated. This is K4-free. At support U={0}:

P_U={0}; S_U={0}; p_U=c_U=1; E(b,j(0))=true.

At g=1 the actual one-jump clique capacity is p_U=1 and raw bound is 3-1=2. At h=2 capacity is p_U+1=2, raw bound 3-2=1. Thus the bound g>=ell-2=2 is optimal for *raw* support stability uniformly over K4-free originals. The earlier g>=ell-1=3 theorem is valid but nonsharp in the K4-free subclass.

More generally, ell>=3, take an original complete graph on ell-1 vertices, order its vertices 0,...,ell-2, put b=ell-3 and j=ell-2, and use the singleton support. Then P_U and S_U have size ell-3, c_U=p_U=ell-3, and the raw fall occurs from cut g=ell-3 to h=ell-2. (For ell=3, b=0, j=1, and the event is 0->1.) The original graph is K_ell-free. Consequently ell-2 is the best uniform stable generation.

## Adversarial conditions and limits

1. The precise source hypothesis `genuine K_ell-free` must be an explicit Lean predicate/lemma, **not** inferred from the already proved ordinary raw-age formula.
2. The max-clique C attaining c_U exists because S_U is finite. It must be a clique in E in both directed orientations. The original graph's symmetry and irreflexivity must be available at the proof boundary.
3. The nonempty support is essential to select a later original j(t0). Without it, the argument has no second added vertex.
4. Strict order i<b<j(t0) proves C, b and j(t0) are pairwise distinct. Later top names need not be pairwise distinct for this single-support proof.
5. A clique on p_U+2 vertices is genuine. Even when p_U=0, the two vertices b,j(t0) form an edge.
6. This theorem does not say the *full* Kpt source stops changing at ell-2: auxiliary E, parameter-closed (B3), I1/I2/I3 or source indexing can still detect later levels.
7. It does not compare two different recursive realization branches. Original graph E, b, k, M and given j remain fixed.
8. The phase g=k+1/top is excluded; the top gate is a different relation.
9. This is a theorem about RAW stability. No raw-event-to-canonical-COVER implication is asserted.
10. Do not remove the general ell-1 stability theorem: its hypotheses allow original graphs that are not known to be K_ell-free.
11. Raw-drop sharpness does not automatically imply a canonical integer-age drop in a multi-sort support system; compare the genuine redundancy example in PR #323.
12. For ell=2, the separate no-edge proof should be Lean-checked rather than forcing a Nat `ell-3` subtraction argument.

## Lean implementation target

New independent `Kk/PartialNumericForbiddenSharpStability.lean`, imported only after identifying the existing true original-graph forbidden-clique predicate:

- `original_support_capacity_le_ell_sub_three_of_eligible`: obtain the max original S_U clique; append b and one chosen j(t0) to obtain an actual forbidden clique unless p_U+2<ell.
- `finiteNumericH_partial_actual_raw_stable_after_ell_sub_two_of_henson`: reduce strictness by the merged raw event iff and the preceding capacity obstruction.
- canonical and feasible-vector corollaries obtained by rewriting.
- separate ell=2 no-event theorem if not subsumed by an existing all-ell lemma.
- compile with full Lake, named `#print axioms` with the exact-head strict parser, and retain an independent physical E/L regression.

This note is an English proof and adversarial audit, **not a claim that Lean compiled**. All frozen black manuscript text and existing validation registry marks remain untouched.


## 19 November continuation: simplified Henson raw-event iff

The new theorem `trackA_henson_partial_raw_event_iff_simple` sharpens the
existing exact raw-event criterion. Under genuine avoidance of
`hensonForbiddenFamily ell hell`, for every nonempty support U and
partial cuts g<=h<=k, **strict raw support loss is equivalent to
exactly three source properties and the cut condition**:

- current original b is adjacent to all given future tops in U;
- c_U = p_U (the linked-old maximum clique attains the full old capacity);
- g <= p_U < h.

The separate general raw-event condition p_U < ell-1 follows
automatically: choose one t in U and an actual C subset S_U of size
p_U. Then C union {b,j(t)} is a real clique of size p_U+2, so
p_U+2<ell under K_ell-freeness. Consequently p_U<ell-1 is redundant,
and the event cannot occur when g>=ell-2.

**Scope:** this iff concerns RAW ordinary-L support events, not
canonical covers (some raw events are invisible to canonical age),
and not auxiliary Kpt I1/I2/I3/B3. The counterpart without genuine
K_ell-freeness must retain its p_U<ell-1 clause.

**Lean source and audit:** the theorem has been added to
`Kk/PartialNumericForbiddenSharpStability.lean` with a named
standard-only axiom report. It is unverified until the exact-head
Lake build passes. A preceding CI build of the initial module failed
at two local proof-script steps (a renamed Finset insertion-cardinality
lemma and a missing definitionally equal capacity normalization).
Both are patched in the submitted branch. No full successful exact-head
gate has yet been observed for this continuation; no manuscript green
mark or black-text edit is justified.


## Local generation transitions and uniqueness (further Track A continuation)

Under genuine Henson avoidance, fix the original graph E, b, k, M,
the SAME labelled later originals j and a nonempty support U.
Write p_U=cap_E(P_U), c_U=cap_E(S_U).
For a single step g→g+1 with g+1≤k, the simplified physical raw
event iff reduces to

  Raw_(g+1)(U)<Raw_g(U)
    iff b is U-eligible, c_U=p_U, and p_U=g.

The arithmetic is exact: g≤p_U<g+1 iff p_U=g. In particular any
two different steps g1<g2 cannot both lower the same support, as that
would force p_U=g1 and p_U=g2. No global assumptions about other
supports or canonical integer ages enter this proof.

This is **not** a statement that the entire canonical age experiences
at most one event: distinct supports may have different p_U, and
some raw events are canonically redundant. It also does not limit the
number of genuine auxiliary Kpt I1/I2/I3/B3 levels.

New Lean endpoints:
- `trackA_henson_partial_raw_single_step_iff`
- `trackA_henson_partial_raw_at_most_one_single_step`

Both were added after the English proof and registered for the strict
named standard-only axiom gate. Their exact-head kernel result remains
unchecked: no passing post-repair workflow result was returned.

### Validation blocker

A prior GitHub Actions head #44400174911 FAILED on two local Lean
script issues, while preceding Track A modules compiled: old
`Finset.card_insert_of_not_mem` name and unsimplified but definitionally
equal capacity syntax. These were patched in the PR branch. Subsequent
GitHub queries have not exposed an exact-head Actions run for the
newest commits. Do not mark these endpoints validated until the
current head is actually built and standard-only axioms reported.


## Canonical visibility over genuine Henson ordinary-L ages (continuation)

**Theorem, English-first.** Let ell>=2, let the symmetric loopless
original E avoid the genuine normalized Henson forbidden family, and
fix the SAME current original b, numeric H height k, Boolean carrier
M, and later-top family j. For 0<=g<=h<=k the canonical integer
ordinary-L ages at h and g differ if and only if there is a normalized
integer clique-multiplicity vector w and nonempty admissible support U
such that:

1. **Whole-vector old feasibility:** w respects the old RAW bound
   B_g(V) for EVERY admissible support V (not merely V=U).
2. **Saturation at U:** sum_(t in U) w_t = B_g(U).
3. **Physical raw event:** b is U-eligible; c_U=p_U; g<=p_U<h.

No separate `p_U<ell-1` assumption is needed: the genuine original
K_ell-free graph already forces `p_U+2<ell` by taking a maximum
original clique C in S_U and appending distinct real originals
b and j(t0) for any t0 in U.

**Proof.** Apply the already established universal canonical
visibility criterion
`finiteNumericH_partial_canonical_change_iff_saturating_raw_event`.
The forward direction drops its redundant `p_U<ell-1` clause. In
the reverse direction, the new genuine-Henson raw-event iff gives
a literal strict raw decrease, and the older general raw-event
criterion recovers the positivity clause. Now apply the universal
canonical criterion with the globally feasible saturating witness.
No reliance on a diary classification or on Definition 3.1 occurs.

**Adversarial checks.**

- Requiring only `w(U)=B_g(U)` without ALL-support old feasibility
  is false: a simultaneous stronger support bound may eliminate
  w before the proposed event.
- Mere raw-age loss does NOT force canonical-age loss; the genuine
  seven-original K4-free counterexample from Track A PR #323 applies.
- The conclusion is inequality of full canonical age functions,
  not a claim that the old/new ages are adjacent (a cover) in the
  graph-age poset.
- Different U can activate at different generations even though
  every fixed U has at most one raw event. No uniqueness of a global
  interesting level is concluded.
- A single Henson original graph and identical given later tops
  are fixed throughout; no reindexing of Kpt sources is performed.
- Ordinary-L stability does not imply (B3) or the absence of
  dependent I1/I2/I3 events.
- Nonempty U is indispensable for the real extra vertex j(t0).
- The new theorem uses `finiteNumericHPartialActualRawAt`; the
  older canonical theorem uses
  `finiteNumericHPhysicalPartialOldRaw`. Both definitions unfold
  to the IDENTICAL literal numbered old-prefix bound. This is a
  definitional equality, not a conjectural graphical comparison.
- Genuine Henson forbidden-family avoidance supplies symmetry,
  looplessness, and forbidden K_ell; it is not sufficient to
  prove the global BRD theorem.

**Lean integration:** new endpoint
`trackA_henson_canonical_change_iff_saturating_event` in
`Kk/PartialNumericForbiddenSharpStability.lean`, with a qualified
`#check` / `#print axioms` registration. It remains UNVERIFIED
until an exact-head full Lake build and standard-only axiom gate pass.
The original two proof-engineering failures from the first workflow
are patched but no corrected-head CI run was visible at this audit.
Frozen black manuscript and validation marks remain unchanged.

**Next bridge for Track A:** construct a finite support-event *schedule*
from `U -> p_U`, then overlay the actual Kpt terminal and
old/upper crossing predicates. A bare ordinary-L event schedule
cannot classify full algorithmically interesting levels: any such
claim must state extra parameter-closed source hypotheses explicitly.


## Whole raw profile event criterion (same H block)

Define B_g as the genuine ordinary-L raw support function for a
fixed original graph E, current original b, numeric H height k,
Boolean carrier M and GIVEN later original family j. Under Henson
forbidden-family avoidance, for g<=h<=k:

    B_h != B_g

**iff** there is an actual nonempty support U such that

    b U-eligible, c_U=p_U, and g<=p_U<h.

**English proof.** If B_h and B_g differ, choose U where they
differ. The previously established pointwise antitonicity gives
B_h(U)<B_g(U); the new Henson raw-event iff provides the certificate.
Conversely the certificate produces a strict decrease at the named U,
so the full support functions cannot be equal.

No singleton-support shortcut is possible: the event U may involve
two or more target sorts with genuine common-neighbour clique capacity
different from every singleton capacity. The theorem is NOT an exact
canonical event characterization: that needs the global old-feasible
saturating integer witness in the previous section.

This proves that a raw ordinary-L event schedule within an H block is
entirely encoded by the finite data

    (U, b U-eligible, c_U=p_U, p_U),

with all actual event times restricted to p_U<ell-2 by genuine
forbidden-clique avoidance. Different supports may share p_U, so the
number of event **times** is at most ell-2 for ell>=2.
This is a bound only for ordinary-L raw support profile changes;
full Kpt E/I1/I2/I3/B3 interesting levels can occur outside it.

**Lean:** `trackA_henson_raw_function_change_iff_exists_support`
has been added with a qualified named axiom gate. It reuses actual
finite-numbered physical bounds, not invented diary types or
abstract shadow ages. The source is unverified until an exact-head
kernel build and axiom gate pass. No changes to frozen black TeX or
existing validated marks.
