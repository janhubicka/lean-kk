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
