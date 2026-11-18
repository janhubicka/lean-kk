# Track A — partial-block raw and canonical ages stabilize at generation ell−1

18 November 2026. English mathematical proof and adversarial review BEFORE Lean.

## Certified mathematical inputs

- PR #284 (merged; exact-head CI 44040233653): the TRUE physical
  partial old raw support bound strictly decreases between
  generation cuts g<=h<=k **iff** b is U-eligible, linked
  original capacity c_U equals original old capacity p_U,
  the threshold lies g<=p_U<h, and the old raw value is
  NOT saturated: p_U<ell-1. Any strict drop has size one.
- PR #228: the actual physical raw support age is
  pointwise antitone when the old numbered prefix advances.
- PR #273: the raw, canonical and feasible integer clique
  vector ages are calculated from the actual finite numeric H
  binary-L table, and are independent of its total Boolean
  cutoff for a given later-top family j.

## Main theorem

Fix symmetric original Boolean graph E, numerical height k,
current original b, finite total numeric binary table M, a
family of GIVEN later ORIGINAL top names j(t)>b, ell,d,
and partial cuts

    ell-1 <= g <= h <= k.

Define Raw_x(U) as the actual `finiteOldColumnRawBound`
for *every* nonempty admissible U at numbered cut
`hPosition(k,b,x)`, with actual numeric-L crossings to
top original names j(t) in BOTH orientations.

Then we have equality of the ENTIRE raw support functions:

    Raw_g = Raw_h.

Consequently deterministic integer graph-age
canonicalizations and feasible normalized integer
clique-vector sets agree:

    canonical(Raw_g)=canonical(Raw_h),
    feasible(Raw_g)=feasible(Raw_h).

## Proof

Fix any admissible nonempty U. By physical age
antitonicity, Raw_h(U)<=Raw_g(U). If strict, the
verified genuine numerical-H raw-event iff gives
some original clique capacity p_U such that

    g <= p_U  AND  p_U < ell-1.

This contradicts the input ell-1<=g. Hence
Raw_h(U)=Raw_g(U) by antisymmetry of the natural order.
By extensionality the total raw support functions
agree, and canonicalization / feasible vectors
preserve equality by simple rewriting.

NO induction on the original number b, selected
future names, or hypothetical recursive schedule
is required.

## Additional one-step form

For every partial transition cut g→g+1 with
ell-1<=g<k, there is no raw or canonical ordinary-L
age change, regardless of which nonempty support
is considered. In particular for height k=ell
the cuts g=ell-1 and g=ell yield IDENTICAL raw
and canonical ordinary-L ages.

The latter does not imply full Algorithm (I1)–(I3) /
parameter-closed (B3) level triviality: auxiliary
Kpt E records or source indices may change.

## Adversarial checks

1. This compares the same original E, b, k, M and
   **given** later original names j(t) at both cuts.
   It does not compare different recursive branches.
2. The literal full numbered H prefix contains even
   real and odd fake coordinates; the prior event theorem
   is about the complete physical set, not a selected
   shadow.
3. The rule requires g<=h<=k, so all current-b real
   generations included are NON-TOP. At g=k+1 the
   top-to-top gate changes; the theorem does not apply.
4. If ell=0 or 1, ell-1=0 by Nat truncation, and
   there are no nonempty IntegerGraphSupport d ell.
   The function equality is vacuous and consistent.
5. For ell>=2, a capacity jump may occur at
   p_U+1>=ell but is invisible to raw age because
   the old raw bound is already zero.
6. A raw non-event implies canonical age equality
   because the entire raw functions agree; the proof
   uses ALL nonempty supports, not merely one.
7. The reverse implication for isolated raw supports
   (raw event -> canonical cover) is NOT claimed.
8. The arbitrary finite Boolean carrier parameter M
   is not a statement that all selected top numeric
   positions are in the carrier. Literal physical
   membership needs separate cutoff assumptions.
9. E symmetry and later original conditions are needed
   by the numerical H input theorem, not by arithmetic.
10. No assumption that P_U or S_U is a clique: p_U
    and c_U are maximum directed CLIQUE sizes.
11. The exact cut threshold is ell-1, not ell.
    Every strict raw event uses p_U<ell-1 and
    g<=p_U, so its LAST possible starting generation
    is at most ell-2.
12. Raw age is natural-number truncated subtraction,
    and this saturation is central rather than a
    technical corner case.
13. The stated stability is for **ordinary-L finite
    graph age only**. Full dependent Kpt E, I1/I2/I3
    and (B3) can still distinguish stages.
14. No actual recursively prescribed original
    realization schedule, common labelled inverse
    source or global BRD is obtained.
15. This theorem is a reusable necessary finite
    simplification for the boring-level analysis,
    not the final characterization of boring levels.

## Lean acceptance

Create independent module
`Kk/PartialNumericRawAgeHeightStability.lean` with
raw function, canonical and feasible equalities,
strict standard-only named axiom audit, direct
module/full Lake CI and the independent 197,120-case
physical raw-event regression inherited from PR #284.
Do not alter the manuscript's verified finite
marks until this exact-head gate passes.
