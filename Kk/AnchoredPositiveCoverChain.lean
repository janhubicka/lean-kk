import Kk.AnchoredPositiveNeutralBlock
import Mathlib.Tactic

/-!
# Track B: two true Henson age covers with a genuinely POSITIVE neutral stage

English proof and ten hostile checks were committed FIRST in:
docs/track_b_cover_positive_neutral_cover_composition_english_audit.md

In ONE unchanged original Henson graph E and ONE fixed finite
future-sort dimension d, realize two consecutive canonical age
covers with an intervening genuine POSITIVE support-T0 clique QN.
Its own old canonical age is unchanged because the first
cover's already constructed reserved clique Q0 is a sufficient
positive anchor. No zero-tail reset or independently assumed
zero-critical count is used.

The theorem constructs THREE separate actual positive finite
numerical-H stage witnesses, not a *single coherent* selected
embedding through all three stages. Full dependent Kpt E/L+
B3 source microevents and labelled inverse monoid orbits remain OPEN.
-/

namespace Kk

/-- An actual old Henson physical cover automatically provides a
genuine anchor for any later positive-neutral clique on the SAME
sort support T0, as long as its size rN is at most r0.

This is a completely source-exact finite construction:
  first canonical age cover upper -> middle;
  real age-NEUTRAL POSITIVE support-T0 block QN;
  second canonical age cover middle -> lower.

All source original indices, physical Q0-QN-Q1 nonedges, entire
gap-inclusive columns, raw/canonical age identities and three
separate finite numerical-H uniform positive stages are real.
The first and second top selected witnesses need not coincide
or extend each other; this is NOT the global resolved copy. -/
theorem henson_leftDense_two_physical_covers_with_positive_neutral_block
    (d ell b k0 kN k1 r0 rN r1 : Nat)
    (hell : 2 ≤ ell) (hd : 0 < d)
    (hrNPos : 0 < rN) (hrNLe : rN ≤ r0)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool)
    (T0 T1 : IntegerGraphSupport d ell)
    (lower middle upper : IntegerGraphSupport d ell → Nat)
    (hCover0 : AgeCover (IsIntegerGraphAge d ell) middle upper)
    (hCover1 : AgeCover (IsIntegerGraphAge d ell) lower middle)
    (hEll0 : ell = middle T0 + r0 + 1)
    (hAt0 : upper T0 = middle T0 + 1)
    (hEll1 : ell = lower T1 + r1 + 1)
    (hAt1 : middle T1 = lower T1 + 1)
    (hPrior : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) = upper) :
    ∃ (Q0 : Finset Nat) (F0 : Nat)
      (QN : Finset Nat) (FN : Nat)
      (Q1 : Finset Nat) (F1 : Nat),
      let c1 := supportBlockGappedColumn b Q0 T0.1 c
      let cN := supportBlockGappedColumn F0 QN T0.1 c1
      Q0.card = r0 ∧
      QN.card = rN ∧
      Q1.card = r1 ∧
      (∀ q ∈ Q0, b ≤ q ∧ q < F0) ∧
      (∀ q ∈ QN, F0 ≤ q ∧ q < FN) ∧
      (∀ q ∈ Q1, FN ≤ q ∧ q < F1) ∧
      IsDirectedCliqueOn E Q0 ∧
      IsDirectedCliqueOn E QN ∧
      IsDirectedCliqueOn E Q1 ∧
      (∀ q0 ∈ Q0, ∀ qN ∈ QN,
        E q0 qN = false ∧ E qN q0 = false) ∧
      (∀ qN ∈ QN, ∀ q1 ∈ Q1,
        E qN q1 = false ∧ E q1 qN = false) ∧
      (∀ q0 ∈ Q0, ∀ q1 ∈ Q1,
        E q0 q1 = false ∧ E q1 q0 = false) ∧
      (∀ qN ∈ QN, ∀ t ∈ T0.1, cN qN t = true) ∧
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range F0) c1) =
        middle ∧
      finiteOldColumnRawBound E ell d (Finset.range FN) cN =
        finiteOldColumnRawBound E ell d (Finset.range F0) c1 ∧
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range FN) cN) =
        middle ∧
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range F1)
          (supportBlockGappedColumn FN Q1 T1.1 cN)) = lower ∧
      HasUniformPositiveSupportStage E d ell b F0 k0 hd c Q0 T0 ∧
      HasUniformPositiveSupportStage E d ell F0 FN kN hd c1 QN T0 ∧
      HasUniformPositiveSupportStage E d ell FN F1 k1 hd cN Q1 T1 := by
  classical
  obtain ⟨Q0, F0, h0card, h0within, h0clique, _h0iso,
    h0age, _h0feasible, h0stage⟩ :=
    henson_leftDense_exists_physical_finite_canonical_cover_stage
      d ell b k0 r0 hell hd E hAvoid hDense c T0
      middle upper hCover0 hEll0 hAt0 hPrior
  let c1 : Nat → Fin d → Bool :=
    supportBlockGappedColumn b Q0 T0.1 c
  have hAnchorWithin : Q0 ⊆ Finset.range F0 := by
    intro q hq
    exact Finset.mem_range.mpr (h0within q hq).2
  have hAnchorPositive : ∀ q ∈ Q0, ∀ t ∈ T0.1,
      c1 q t = true := by
    intro q hq t ht
    simp [c1, supportBlockGappedColumn, supportBlockOldColumn,
      hq, ht]
  have hrNEll : rN < ell := by omega
  have hNLe : rN ≤ Q0.card := by omega
  obtain ⟨QN, FN, hNcard, hNwithin, hNclique, hNiso,
    hNraw, hNcanonical, hNstage⟩ :=
    henson_leftDense_exists_anchored_positive_neutral_block
      d ell F0 kN rN hell hd E hAvoid hDense c1 T0 Q0
      hAnchorWithin h0clique hAnchorPositive
      hrNPos hNLe hrNEll
  let cN : Nat → Fin d → Bool :=
    supportBlockGappedColumn F0 QN T0.1 c1
  have hMiddleN :
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range FN) cN) =
          middle :=
    hNcanonical.trans h0age
  obtain ⟨Q1, F1, h1card, h1within, h1clique, h1iso,
    h1age, _h1feasible, h1stage⟩ :=
    henson_leftDense_exists_physical_finite_canonical_cover_stage
      d ell FN k1 r1 hell hd E hAvoid hDense
      cN T1 lower middle hCover1 hEll1 hAt1 hMiddleN
  have hNNonempty : QN.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨qN, hqN⟩ := hNNonempty
  have hF0FN : F0 ≤ FN :=
    (hNwithin qN hqN).1.trans
      (Nat.le_of_lt (hNwithin qN hqN).2)
  refine ⟨Q0,F0,QN,FN,Q1,F1,
    h0card,hNcard,h1card,h0within,hNwithin,h1within,
    h0clique,hNclique,h1clique,?_,?_,?_,?_,
    h0age,hNraw,hMiddleN,h1age,h0stage,hNstage,h1stage⟩
  · intro q0 hq0 q hq
    exact hNiso q0 (h0within q0 hq0).2 q hq
  · intro q hq q1 hq1
    exact h1iso q (hNwithin q hq).2 q1 hq1
  · intro q0 hq0 q1 hq1
    have hqBefore : q0 < FN :=
      lt_of_lt_of_le (h0within q0 hq0).2 hF0FN
    exact h1iso q0 hqBefore q1 hq1
  · intro q hq t ht
    simp [cN, supportBlockGappedColumn, supportBlockOldColumn,
      hq, ht]

#print axioms Kk.henson_leftDense_two_physical_covers_with_positive_neutral_block

end Kk
