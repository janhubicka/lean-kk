import Kk.AnchoredPositiveCoverChain
import Kk.PreservedTypedNeutralGap
import Mathlib.Tactic

/-!
# Track B: a real first canonical cover saturates its original common-neighbour support

English proof and twelve hostile scope checks were written BEFORE Lean:
docs/track_b_cover_anchor_saturation_criticality_english_audit.md

The pre-stage ENTIRE canonical old age upper plus the exact age-cover
side equations force the old true T-common original clique capacity
to be strictly smaller than r. Adding a genuine physically isolated
clique Q of size r with complete T-positive future columns therefore
makes the entire literal post-stage T-common capacity EXACTLY r.

A later original v adjacent in BOTH E directions to every q in Q,
with a complete T-positive continuation column and the same literal
old original typed prefix, is necessarily a critical ORIGINAL event
on T: Q supplies a maximum mutually linked clique. Under actual
K_ell-free safety of the enlarged original pool the RAW age strictly
drops. It is NOT proved that this produces a canonical cover, and
one cannot identify v with an arbitrary selected top witness merely
from the existence of separate finite Henson stages.
-/

namespace Kk

/-- Source-exact distinguished T-common-neighbour clique capacity
AFTER a real isolated canonical age-cover block. The exact value
r is DERIVED from the PRE-STAGE full canonical age and the two
age-cover side equations, not assumed. -/
theorem real_cover_anchor_common_capacity_exact
    (E : Nat → Nat → Bool) (ell d b F r : Nat)
    (c : Nat → Fin d → Bool)
    (T : IntegerGraphSupport d ell)
    (Q : Finset Nat)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hBF : b ≤ F)
    (hWithin : ∀ q ∈ Q, b ≤ q ∧ q < F)
    (hClique : IsDirectedCliqueOn E Q)
    (hCard : Q.card = r)
    (hIso : ∀ p, p < b → ∀ q ∈ Q,
      E p q = false ∧ E q p = false)
    (hEll : ell = lower T + r + 1)
    (hAt : upper T = lower T + 1)
    (hPrior : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) = upper) :
    finiteDirectedCliqueCapacity E
      (oldSupportCommonNeighbourPool (Finset.range F)
        (supportBlockGappedColumn b Q T.1 c) T.1) = r := by
  classical
  have hAgeLe : upper T ≤
      finiteOldColumnRawBound E ell d (Finset.range b) c T := by
    have h := (integerGraphAgeCanonical_le_raw d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c)) T
    rw [hPrior] at h
    exact h
  have hCapOldLt : finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b) c T.1) < r := by
    change upper T ≤ ell - 1 -
        finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool (Finset.range b) c T.1) at hAgeLe
    omega
  have hDisjoint : Disjoint (Finset.range b) Q := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hpB := Finset.mem_range.mp hp
    have hqb := (hWithin p hq).1
    omega
  have hZero : ∀ p ∈ oldSupportCommonNeighbourPool
      (Finset.range b) c T.1, ∀ q ∈ Q, E p q = false := by
    intro p hp q hq
    exact (hIso p (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
      q hq).1
  have hPool :
      oldSupportCommonNeighbourPool (Finset.range F)
        (supportBlockGappedColumn b Q T.1 c) T.1 =
      oldSupportCommonNeighbourPool (Finset.range b) c T.1 ∪ Q := by
    calc
      _ = oldSupportCommonNeighbourPool (Finset.range b ∪ Q)
          (supportBlockOldColumn Q T.1 c) T.1 :=
        supportBlockGappedCommonNeighbourPool_eq
          b F hBF Q hWithin T T c
      _ = oldSupportCommonNeighbourPool (Finset.range b) c T.1 ∪
          (if T.1 ⊆ T.1 then Q else ∅) :=
        supportBlockCommonNeighbourPool_eq
          (Finset.range b) Q hDisjoint c T T
      _ = oldSupportCommonNeighbourPool (Finset.range b) c T.1 ∪ Q := by
        simp
  rw [hPool]
  rw [finiteDirectedCliqueCapacity_isolated_union_max
    E (oldSupportCommonNeighbourPool (Finset.range b) c T.1) Q hZero]
  rw [isolatedReservedClique_capacity_eq_card E Q hClique, hCard]
  exact max_eq_right (Nat.le_of_lt hCapOldLt)

/-- If a later actual original sees the whole maximum post-cover
anchor clique Q in BOTH directions, and its NEW complete typed
column is positive on all of T, then it is a critical ORIGINAL
on T. Raw decrease is strict under genuine enlarged-prefix safety.

This does not assert that the new original is the selected top
witness of an earlier finite Henson stage, nor that the CANONICAL
age drops. Such application data remain separate. -/
theorem real_cover_later_full_anchor_link_is_critical
    (E : Nat → Nat → Bool) (ell d b F r : Nat)
    (c cNext : Nat → Fin d → Bool)
    (T : IntegerGraphSupport d ell)
    (Q : Finset Nat)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hBF : b ≤ F)
    (hWithin : ∀ q ∈ Q, b ≤ q ∧ q < F)
    (hClique : IsDirectedCliqueOn E Q)
    (hCard : Q.card = r)
    (hIso : ∀ p, p < b → ∀ q ∈ Q,
      E p q = false ∧ E q p = false)
    (hEll : ell = lower T + r + 1)
    (hAt : upper T = lower T + 1)
    (hPrior : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) = upper)
    (v : Nat) (hAfter : F ≤ v)
    (hPrefix : ∀ p, p < F → ∀ t,
      cNext p t = supportBlockGappedColumn b Q T.1 c p t)
    (hPos : ∀ t ∈ T.1, cNext v t = true)
    (hLinks : ∀ q ∈ Q, E q v = true ∧ E v q = true) :
    originalCriticalSupport E (Finset.range F) cNext T v ∧
    (finitePoolCliqueCheck E ell
        (insert v (Finset.range F)) = false →
      finiteOldColumnRawBound E ell d
          (insert v (Finset.range F)) cNext T <
        finiteOldColumnRawBound E ell d
          (Finset.range F) cNext T) := by
  classical
  have hCap : finiteDirectedCliqueCapacity E
      (oldSupportCommonNeighbourPool (Finset.range F)
        cNext T.1) = r := by
    rw [oldSupportCommonNeighbourPool_eq_of_column_prefix
      F cNext (supportBlockGappedColumn b Q T.1 c) hPrefix T.1]
    exact real_cover_anchor_common_capacity_exact
      E ell d b F r c T Q lower upper
      hBF hWithin hClique hCard hIso hEll hAt hPrior
  have hQPool : Q ⊆
      oldSupportCommonNeighbourPool (Finset.range F) cNext T.1 := by
    intro q hq
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (hWithin q hq).2, ?_⟩
    intro t ht
    rw [hPrefix q (hWithin q hq).2 t]
    simp [supportBlockGappedColumn, supportBlockOldColumn, hq, ht]
  have hQMut : Q ⊆ mutualLinkedNeighbours E
      (oldSupportCommonNeighbourPool (Finset.range F) cNext T.1) v := by
    intro q hq
    exact Finset.mem_filter.mpr ⟨hQPool hq, hLinks q hq⟩
  have hMutSub : mutualLinkedNeighbours E
      (oldSupportCommonNeighbourPool (Finset.range F) cNext T.1) v ⊆
      oldSupportCommonNeighbourPool (Finset.range F) cNext T.1 := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hCapQ := isolatedReservedClique_capacity_eq_card E Q hClique
  have hCapLow := finiteDirectedCliqueCapacity_mono E
    Q (mutualLinkedNeighbours E
      (oldSupportCommonNeighbourPool (Finset.range F) cNext T.1) v) hQMut
  have hCapHigh := finiteDirectedCliqueCapacity_mono E
    (mutualLinkedNeighbours E
      (oldSupportCommonNeighbourPool (Finset.range F) cNext T.1) v)
    (oldSupportCommonNeighbourPool (Finset.range F) cNext T.1) hMutSub
  have hCrit : originalCriticalSupport E
      (Finset.range F) cNext T v := by
    refine ⟨hPos, ?_⟩
    omega
  refine ⟨hCrit, ?_⟩
  intro hSafe
  have hvFresh : v ∉ Finset.range F := by
    simp only [Finset.mem_range]
    omega
  exact (finiteOldColumnRawBound_insert_strict_drop_iff_critical_of_safe
    E ell d (Finset.range F) cNext T v hvFresh hSafe).2 hCrit

#print axioms Kk.real_cover_anchor_common_capacity_exact
#print axioms Kk.real_cover_later_full_anchor_link_is_critical

end Kk
