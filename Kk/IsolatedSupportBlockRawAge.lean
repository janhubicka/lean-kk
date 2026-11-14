import Kk.FiniteOldColumnAge
import Kk.IsolatedBlockContinuationAge
import Kk.LinkedCliqueCapacityUpdate
import Mathlib.Tactic

/-!
# Track A: exact RAW old age after adding an isolated support-T reserved block

English proof, hostile audit, and a sharp pointwise counterexample
were written FIRST:
  docs/isolated_support_block_raw_age_english_audit.md

The real common-old-neighbour clique capacity after inserting a
reserved block Q joined to precisely the future sorts in T can
change on EVERY nonempty support U⊆T, not only on the distinguished
support U=T. It is the MAXIMUM of the preexisting old common-neighbour
capacity and cap_E(Q), because old P and new Q have zero crossing
ordinary-L bits.

This is the LITERAL raw age update of the fixed original graph,
not a false pointwise equality with the ideal rawCliqueBlockBound
that changes only T. The already kernel-checked all-clique-profile
canonicalization shows why their feasible clique families may
nevertheless coincide.

All names and edges are those of the unchanged E. This finite
arithmetic is not the complete unbounded physical stage, nor
auxiliary Kpt E/B3 or a labelled common inverse-source orbit.
-/

namespace Kk

/-- In the absence of ALL forward L atoms from X to Y, no directed
clique in X∪Y can contain one vertex exclusively from each side.
Consequently the maximum clique capacity is a MAX, not a sum.
This lemma does not need X and Y disjoint or E symmetric. -/
theorem finiteDirectedCliqueCapacity_isolated_union_max
    (E : Nat → Nat → Bool) (X Y : Finset Nat)
    (hZero : ∀ x ∈ X, ∀ y ∈ Y, E x y = false) :
    finiteDirectedCliqueCapacity E (X ∪ Y) =
      max (finiteDirectedCliqueCapacity E X)
        (finiteDirectedCliqueCapacity E Y) := by
  classical
  apply Nat.le_antisymm
  · obtain ⟨s,hsUnion,hsClique,hsCard⟩ :=
      finiteDirectedCliqueCapacity_attained E (X ∪ Y)
    have hsInOne : s ⊆ X ∨ s ⊆ Y := by
      by_contra hNo
      have hNotX : ¬ s ⊆ X := by
        intro hsX
        exact hNo (Or.inl hsX)
      have hNotY : ¬ s ⊆ Y := by
        intro hsY
        exact hNo (Or.inr hsY)
      have hx : ∃ x ∈ s, x ∉ X := by
        by_contra hh
        apply hNotX
        intro x hxS
        by_contra hxNot
        exact hh ⟨x,hxS,hxNot⟩
      have hy : ∃ y ∈ s, y ∉ Y := by
        by_contra hh
        apply hNotY
        intro y hyS
        by_contra hyNot
        exact hh ⟨y,hyS,hyNot⟩
      obtain ⟨x,hxS,hxNotX⟩ := hx
      obtain ⟨y,hyS,hyNotY⟩ := hy
      have hxY : x ∈ Y := by
        rcases Finset.mem_union.mp (hsUnion hxS) with hxX | hxY
        · exact False.elim (hxNotX hxX)
        · exact hxY
      have hyX : y ∈ X := by
        rcases Finset.mem_union.mp (hsUnion hyS) with hyX | hyY
        · exact hyX
        · exact False.elim (hyNotY hyY)
      have hyx : y ≠ x := by
        intro hEq
        apply hxNotX
        exact hEq ▸ hyX
      have hEdge : E y x = true := hsClique y hyS x hxS hyx
      have hMissing : E y x = false := hZero y hyX x hxY
      rw [hMissing] at hEdge
      cases hEdge
    rcases hsInOne with hsX | hsY
    · calc
        finiteDirectedCliqueCapacity E (X ∪ Y) = s.card := hsCard.symm
        _ ≤ finiteDirectedCliqueCapacity E X :=
          directedClique_card_le_capacity E X s hsX hsClique
        _ ≤ max (finiteDirectedCliqueCapacity E X)
          (finiteDirectedCliqueCapacity E Y) := le_max_left _ _
    · calc
        finiteDirectedCliqueCapacity E (X ∪ Y) = s.card := hsCard.symm
        _ ≤ finiteDirectedCliqueCapacity E Y :=
          directedClique_card_le_capacity E Y s hsY hsClique
        _ ≤ max (finiteDirectedCliqueCapacity E X)
          (finiteDirectedCliqueCapacity E Y) := le_max_right _ _
  · apply max_le
    · exact finiteDirectedCliqueCapacity_mono E X (X ∪ Y)
        Finset.subset_union_left
    · exact finiteDirectedCliqueCapacity_mono E Y (X ∪ Y)
        Finset.subset_union_right

/-- The complete original-to-future sort column after inserting Q:
the reserved originals see precisely the supports T, in both
physical directions when a later future is built. On old P disjoint
from Q this leaves every prescribed c-bit unchanged. -/
def supportBlockOldColumn {d : Nat}
    (Q : Finset Nat) (T : Finset (Fin d))
    (c : Nat → Fin d → Bool)
    (p : Nat) (t : Fin d) : Bool :=
  if p ∈ Q then decide (t ∈ T) else c p t

theorem supportBlockOldColumn_on_reserved
    {d : Nat} (Q : Finset Nat) (T : Finset (Fin d))
    (c : Nat → Fin d → Bool) (p : Nat) (t : Fin d)
    (hp : p ∈ Q) :
    supportBlockOldColumn Q T c p t = decide (t ∈ T) := by
  simp [supportBlockOldColumn, hp]

theorem supportBlockOldColumn_off_reserved
    {d : Nat} (Q : Finset Nat) (T : Finset (Fin d))
    (c : Nat → Fin d → Bool) (p : Nat) (t : Fin d)
    (hp : p ∉ Q) :
    supportBlockOldColumn Q T c p t = c p t := by
  simp [supportBlockOldColumn, hp]

/-- EXACT physical old common-neighbourhood set after a reserved
support-T insertion. The new Q block belongs to the U-neighbourhood
iff the ENTIRE support U is contained in T. This does not assume
Q is a clique and does not discard absent future-sort columns. -/
theorem supportBlockCommonNeighbourPool_eq
    {d ell : Nat} (P Q : Finset Nat)
    (hDisjoint : Disjoint P Q)
    (c : Nat → Fin d → Bool)
    (T U : IntegerGraphSupport d ell) :
    oldSupportCommonNeighbourPool (P ∪ Q)
        (supportBlockOldColumn Q T.1 c) U.1 =
      oldSupportCommonNeighbourPool P c U.1 ∪
        (if U.1 ⊆ T.1 then Q else ∅) := by
  classical
  ext p
  have hMember :
      p ∈ oldSupportCommonNeighbourPool (P ∪ Q)
          (supportBlockOldColumn Q T.1 c) U.1 ↔
        p ∈ oldSupportCommonNeighbourPool P c U.1 ∨
          (p ∈ Q ∧ U.1 ⊆ T.1) := by
    constructor
    · intro hp
      obtain ⟨hpUnion,hAll⟩ := Finset.mem_filter.mp hp
      rcases Finset.mem_union.mp hpUnion with hpP | hpQ
      · left
        have hpNotQ : p ∉ Q := by
          intro hpQ
          exact (Finset.disjoint_left.mp hDisjoint) hpP hpQ
        refine Finset.mem_filter.mpr ⟨hpP,?_⟩
        intro t ht
        have hBit := hAll t ht
        simpa [supportBlockOldColumn, hpNotQ] using hBit
      · right
        refine ⟨hpQ,?_⟩
        intro t ht
        have hBit := hAll t ht
        have hDec : decide (t ∈ T.1) = true := by
          simpa [supportBlockOldColumn, hpQ] using hBit
        simpa only [decide_eq_true_eq] using hDec
    · rintro (hpOld | ⟨hpQ,hSubset⟩)
      · obtain ⟨hpP,hAll⟩ := Finset.mem_filter.mp hpOld
        have hpNotQ : p ∉ Q := by
          intro hpQ
          exact (Finset.disjoint_left.mp hDisjoint) hpP hpQ
        refine Finset.mem_filter.mpr
          ⟨Finset.mem_union.mpr (Or.inl hpP),?_⟩
        intro t ht
        simpa [supportBlockOldColumn, hpNotQ] using hAll t ht
      · refine Finset.mem_filter.mpr
          ⟨Finset.mem_union.mpr (Or.inr hpQ),?_⟩
        intro t ht
        have htT : t ∈ T.1 := hSubset ht
        simp [supportBlockOldColumn, hpQ, htT]
  by_cases hSubset : U.1 ⊆ T.1
  · simpa [hSubset] using hMember
  · simpa [hSubset] using hMember

/-- Literal raw-age update, with the TRUE common-neighbour capacity
at every nonempty U. A support U⊆T (including PROPER subsets)
can acquire the entire new reserved block Q as common neighbours.
Old P and Q are L-isolated, so the capacity is their MAXIMUM. -/
theorem supportBlockRawBound_exact
    (E : Nat → Nat → Bool) (ell d : Nat)
    (P Q : Finset Nat)
    (hDisjoint : Disjoint P Q)
    (hZero : ∀ p ∈ P, ∀ q ∈ Q, E p q = false)
    (c : Nat → Fin d → Bool)
    (T U : IntegerGraphSupport d ell) :
    finiteOldColumnRawBound E ell d (P ∪ Q)
      (supportBlockOldColumn Q T.1 c) U =
    ell - 1 -
      (if U.1 ⊆ T.1 then
        max (finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool P c U.1))
          (finiteDirectedCliqueCapacity E Q)
       else finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool P c U.1)) := by
  classical
  have hPool := supportBlockCommonNeighbourPool_eq
    P Q hDisjoint c T U
  have hOldZero :
      ∀ p ∈ oldSupportCommonNeighbourPool P c U.1,
        ∀ q ∈ Q, E p q = false := by
    intro p hp q hq
    exact hZero p (Finset.mem_filter.mp hp).1 q hq
  unfold finiteOldColumnRawBound
  rw [hPool]
  by_cases hSubset : U.1 ⊆ T.1
  · simp only [if_pos hSubset]
    rw [finiteDirectedCliqueCapacity_isolated_union_max
      E (oldSupportCommonNeighbourPool P c U.1) Q hOldZero]
  · simp only [if_neg hSubset, Finset.union_empty]

/-- Adding an isolated support-T reserved block never INCREASES
a raw old-column age bound at any admissible support.
This holds even for raw zero bounds and without genuine-age positivity. -/
theorem supportBlockRawBound_le_old
    (E : Nat → Nat → Bool) (ell d : Nat)
    (P Q : Finset Nat) (hDisjoint : Disjoint P Q)
    (hZero : ∀ p ∈ P, ∀ q ∈ Q, E p q = false)
    (c : Nat → Fin d → Bool)
    (T U : IntegerGraphSupport d ell) :
    finiteOldColumnRawBound E ell d (P ∪ Q)
      (supportBlockOldColumn Q T.1 c) U ≤
    finiteOldColumnRawBound E ell d P c U := by
  rw [supportBlockRawBound_exact E ell d P Q hDisjoint hZero c T U]
  change ell - 1 -
    (if U.1 ⊆ T.1 then
      max (finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool P c U.1))
        (finiteDirectedCliqueCapacity E Q)
    else finiteDirectedCliqueCapacity E
      (oldSupportCommonNeighbourPool P c U.1)) ≤
    ell - 1 - finiteDirectedCliqueCapacity E
      (oldSupportCommonNeighbourPool P c U.1)
  split_ifs with hSubset
  · have hLe : finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool P c U.1) ≤
      max (finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool P c U.1))
        (finiteDirectedCliqueCapacity E Q) := le_max_left _ _
    omega
  · exact le_refl _

/-- Supports NOT contained in T retain their literal old raw
bound exactly, even before canonicalization. -/
theorem supportBlockRawBound_unchanged_off_support
    (E : Nat → Nat → Bool) (ell d : Nat)
    (P Q : Finset Nat) (hDisjoint : Disjoint P Q)
    (hZero : ∀ p ∈ P, ∀ q ∈ Q, E p q = false)
    (c : Nat → Fin d → Bool)
    (T U : IntegerGraphSupport d ell)
    (hNot : ¬ U.1 ⊆ T.1) :
    finiteOldColumnRawBound E ell d (P ∪ Q)
      (supportBlockOldColumn Q T.1 c) U =
    finiteOldColumnRawBound E ell d P c U := by
  rw [supportBlockRawBound_exact E ell d P Q hDisjoint hZero c T U]
  simp [hNot, finiteOldColumnRawBound]

#print axioms Kk.finiteDirectedCliqueCapacity_isolated_union_max
#print axioms Kk.supportBlockOldColumn_on_reserved
#print axioms Kk.supportBlockOldColumn_off_reserved
#print axioms Kk.supportBlockCommonNeighbourPool_eq
#print axioms Kk.supportBlockRawBound_exact
#print axioms Kk.supportBlockRawBound_le_old
#print axioms Kk.supportBlockRawBound_unchanged_off_support

end Kk
