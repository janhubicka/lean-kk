import Kk.LocalEventTraceBlindness
import SuccessorTree.Envelope
import Mathlib.Tactic

/-!
# Track E: the local I1/I2/I3 blindness survives GENUINE Kpt meet closure

If a genuine Kpt source Z is meet-closed and x ≤ y for a node y∈Z,
then Z∪{x} remains meet-closed. For selected parameter level set
I=∅, both are therefore literally least Kpt meet/parameter closures
of their respective seed sets.

When some old t∈Z already ends at level lev x and x∉Z, the two
genuine different closures have identical full dependent L+
old/upper crossing relations, I1 terminal existence flags,
prioritized structural event tags and ACTUAL monoid IsInterestingAt
truth values at every cut.

This is an adversarial regression for actual closure OPERATORS over
I=∅. It is NOT a construction of two distinct full AlgorithmRuns
with the same resolved KK diary.

English-first hostile audit:
  docs/track_e_priority_cut_comparison_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Adding an actual ancestor x≤y of an existing member y to a
componentwise meet-closed genuine Kpt source preserves exact
componentwise meet closure. The possible meet of x with an old
member b is either x or meet(y,b), hence belongs to the extension.

No *global* total meet-commutativity is assumed: symmetry of the
meet is deduced only for pairs in the same root component. -/
theorem kpt_meetClosed_insert_below
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family))
    (hClosed : SMTree.Envelope.MeetClosed Z)
    (x y : AdmissibleKptNode family)
    (hxy : x ≤ y) (hy : y ∈ Z) :
    SMTree.Envelope.MeetClosed (Set.insert x Z) := by
  have hCross (b : AdmissibleKptNode family)
      (hb : b ∈ Z) (hComp : SMTree.Envelope.SameComponent x b) :
      LevelTree.meet x b ∈ Set.insert x Z := by
    obtain ⟨r,hrx,hrb⟩ := hComp
    have hYComp : SMTree.Envelope.SameComponent y b :=
      ⟨r,hrx.trans hxy,hrb⟩
    have hMeetYIn : LevelTree.meet y b ∈ Z :=
      hClosed hy hb hYComp
    have hMY : LevelTree.meet y b ≤ y :=
      LevelTree.meet_le_left hYComp
    have hMB : LevelTree.meet y b ≤ b :=
      LevelTree.meet_le_right hYComp
    rcases LevelTree.comparable_below hxy hMY with hXLeM | hMLeX
    · have hXLeB : x ≤ b := hXLeM.trans hMB
      have hEq : LevelTree.meet x b = x := by
        apply le_antisymm
        · exact LevelTree.meet_le_left ⟨r,hrx,hrb⟩
        · exact LevelTree.le_meet le_rfl hXLeB
      exact Set.mem_insert_iff.mpr (Or.inl hEq)
    · have hEq : LevelTree.meet x b = LevelTree.meet y b := by
        apply le_antisymm
        · exact LevelTree.le_meet
            ((LevelTree.meet_le_left ⟨r,hrx,hrb⟩).trans hxy)
            (LevelTree.meet_le_right ⟨r,hrx,hrb⟩)
        · exact LevelTree.le_meet hMLeX hMB
      rw [hEq]
      exact Set.mem_insert_of_mem x hMeetYIn
  intro a b ha hb hComp
  rcases Set.mem_insert_iff.mp ha with hax | haZ
  · subst a
    rcases Set.mem_insert_iff.mp hb with hbx | hbZ
    · subst b
      have hCompXX : SMTree.Envelope.SameComponent x x :=
        ⟨x,le_rfl,le_rfl⟩
      have hMeetXX : LevelTree.meet x x = x := by
        apply le_antisymm
        · exact LevelTree.meet_le_left hCompXX
        · exact LevelTree.le_meet le_rfl le_rfl
      exact Set.mem_insert_iff.mpr (Or.inl hMeetXX)
    · exact hCross b hbZ hComp
  · rcases Set.mem_insert_iff.mp hb with hbx | hbZ
    · subst b
      obtain ⟨r,hra,hrx⟩ := hComp
      have hSwapComp : SMTree.Envelope.SameComponent x a :=
        ⟨r,hrx,hra⟩
      have hComm : LevelTree.meet a x = LevelTree.meet x a := by
        apply le_antisymm
        · exact LevelTree.le_meet
            (LevelTree.meet_le_right ⟨r,hra,hrx⟩)
            (LevelTree.meet_le_left ⟨r,hra,hrx⟩)
        · exact LevelTree.le_meet
            (LevelTree.meet_le_right hSwapComp)
            (LevelTree.meet_le_left hSwapComp)
      rw [hComm]
      exact hCross a haZ hSwapComp
    · exact Set.mem_insert_of_mem x (hClosed haZ hbZ hComp)

/-- An actual Kpt source that is meet-closed is its own literal
least meet-and-parameter closure over the EMPTY set of selected
parameter levels. This uses the genuine closure definition and
the fact that parameter closure over ∅ is vacuous. -/
theorem kpt_closure_empty_levels_eq_of_meetClosed
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family))
    (hClosed : SMTree.Envelope.MeetClosed Z) :
    SMTree.Envelope.closure (admissibleKptSTree family)
      (∅ : Set Nat) Z = Z := by
  have hParam :
      SMTree.Envelope.ParameterClosedOver
        (admissibleKptSTree family) Z (∅ : Set Nat) := by
    intro a ha i hi
    exact False.elim (by simpa using hi)
  apply Set.Subset.antisymm
  · exact SMTree.Envelope.closure_minimal
      (admissibleKptSTree family) (∅ : Set Nat) Z Z
      Set.Subset.rfl hClosed hParam
  · exact SMTree.Envelope.subset_closure
      (admissibleKptSTree family) (∅ : Set Nat) Z

/-- Strengthened genuine-closure obstruction: two DIFFERENT literal
least Kpt meet-and-parameter closures for I=∅ can have identical
full old/upper L+ crossing spectra, terminal-I1 existence flags,
priority structural tags and genuine monoid IsInterestingAt verdicts
at EVERY cut.

The closure sets arise from DIFFERENT seed sets Z and insert x Z.
This does not imply they arise from two AlgorithmRuns on the same
seed set, or satisfy the resolved Henson numerical-H+ schedule. -/
theorem distinct_meetClosed_Kpt_closures_same_all_local_verdicts
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family))
    (hClosed : SMTree.Envelope.MeetClosed Z)
    (x y t : AdmissibleKptNode family)
    (hxy : x ≤ y) (hy : y ∈ Z) (ht : t ∈ Z)
    (hSameLevel : LevelTree.lev t = LevelTree.lev x)
    (hNot : x ∉ Z) :
    let ZA : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (∅ : Set Nat) (Set.insert x Z)
    let ZB : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (∅ : Set Nat) Z
    ZA ≠ ZB ∧
      (∀ cut, KptI1AtCut family ZA cut ↔
        KptI1AtCut family ZB cut) ∧
      (∀ cut, FullPhysicalClosureCrossing family ZA cut =
        FullPhysicalClosureCrossing family ZB cut) ∧
      (∀ cut, kptPriorityStructuralTag family ZA cut =
        kptPriorityStructuralTag family ZB cut) ∧
      (∀ cut,
        SMTree.Envelope.IsInterestingAt
          (normalizedKptSMTree family) ZA cut ↔
        SMTree.Envelope.IsInterestingAt
          (normalizedKptSMTree family) ZB cut) := by
  have hClosedIns : SMTree.Envelope.MeetClosed (Set.insert x Z) :=
    kpt_meetClosed_insert_below family Z hClosed x y hxy hy
  have hEqA :=
    kpt_closure_empty_levels_eq_of_meetClosed
      family (Set.insert x Z) hClosedIns
  have hEqB :=
    kpt_closure_empty_levels_eq_of_meetClosed family Z hClosed
  dsimp
  rw [hEqA,hEqB]
  exact distinct_Kpt_node_sets_same_all_I1_I2_I3_local_verdicts
    family Z x y t hxy hy ht hSameLevel hNot

end Kk
