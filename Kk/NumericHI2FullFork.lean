import Kk.NumericHIndexedUpperRecords
import SuccessorTree.V10.AncestorMeet
import Mathlib.Tactic

/-!
# Track C: exact (I2) obstruction as a fork in the FULL indexed Kpt source

English-first proof and 16 hostile checks:
  docs/track_c_i2_full_fork_english_audit.md

The literal Algorithm 5.4 competing-meet test at cut p permits trivial
meets a=a. Such an (I1) node at level p does NOT give two crossing
upper types. Under NO (I1), however, a competing meet is equivalent
to two actual closure nodes above p with the SAME old complete L+ type
and DISTINCT next complete L+ types. This is not a selected-shadow
criterion: auxiliary E and every negative L atom remain present.

The same fork is equivalent to a pair of ACTUAL, ACTIVE finite Kpt
node indices in the true AlgorithmRun's exhaustive source record.

These statements classify a local I2 obstruction, not global boringness,
unbounded recursive H+ geometry, or common labelled inverse source.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Full dependent L+ fork at cut: two actual Kpt sources cross the
cut with identical complete OLD raw type and different complete
UPPER raw types. Noncanonical seed/meet recipes have no role. -/
def KptFullCutFork
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family)) (cut : Nat) : Prop :=
  ∃ a : AdmissibleKptNode family, a ∈ Z ∧
    ∃ b : AdmissibleKptNode family, b ∈ Z ∧
      cut < LevelTree.lev a ∧ cut < LevelTree.lev b ∧
      kptFullOldAtCut a cut = kptFullOldAtCut b cut ∧
      kptFullUpperAtCut a cut ≠ kptFullUpperAtCut b cut

/-- A full old-equal/upper-distinct fork forces a genuinely shared
component and an exact cut-level meet. NO (I1) assumption is needed
in this direction: both witnesses already cross the cut strictly. -/
theorem kpt_full_cut_fork_forces_I2_meet
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family)) (cut : Nat)
    (hFork : KptFullCutFork family Z cut) :
    ∃ a : AdmissibleKptNode family, a ∈ Z ∧
      ∃ b : AdmissibleKptNode family, b ∈ Z ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut := by
  obtain ⟨a,ha,b,hb,hca,hcb,hOld,hUpper⟩ := hFork
  have hA := kpt_full_old_upper_types_of_crossing a cut hca
  have hB := kpt_full_old_upper_types_of_crossing b cut hcb
  have hOldEq :
      LevelTree.ancestor a cut (Nat.le_of_lt hca) =
        LevelTree.ancestor b cut (Nat.le_of_lt hcb) := by
    apply Subtype.ext
    have hSome :
        some (LevelTree.ancestor a cut (Nat.le_of_lt hca)).val =
          some (LevelTree.ancestor b cut (Nat.le_of_lt hcb)).val := by
      calc
        some (LevelTree.ancestor a cut (Nat.le_of_lt hca)).val =
            kptFullOldAtCut a cut := hA.1.symm
        _ = kptFullOldAtCut b cut := hOld
        _ = some (LevelTree.ancestor b cut (Nat.le_of_lt hcb)).val := hB.1
    exact Option.some.inj hSome
  have hNextNe :
      LevelTree.ancestor a (cut+1) (Nat.succ_le_iff.mpr hca) ≠
        LevelTree.ancestor b (cut+1) (Nat.succ_le_iff.mpr hcb) := by
    intro hNext
    apply hUpper
    calc
      kptFullUpperAtCut a cut =
          some (LevelTree.ancestor a (cut+1)
            (Nat.succ_le_iff.mpr hca)).val := hA.2
      _ = some (LevelTree.ancestor b (cut+1)
            (Nat.succ_le_iff.mpr hcb)).val :=
          congrArg (fun z : AdmissibleKptNode family => some z.val) hNext
      _ = kptFullUpperAtCut b cut := hB.2.symm
  have hComp : SMTree.Envelope.SameComponent a b := by
    refine ⟨LevelTree.ancestor a cut (Nat.le_of_lt hca),
      LevelTree.ancestor_le a cut (Nat.le_of_lt hca), ?_⟩
    rw [hOldEq]
    exact LevelTree.ancestor_le b cut (Nat.le_of_lt hcb)
  have hMeet :=
    SMTree.Envelope.meet_level_eq_of_nextPrefix_ne
      hca hcb hOldEq hNextNe
  exact ⟨a,ha,b,hb,hComp,hMeet⟩

/-- The reverse direction requires excluding actual (I1) nodes
*at the same cut*: otherwise a trivial meet a=a at level cut is
not a fork because that node does not cross the cut.

With this correct qualification, every actual cut-level competing
meet gives two complete old-equal/upper-different Kpt records. -/
theorem kpt_I2_meet_forces_full_cut_fork_of_no_I1
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family)) (cut : Nat)
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ Z ∧ LevelTree.lev z = cut)
    (hMeet : ∃ a : AdmissibleKptNode family, a ∈ Z ∧
      ∃ b : AdmissibleKptNode family, b ∈ Z ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :
    KptFullCutFork family Z cut := by
  obtain ⟨a,ha,b,hb,hComp,hMeetLevel⟩ := hMeet
  have hLeA : cut ≤ LevelTree.lev a := by
    have h := LevelTree.level_le_of_le (LevelTree.meet_le_left hComp)
    omega
  have hLeB : cut ≤ LevelTree.lev b := by
    have h := LevelTree.level_le_of_le (LevelTree.meet_le_right hComp)
    omega
  have hCa : cut < LevelTree.lev a := by
    have hNot : LevelTree.lev a ≠ cut := by
      intro heq
      exact hNoI1 ⟨a,ha,heq⟩
    omega
  have hCb : cut < LevelTree.lev b := by
    have hNot : LevelTree.lev b ≠ cut := by
      intro heq
      exact hNoI1 ⟨b,hb,heq⟩
    omega
  have hMa :
      LevelTree.meet a b =
        LevelTree.ancestor a cut (Nat.le_of_lt hCa) :=
    LevelTree.eq_ancestor_of_le
      (LevelTree.meet_le_left hComp) hMeetLevel (Nat.le_of_lt hCa)
  have hMb :
      LevelTree.meet a b =
        LevelTree.ancestor b cut (Nat.le_of_lt hCb) :=
    LevelTree.eq_ancestor_of_le
      (LevelTree.meet_le_right hComp) hMeetLevel (Nat.le_of_lt hCb)
  have hSameOld :
      LevelTree.ancestor a cut (Nat.le_of_lt hCa) =
        LevelTree.ancestor b cut (Nat.le_of_lt hCb) :=
    hMa.symm.trans hMb
  have hNextNe :
      LevelTree.ancestor a (cut+1) (Nat.succ_le_iff.mpr hCa) ≠
        LevelTree.ancestor b (cut+1) (Nat.succ_le_iff.mpr hCb) := by
    intro hEq
    have hCross :
        LevelTree.ancestor a (cut+1) (Nat.succ_le_iff.mpr hCa) ≤
          LevelTree.meet a b := by
      apply LevelTree.le_meet
      · exact LevelTree.ancestor_le a (cut+1) (Nat.succ_le_iff.mpr hCa)
      · rw [hEq]
        exact LevelTree.ancestor_le b (cut+1) (Nat.succ_le_iff.mpr hCb)
    have hLev := LevelTree.level_le_of_le hCross
    have hAlev :=
      LevelTree.level_ancestor a (cut+1) (Nat.succ_le_iff.mpr hCa)
    omega
  have hA := kpt_full_old_upper_types_of_crossing a cut hCa
  have hB := kpt_full_old_upper_types_of_crossing b cut hCb
  refine ⟨a,ha,b,hb,hCa,hCb,?_,?_⟩
  · calc
      kptFullOldAtCut a cut =
          some (LevelTree.ancestor a cut (Nat.le_of_lt hCa)).val := hA.1
      _ = some (LevelTree.ancestor b cut (Nat.le_of_lt hCb)).val :=
        congrArg (fun z : AdmissibleKptNode family => some z.val) hSameOld
      _ = kptFullOldAtCut b cut := hB.1.symm
  · intro hUpper
    apply hNextNe
    apply Subtype.ext
    have hSome :
        some (LevelTree.ancestor a (cut+1)
          (Nat.succ_le_iff.mpr hCa)).val =
          some (LevelTree.ancestor b (cut+1)
            (Nat.succ_le_iff.mpr hCb)).val := by
      calc
        some (LevelTree.ancestor a (cut+1)
          (Nat.succ_le_iff.mpr hCa)).val =
            kptFullUpperAtCut a cut := hA.2.symm
        _ = kptFullUpperAtCut b cut := hUpper
        _ = some (LevelTree.ancestor b (cut+1)
          (Nat.succ_le_iff.mpr hCb)).val := hB.2
    exact Option.some.inj hSome

/-- The exact alternative at any cut: a competing cut-level meet
produces either a genuine (I1) closure node at that level, OR a
nonfunctional fork in the complete old/upper L+ records. -/
theorem kpt_I2_meet_implies_I1_or_full_fork
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family)) (cut : Nat)
    (hMeet : ∃ a : AdmissibleKptNode family, a ∈ Z ∧
      ∃ b : AdmissibleKptNode family, b ∈ Z ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :
    (∃ z : AdmissibleKptNode family,
        z ∈ Z ∧ LevelTree.lev z = cut) ∨
      KptFullCutFork family Z cut := by
  by_cases hI1 : ∃ z : AdmissibleKptNode family,
      z ∈ Z ∧ LevelTree.lev z = cut
  · exact Or.inl hI1
  · exact Or.inr
      (kpt_I2_meet_forces_full_cut_fork_of_no_I1
        family Z cut hI1 hMeet)

/-- The exact cut-level event classification when (I1) is absent:
a competing (I2) meet exists iff the complete physical Kpt source
has an OLD-equal, UPPER-distinct fork. No original-name choices. -/
theorem kpt_no_I1_I2_iff_complete_full_fork
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family)) (cut : Nat)
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ Z ∧ LevelTree.lev z = cut) :
    (∃ a : AdmissibleKptNode family, a ∈ Z ∧
      ∃ b : AdmissibleKptNode family, b ∈ Z ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) ↔
      KptFullCutFork family Z cut := by
  constructor
  · exact kpt_I2_meet_forces_full_cut_fork_of_no_I1
      family Z cut hNoI1
  · exact kpt_full_cut_fork_forces_I2_meet family Z cut

/-- Turn the genuine raw Kpt fork into a FINITE, active-index
certificate, without choosing any seed/meet decomposition or an
original-name representative. The named nodes are exactly the
Finset values, and the Boolean mask is the true Z membership. -/
theorem kpt_full_fork_iff_finite_active_indices
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family)) (cut : Nat)
    (params : Finset (AdmissibleKptNode family))
    (hCovered : Z ⊆ (params : Set (AdmissibleKptNode family)))
    (present : Fin params.card → Bool)
    (hPresent : ∀ i : Fin params.card,
      present i = true ↔ (params.equivFin.symm i).val ∈ Z) :
    KptFullCutFork family Z cut ↔
      ∃ i j : Fin params.card,
        present i = true ∧ present j = true ∧
        cut < LevelTree.lev (params.equivFin.symm i).val ∧
        cut < LevelTree.lev (params.equivFin.symm j).val ∧
        kptFullOldAtCut (params.equivFin.symm i).val cut =
          kptFullOldAtCut (params.equivFin.symm j).val cut ∧
        kptFullUpperAtCut (params.equivFin.symm i).val cut ≠
          kptFullUpperAtCut (params.equivFin.symm j).val cut := by
  classical
  constructor
  · rintro ⟨a,ha,b,hb,hCa,hCb,hOld,hUpper⟩
    have hpa : a ∈ params := hCovered ha
    have hpb : b ∈ params := hCovered hb
    let i : Fin params.card := params.equivFin ⟨a,hpa⟩
    let j : Fin params.card := params.equivFin ⟨b,hpb⟩
    have hi : (params.equivFin.symm i).val = a := by simp [i]
    have hj : (params.equivFin.symm j).val = b := by simp [j]
    refine ⟨i,j, (hPresent i).2 ?_, (hPresent j).2 ?_,
      ?_, ?_, ?_, ?_⟩
    · simpa only [hi] using ha
    · simpa only [hj] using hb
    · simpa only [hi] using hCa
    · simpa only [hj] using hCb
    · simpa only [hi,hj] using hOld
    · simpa only [hi,hj] using hUpper
  · rintro ⟨i,j,hi,hj,hCa,hCb,hOld,hUpper⟩
    refine ⟨(params.equivFin.symm i).val, (hPresent i).1 hi,
      (params.equivFin.symm j).val, (hPresent j).1 hj,
      hCa,hCb,hOld,hUpper⟩

/-- At the TRUE numerical H+ AlgorithmRun pre-cut closure, when
there is no (I1) source node, the entire competing (I2) test
is EXACTLY the existence of two active finite indices with
the same complete old L+ and different complete upper L+ types.

The single params domain and presentAt function can be constructed
by the earlier kernel-checked exhaustive Track C run-index theorem.
No-(I2) is NOT assumed; this equivalence diagnoses whether it fails. -/
theorem finiteNumericH_run_no_I1_I2_iff_indexed_full_fork
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Set (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hSeeds : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid U)
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (params : Finset (AdmissibleKptNode family))
    (hParams : ∀ z : AdmissibleKptNode family,
      z ∈ params ↔
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I 0) X)
    (presentAt : Nat → Fin params.card → Bool)
    (hPresent : ∀ cut : Nat, ∀ i : Fin params.card,
      presentAt cut i = true ↔
        (params.equivFin.symm i).val ∈
          SMTree.Envelope.closure (admissibleKptSTree family)
            (R.I (cut+1)) X)
    (cut : Nat) (hCut : cut < top)
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X ∧
      LevelTree.lev z = cut) :
    let Z : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1)) X
    (∃ a : AdmissibleKptNode family, a ∈ Z ∧
      ∃ b : AdmissibleKptNode family, b ∈ Z ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) ↔
      ∃ i j : Fin params.card,
        presentAt cut i = true ∧ presentAt cut j = true ∧
        cut < LevelTree.lev (params.equivFin.symm i).val ∧
        cut < LevelTree.lev (params.equivFin.symm j).val ∧
        kptFullOldAtCut (params.equivFin.symm i).val cut =
          kptFullOldAtCut (params.equivFin.symm j).val cut ∧
        kptFullUpperAtCut (params.equivFin.symm i).val cut ≠
          kptFullUpperAtCut (params.equivFin.symm j).val cut := by
  classical
  let Z : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (R.I (cut+1)) X
  have hLevels : R.I (cut+1) ⊆ R.I 0 := by
    intro q hq
    rw [R.I_eq_final_tail_of_run (cut+1) (by omega)] at hq
    exact hq.1
  have hStage : Z ⊆
      SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I 0) X :=
    envelope_closure_mono_levels
      (admissibleKptSTree family)
      (R.I (cut+1)) (R.I 0) X hLevels
  have hCovered :
      Z ⊆ (params : Set (AdmissibleKptNode family)) := by
    intro z hz
    exact (hParams z).2 (hStage hz)
  calc
    (∃ a : AdmissibleKptNode family, a ∈ Z ∧
      ∃ b : AdmissibleKptNode family, b ∈ Z ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) ↔
        KptFullCutFork family Z cut :=
      kpt_no_I1_I2_iff_complete_full_fork family Z cut hNoI1
    _ ↔ (∃ i j : Fin params.card,
        presentAt cut i = true ∧ presentAt cut j = true ∧
        cut < LevelTree.lev (params.equivFin.symm i).val ∧
        cut < LevelTree.lev (params.equivFin.symm j).val ∧
        kptFullOldAtCut (params.equivFin.symm i).val cut =
          kptFullOldAtCut (params.equivFin.symm j).val cut ∧
        kptFullUpperAtCut (params.equivFin.symm i).val cut ≠
          kptFullUpperAtCut (params.equivFin.symm j).val cut) :=
      kpt_full_fork_iff_finite_active_indices
        family Z cut params hCovered (presentAt cut) (hPresent cut)

#print axioms Kk.kpt_full_cut_fork_forces_I2_meet
#print axioms Kk.kpt_I2_meet_forces_full_cut_fork_of_no_I1
#print axioms Kk.kpt_I2_meet_implies_I1_or_full_fork
#print axioms Kk.kpt_no_I1_I2_iff_complete_full_fork
#print axioms Kk.kpt_full_fork_iff_finite_active_indices
#print axioms Kk.finiteNumericH_run_no_I1_I2_iff_indexed_full_fork

end Kk
