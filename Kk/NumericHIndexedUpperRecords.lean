import Kk.NumericHExhaustiveRunIndex
import Kk.NumericHFinalPoolCrossing
import Mathlib.Tactic

/-!
# Track C: exhaustive true-run parameter index with complete old/upper L+ records

ENGLISH PROOF AND 15 HOSTILE CHECKS COMMITTED FIRST:
  docs/track_c_indexed_upper_records_english_audit.md

The finite index is of actual Kpt nodes, NOT of arbitrarily chosen
normal-form meet recipes and NOT of marked graph originals.

At every true AlgorithmRun no-(I2) cut the full canonical
closure-selected source/target function is represented by one
active parameter index, whose two assigned partial types are
the complete old and next Kpt raw L+ ancestors of the SAME node.

Auxiliary E and false relation atoms remain inside the RawPartialTypeNode.
No selected-shadow B3 projection or common cross-occurrence orbit is asserted.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Full OLD dependent Kpt raw type of one actual Kpt node
at a cut, available only when that node actually crosses
the cut. This is independent of a noncanonical seed/meet recipe. -/
noncomputable def kptFullOldAtCut
    {db du dd : Nat} {family : List (NormalizedForbidden db du dd)}
    (z : AdmissibleKptNode family) (cut : Nat) :
    Option (RawPartialTypeNode db du dd) :=
  if h : cut < LevelTree.lev z then
    some (LevelTree.ancestor z cut (Nat.le_of_lt h)).val
  else none

/-- Full assigned UPPER dependent Kpt raw type at cut+1.
The old and upper records are extracted from the SAME actual z. -/
noncomputable def kptFullUpperAtCut
    {db du dd : Nat} {family : List (NormalizedForbidden db du dd)}
    (z : AdmissibleKptNode family) (cut : Nat) :
    Option (RawPartialTypeNode db du dd) :=
  if h : cut < LevelTree.lev z then
    some (LevelTree.ancestor z (cut+1) (Nat.succ_le_iff.mpr h)).val
  else none

/-- Every genuine crossing of an actual Kpt node has exactly
its two complete consecutive L+ raw types. -/
theorem kpt_full_old_upper_types_of_crossing
    {db du dd : Nat} {family : List (NormalizedForbidden db du dd)}
    (z : AdmissibleKptNode family) (cut : Nat)
    (hCross : cut < LevelTree.lev z) :
    kptFullOldAtCut z cut =
      some (LevelTree.ancestor z cut (Nat.le_of_lt hCross)).val ∧
    kptFullUpperAtCut z cut =
      some (LevelTree.ancestor z (cut+1)
        (Nat.succ_le_iff.mpr hCross)).val := by
  constructor
  · simp [kptFullOldAtCut, hCross]
  · simp [kptFullUpperAtCut, hCross]

/-- An actual Kpt node not crossing the cut has NO assigned
full next-type record at that event, even if it is present
in the final closure. This distinguishes active and crossing. -/
theorem kpt_full_old_upper_none_of_no_crossing
    {db du dd : Nat} {family : List (NormalizedForbidden db du dd)}
    (z : AdmissibleKptNode family) (cut : Nat)
    (hNotCross : ¬ cut < LevelTree.lev z) :
    kptFullOldAtCut z cut = none ∧
    kptFullUpperAtCut z cut = none := by
  constructor
  · simp [kptFullOldAtCut, hNotCross]
  · simp [kptFullUpperAtCut, hNotCross]

/-- At a genuine numerical-H+ AlgorithmRun cut with no competing
I2 meet, every prescribed full F source input is indexed by
one ACTUAL active closure node. Its old and assigned upper
types are BOTH literal complete raw L+ ancestors of that
SAME node and thus include auxiliary E, unary/diagonal and
absent binary relations.

The finite parameter enumeration and Boolean live mask are
supplied with their exact coverage properties, which the
previous exhaustive run-index theorem CONSTRUCTS.

No fixed cross-occurrence index or monoid orbit is claimed. -/
theorem finiteNumericH_indexed_cut_full_old_upper_types
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N : Nat)
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family (finiteNumericH K k N)
      (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
      (U : Set (Fin N)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (params : Finset (AdmissibleKptNode family))
    (hParams : ∀ z : AdmissibleKptNode family,
      z ∈ params ↔
      z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I 0) X)
    (presentAt : Nat → Fin params.card → Bool)
    (hPresent : ∀ c : Nat, ∀ j : Fin params.card,
      presentAt c j = true ↔
        (params.equivFin.symm j).val ∈
          SMTree.Envelope.closure (admissibleKptSTree family)
            (R.I (c+1)) X)
    (cut : Nat) (hCut : cut < top)
    (hNoMeet : ¬ ∃ a : AdmissibleKptNode family,
      a ∈ SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1)) X ∧
      ∃ b : AdmissibleKptNode family,
        b ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (R.I (cut+1)) X ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :
    let A : EnumeratedPartialStructure db du dd :=
      finiteNumericH K k N
    let hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L :=
      finiteNumericH_avoids_family family K hCarrier k N hAvoidK
    let V : Finset (Fin N) := hStageOriginals K k N U (R.I 0)
    let original : Fin V.card → Fin A.size := hOriginalName V
    let Z : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1)) X
    let F : PrescribedBoringData cut db du dd :=
      closureSelectedBoringData family A hAvoidA original Z cut
    ∀ T, T ∈ F.source →
      ∃ j : Fin params.card,
        presentAt cut j = true ∧
        kptFullOldAtCut (params.equivFin.symm j).val cut =
          some (⟨cut,T⟩ : RawPartialTypeNode db du dd) ∧
        kptFullUpperAtCut (params.equivFin.symm j).val cut =
          some (⟨cut+1,F.target T⟩ : RawPartialTypeNode db du dd) := by
  classical
  let A : EnumeratedPartialStructure db du dd :=
    finiteNumericH K k N
  let hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L :=
    finiteNumericH_avoids_family family K hCarrier k N hAvoidK
  let V : Finset (Fin N) := hStageOriginals K k N U (R.I 0)
  let original : Fin V.card → Fin A.size := hOriginalName V
  let Z : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (R.I (cut+1)) X
  let F : PrescribedBoringData cut db du dd :=
    closureSelectedBoringData family A hAvoidA original Z cut
  have hGraph : IsCrossingGraphOf family Z cut F :=
    (finiteNumericH_run_final_pool_crossing_and_upper_types
      family K hCarrier hAvoidK k N U X hX top cut
      hCut R hNoMeet).2.1
  change ∀ T : PartialTypeWithE cut db du dd, T ∈ F.source →
    ∃ j : Fin params.card,
      presentAt cut j = true ∧
      kptFullOldAtCut (params.equivFin.symm j).val cut =
        some (⟨cut,T⟩ : RawPartialTypeNode db du dd) ∧
      kptFullUpperAtCut (params.equivFin.symm j).val cut =
        some (⟨cut+1,F.target T⟩ : RawPartialTypeNode db du dd)
  intro T hT
  obtain ⟨z,hz,hzCut,hOld,hUpper⟩ := hGraph T hT
  have hLevels : R.I (cut+1) ⊆ R.I 0 := by
    intro level hLevel
    rw [R.I_eq_final_tail_of_run (cut+1) (by omega)] at hLevel
    exact hLevel.1
  have hFinal :
      z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I 0) X :=
    (envelope_closure_mono_levels
      (admissibleKptSTree family)
      (R.I (cut+1)) (R.I 0) X hLevels) hz
  have hzParams : z ∈ params := (hParams z).2 hFinal
  let j : Fin params.card := params.equivFin ⟨z,hzParams⟩
  have hNode : (params.equivFin.symm j).val = z := by
    simp [j]
  have hLive : presentAt cut j = true :=
    (hPresent cut j).2 (by simpa only [hNode] using hz)
  have hRaw := kpt_full_old_upper_types_of_crossing z cut hzCut
  have hOldRecord : kptFullOldAtCut z cut =
      some (⟨cut,T⟩ : RawPartialTypeNode db du dd) :=
    hRaw.1.trans (congrArg some hOld.symm)
  have hUpperRecord : kptFullUpperAtCut z cut =
      some (⟨cut+1,F.target T⟩ : RawPartialTypeNode db du dd) :=
    hRaw.2.trans (congrArg some hUpper.symm)
  refine ⟨j,hLive,?_,?_⟩
  · simpa only [hNode] using hOldRecord
  · simpa only [hNode] using hUpperRecord

#print axioms Kk.kpt_full_old_upper_types_of_crossing
#print axioms Kk.kpt_full_old_upper_none_of_no_crossing
#print axioms Kk.finiteNumericH_indexed_cut_full_old_upper_types

end Kk
