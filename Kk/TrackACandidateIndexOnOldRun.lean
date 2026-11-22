import Kk.NumericHExhaustiveRunIndex
import Mathlib.Tactic

/-!
# Track A/G: a finite exact candidate Kpt index along an OLD run

English proof and adversarial audit committed first:
docs/track_a_candidate_index_on_old_run_english_audit_20261122.md

One OLD AlgorithmRun on X supplies its selected-level sets. For a
possibly different candidate seed Y inside an actual finite H+ ambient
prefix pool, the complete closures closure(R.I(c+1),Y) are uniformly
enumerated by one finite index of closure(R.I(0),Y). No Y-run exists
or is postulated by this theorem. Source E remains fully dependent.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A true finite numerical-H+ ambient candidate seed Y admits one
finite EXACT full Kpt parameter index at ALL pre-cut closures of an
OLD run R on X. In particular no run on Y or equality of source
sets is required to obtain a single uniform index and live masks.
The index is of the COMPLETE meet/parameter closure, not just Y. -/
theorem finiteNumericH_oldRun_candidate_uniform_exhaustive_source_index
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Set (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid U)
    (runHeight : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X runHeight) :
    ∃ params : Finset (AdmissibleKptNode family),
      ∃ presentAt : Nat → Fin params.card → Bool,
      (∀ z : AdmissibleKptNode family,
         z ∈ params ↔
           z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
             (R.I 0) Y) ∧
      Function.Injective
        (fun j : Fin params.card => (params.equivFin.symm j).val) ∧
      (∀ cut : Nat, ∀ j : Fin params.card,
        presentAt cut j = true ↔
          (params.equivFin.symm j).val ∈
            SMTree.Envelope.closure (admissibleKptSTree family)
              (R.I (cut+1)) Y) ∧
      (∀ cut : Nat, cut < runHeight →
        ∀ z : AdmissibleKptNode family,
          z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
            (R.I (cut+1)) Y ↔
          ∃ j : Fin params.card,
            (params.equivFin.symm j).val = z ∧
            presentAt cut j = true) := by
  classical
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  have hSeedBound :
      Y ⊆ SMTree.Envelope.levelLe
        (T := AdmissibleKptNode family) N := by
    intro z hz
    obtain ⟨o,⟨v,_hv,rfl⟩,hBelow⟩ := hY hz
    have hLevel : LevelTree.lev z ≤ A.freeLevel v.val := by
      have h := LevelTree.level_le_of_le hBelow
      exact h
    have hFree : A.freeLevel v.val ≤ v.val :=
      A.freeLevel_le v.val
    have hvN : v.val < N := v.isLt
    change LevelTree.lev z ≤ N
    omega
  let Z : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family) (R.I 0) Y
  have hFinite : Z.Finite :=
    SMTree.Envelope.closure_finite_of_bounded
      (S := admissibleKptSTree family) (R.I 0) Y N hSeedBound
  let params : Finset (AdmissibleKptNode family) := hFinite.toFinset
  have hExact : ∀ z : AdmissibleKptNode family,
      z ∈ params ↔ z ∈ Z := by
    intro z
    simp [params]
  let presentAt : Nat → Fin params.card → Bool :=
    fun cut j => decide ((params.equivFin.symm j).val ∈
      SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1)) Y)
  have hPresent : ∀ cut : Nat, ∀ j : Fin params.card,
      presentAt cut j = true ↔
        (params.equivFin.symm j).val ∈
          SMTree.Envelope.closure (admissibleKptSTree family)
            (R.I (cut+1)) Y := by
    intro cut j
    simp [presentAt]
  refine ⟨params,presentAt,?_,?_,hPresent,?_⟩
  · exact hExact
  · intro i j hEq
    have hPairs :
        params.equivFin.symm i = params.equivFin.symm j :=
      Subtype.ext hEq
    exact params.equivFin.symm.injective hPairs
  · intro cut hCut z
    let Zcut : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1)) Y
    have hLevels : R.I (cut+1) ⊆ R.I 0 := by
      intro m hm
      rw [R.I_eq_final_tail_of_run (cut+1) (by omega)] at hm
      exact hm.1
    have hSub : Zcut ⊆ Z :=
      envelope_closure_mono_levels
        (admissibleKptSTree family)
        (R.I (cut+1)) (R.I 0) Y hLevels
    constructor
    · intro hz
      have hzFinal : z ∈ Z := hSub hz
      have hzParams : z ∈ params := (hExact z).2 hzFinal
      let j : Fin params.card := params.equivFin ⟨z,hzParams⟩
      have hName : (params.equivFin.symm j).val = z := by
        simp [j]
      refine ⟨j,hName,?_⟩
      exact (hPresent cut j).2 (by simpa only [hName] using hz)
    · rintro ⟨j,hName,hLive⟩
      have hz : (params.equivFin.symm j).val ∈ Zcut :=
        (hPresent cut j).1 hLive
      rw [hName] at hz
      exact hz

#print axioms Kk.finiteNumericH_oldRun_candidate_uniform_exhaustive_source_index

end Kk
