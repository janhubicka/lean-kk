import Kk.NumericHFinalPoolCrossing
import Kk.NumericHMultiRootPreservation
import Mathlib.Tactic

/-!
# Track C: ONE exhaustive finite source-node index across ALL run cuts

English proof and fourteen hostile checks committed BEFORE Lean:
  docs/track_c_exhaustive_run_index_english_audit.md

For a true finite numerical H+ AlgorithmRun and an actually
represented original seed pool, the COMPLETE FINAL meet-and-parameter
closure is finite, even when seeds and selected levels are arbitrary
Sets. Enumerate that very closure by a Finset.equivFin, not by
noncanonical normal-form recipes or original names.

The SAME finite parameter index covers each actual pre-cut closure,
with a Boolean live mask computed from literal closure membership.
This does not assert that two different runs use equal indices,
have the same upper L+ assignments, or share an envelope orbit.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Finite NUMERICAL H+ original-prefix seeds have uniformly
bounded Kpt levels. Genuine meet/parameter closure can never
create a level above that original bound. This proves finiteness
of the ACTUAL final run closure, not a selected-shadow substitute.

The free level is at most the original's physical coordinate,
which is strictly below N. No finite-ness assumption on X itself
is introduced. -/
theorem finiteNumericH_actualRun_finalClosure_finite
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Set (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid U)
    (runHeight : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X runHeight) :
    (SMTree.Envelope.closure (admissibleKptSTree family)
      (R.I 0) X).Finite := by
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  have hSeedBound :
      X ⊆ SMTree.Envelope.levelLe
        (T := AdmissibleKptNode family) N := by
    intro z hz
    obtain ⟨o,⟨v,_hv,rfl⟩,hBelow⟩ := hX hz
    have hLevel :
        LevelTree.lev z ≤ A.freeLevel v.val := by
      have h := LevelTree.level_le_of_le hBelow
      exact h
    have hFree : A.freeLevel v.val ≤ v.val :=
      A.freeLevel_le v.val
    have hvN : v.val < N := v.isLt
    change LevelTree.lev z ≤ N
    omega
  exact SMTree.Envelope.closure_finite_of_bounded
    (S := admissibleKptSTree family) (R.I 0) X N hSeedBound

/-- ONE finite named parameter universe serves EVERY pre-cut
stage of an actual AlgorithmRun. The finite named source
representation is injective, covers every node of the final
COMPLETE Kpt closure, and uses a Boolean active mask for each
real pre-cut closure, INCLUDING generated meets/parameters.

The active mask is the *actual* set-membership test, never a
selected L-front approximation. Its index type Fin params.card
does not change as the cut changes.

No-(I2) is NOT assumed here. A full source node can exist while
failing to cross the tested cut; source crossing requires an
additional strict level comparison. -/
theorem finiteNumericH_actualRun_uniform_exhaustive_source_index
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Set (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid U)
    (runHeight : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X runHeight) :
    ∃ params : Finset (AdmissibleKptNode family),
      (∀ z : AdmissibleKptNode family,
         z ∈ params ↔
           z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
             (R.I 0) X) ∧
      Function.Injective
        (fun j : Fin params.card => (params.equivFin.symm j).val) ∧
      (∀ cut : Nat, cut < runHeight →
        ∀ z : AdmissibleKptNode family,
          z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
            (R.I (cut+1)) X ↔
          ∃ j : Fin params.card,
            (params.equivFin.symm j).val = z ∧
            decide ((params.equivFin.symm j).val ∈
              SMTree.Envelope.closure (admissibleKptSTree family)
                (R.I (cut+1)) X) = true) := by
  classical
  let Z : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family) (R.I 0) X
  have hFinite : Z.Finite :=
    finiteNumericH_actualRun_finalClosure_finite
      family K k N hAvoid U X hX runHeight R
  let params : Finset (AdmissibleKptNode family) := hFinite.toFinset
  have hExact : ∀ z : AdmissibleKptNode family,
      z ∈ params ↔ z ∈ Z := by
    intro z
    simp [params]
  refine ⟨params, ?_, ?_, ?_⟩
  · exact hExact
  · intro i j hEq
    have hPairs :
        params.equivFin.symm i = params.equivFin.symm j :=
      Subtype.ext hEq
    exact params.equivFin.symm.injective hPairs
  · intro cut hCut z
    let Zcut : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1)) X
    have hLevels : R.I (cut+1) ⊆ R.I 0 := by
      intro m hm
      rw [R.I_eq_final_tail_of_run (cut+1) (by omega)] at hm
      exact hm.1
    have hSub : Zcut ⊆ Z :=
      envelope_closure_mono_levels
        (admissibleKptSTree family)
        (R.I (cut+1)) (R.I 0) X hLevels
    constructor
    · intro hz
      have hzFinal : z ∈ Z := hSub hz
      have hzParams : z ∈ params := (hExact z).2 hzFinal
      let j : Fin params.card := params.equivFin ⟨z,hzParams⟩
      have hName : (params.equivFin.symm j).val = z := by
        simp [j]
      refine ⟨j,hName,?_⟩
      have hPresent : decide (z ∈ Zcut) = true :=
        decide_eq_true_eq.mpr hz
      simpa only [hName] using hPresent
    · rintro ⟨j,hName,hPresent⟩
      have hz : (params.equivFin.symm j).val ∈ Zcut :=
        decide_eq_true_eq.mp hPresent
      rw [hName] at hz
      exact hz

#print axioms Kk.finiteNumericH_actualRun_finalClosure_finite
#print axioms Kk.finiteNumericH_actualRun_uniform_exhaustive_source_index

end Kk
