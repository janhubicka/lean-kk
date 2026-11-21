import Kk.TrackCMaxOriginalZeroCertificate
import Kk.TrackGBoringOnlyNoNoveltyRunTransfer
import Mathlib.Tactic

/-!
# Track C: actual same-height Y-run from max real-zero prefixes plus off-zero quietness

English-first adversarial audit:
 docs/track_c_sameheight_realzero_transport_audit_20261121.md

The complete physical K/L numerical-H+ old/new base extension supplies
the true old AlgorithmRun RX and one finite original support W for the
corrected bare Y=X∪{one real original}. E79 / Track C maximal socle
tests force full candidate no-novelty at old-boring real-zero cuts.
If quietness also holds at all OTHER genuinely old-boring cuts,
the verified Track G theorem builds a genuine SAME-HEIGHT target
AlgorithmRun RY on Y, preserving RX.I and its TOTAL MMap-valued RX.F.

Do NOT confuse RY (height oldTop) with the independently constructed
physically taller root run (height newTop); no global diary result.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A full old/new physical numerical-H+ extension admits a genuine
target run at the OLD scan height with identical TOTAL I and F
provided at most one full OLD Kpt prefix test per eligible original
holds at its maximal real-zero cut, and full physical quietness
holds at all OLD-BORING cuts OUTSIDE the real-zero class.

The geometric premises are not derived from the resolved diary, and
nothing is claimed about the physically taller newTop AlgorithmRun. -/
theorem finiteNumericH_constructed_sameHeight_run_of_max_zero_and_offzero
    (family : List (NormalizedForbidden 1 0 1))
    (K L : AgeTestModel 1 0 1)
    (k b N M j : Nat)
    (hNM : N ≤ M) (hBlock : N ≤ hPosition k b 0)
    (hk : 0 < k) (hj : 0 < j)
    (hTarget : hPosition k j k < M)
    (hNTop : N ≤ hPosition k (j-1) k+1)
    (hBin : ∀ i j : Nat, i < b → j < b →
      ∀ r : Fin 1, K.binary i j r = L.binary i j r)
    (hUn : ∀ i : Nat, i < b → ∀ r : Fin 0,
      K.unary i r = L.unary i r)
    (hDiag : ∀ i : Nat, i < b → ∀ r : Fin 1,
      K.diagonal i r = L.diagonal i r)
    (hAvoidK : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hAvoidL : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (hSymL : ∀ i j : Nat,
      (finiteNumericH L k M).L.binary i j (0 : Fin 1) =
        (finiteNumericH L k M).L.binary j i (0 : Fin 1))
    (U : Set (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hSeeds : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoidK U)
    (oldTop : Nat)
    (hOldPhysical : HasPhysicalExhaustiveKptRun family X oldTop) :
    let Y : Set (AdmissibleKptNode family) :=
      finiteNumericH_bareTopRootSeeds
        family L k M j hAvoidL hTarget X
    ∃ Rold : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family) X oldTop,
      ∃ W : Finset (Fin M),
        Y ⊆ ambientPrefixPool family
          (finiteNumericH L k M) hAvoidL (W : Set (Fin M)) ∧
        ((∀ (v : Fin M),
          ∀ (hNonempty :
            (kpt_actual_original_socle_allowed_cuts
              family L k M hAvoidL W X Y oldTop Rold
              (kptActualPositiveRealZeroCuts
                family L k M W X oldTop Rold) v).Nonempty),
          KptActualOldSocleCoveredAt family X oldTop Rold
            ((finiteNumericH L k M).kptOriginal family hAvoidL v)
            ((kpt_actual_original_socle_allowed_cuts
              family L k M hAvoidL W X Y oldTop Rold
              (kptActualPositiveRealZeroCuts
                family L k M W X oldTop Rold) v).max' hNonempty)) →
        (∀ cut : Nat, cut < oldTop →
          ¬ SMTree.Envelope.IsInterestingAt
            (normalizedKptSMTree family)
            (SMTree.Envelope.closure (admissibleKptSTree family)
              (Rold.I (cut+1)) X) cut →
          cut ∉ kptActualPositiveRealZeroCuts
            family L k M W X oldTop Rold →
          NewRootNoNoveltyAtCut family
            (SMTree.Envelope.closure (admissibleKptSTree family)
              (Rold.I (cut+1)) X)
            (SMTree.Envelope.closure (admissibleKptSTree family)
              (Rold.I (cut+1)) Y) cut) →
        ∃ RY : SMTree.Envelope.AlgorithmRun
            (normalizedKptSMTree family) Y oldTop,
          RY.I = Rold.I ∧ RY.F = Rold.F) := by
  classical
  let Y : Set (AdmissibleKptNode family) :=
    finiteNumericH_bareTopRootSeeds
      family L k M j hAvoidL hTarget X
  obtain ⟨Rold, W, hCover, hMaxQuiet⟩ :=
    finiteNumericH_constructed_bare_root_real_zero_of_max_socle
      family K L k b N M j hNM hBlock hk hj hTarget hNTop
      hBin hUn hDiag hAvoidK hAvoidL hSymL U X hSeeds
      oldTop hOldPhysical
  refine ⟨Rold, W, hCover, ?_⟩
  intro hMax hOffZero
  have hXY : X ⊆ Y := by
    intro z hz
    change z ∈ X ∪
      ((fun v : Fin M =>
        (finiteNumericH L k M).kptOriginal family hAvoidL v) ''
        ({(⟨hPosition k j k, hTarget⟩ : Fin M)} : Set (Fin M)))
    exact Or.inl hz
  apply kpt_transport_actualRun_of_boring_only_noNovelty
    family X Y hXY oldTop Rold
  intro cut hCut hOldBoring
  have hOldUnselected : cut ∉ Rold.I cut := by
    intro hSel
    obtain ⟨_D, _hSkip, _hCross, hIEq, _hFEq⟩ :=
      Rold.noninteresting_step cut hCut hOldBoring
    have hInNext : cut ∈ Rold.I (cut+1) := by
      rw [hIEq] at hSel
      exact hSel
    have hTooHigh : cut+1 ≤ cut :=
      (Rold.I_mem_bounds (cut+1) (by omega) cut hInNext).1
    omega
  by_cases hZero :
      cut ∈ kptActualPositiveRealZeroCuts
        family L k M W X oldTop Rold
  · obtain ⟨idx, g, hEq, hPositive, hStageZero⟩ := hZero
    subst cut
    exact hMaxQuiet hMax idx g hPositive hCut
      hOldUnselected hStageZero
  · exact hOffZero cut hCut hOldBoring hZero

end Kk

#check @Kk.finiteNumericH_constructed_sameHeight_run_of_max_zero_and_offzero
#print axioms Kk.finiteNumericH_constructed_sameHeight_run_of_max_zero_and_offzero
