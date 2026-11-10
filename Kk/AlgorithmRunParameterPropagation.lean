import Kk.B3GadgetClosureParameter
import Kk.AlgorithmRunTwoB3Selection
import Mathlib.Tactic

/-!
# Actual run propagation through genuine closure parameters

The English proof and adversarial audit were committed FIRST in
`docs/algorithm_run_parameter_propagation_english_audit.md`.

A genuine ambient original already in the full meet-and-parameter
closure can force its own positive-free-level parameters, even when
it is not an original seed. The physical S3 parameter calculation is
reused from `kpt_closure_contains_positive_parameter_of_seed`; closure
minimality eliminates the auxiliary outer closure.

For an actual AlgorithmRun, the source is required in the pre-cut
closure at c+1. A selected cut c then puts its genuine positive
parameter into every lower pre-cut closure. Finally, actual one-upper
and two-upper B3 failures force BOTH cuts in a two-step application,
without assuming either selection as a premise.

All statements retain the same ambient structure, forbidden family,
and seed set. They do not establish global diary admissibility,
occurrence-independent envelope records, or a common labelled orbit.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

universe u v

/-- Adding selected parameter levels enlarges the existing full
meet-and-parameter closure, with the seed set kept fixed. -/
theorem envelope_closure_mono_levels
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    (S : STree T Label) (I J : Set Nat) (X : Set T)
    (hIJ : I ⊆ J) :
    SMTree.Envelope.closure S I X ⊆
      SMTree.Envelope.closure S J X := by
  exact SMTree.Envelope.closure_minimal
    S I X (SMTree.Envelope.closure S J X)
    (SMTree.Envelope.subset_closure S J X)
    (SMTree.Envelope.closure_meetClosed S J X)
    ((SMTree.Envelope.closure_parameterClosed S J X).mono_levels hIJ)

/-- A genuine ambient original in the FULL closure forces its actual
positive-free-level parameter at any selected crossing level.

The original need not be a seed. Applying the existing physical S3
seed theorem to the closed set introduces an auxiliary outer closure;
minimality immediately puts its result back in the original closure. -/
theorem kpt_closure_contains_positive_parameter_of_original_mem
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (I : Set Nat)
    (X : Set (AdmissibleKptNode family))
    (v : Fin A.size)
    (hOriginal : A.kptOriginal family hAvoid v ∈
      SMTree.Envelope.closure (admissibleKptSTree family) I X)
    (c : Nat) (hcSelected : c ∈ I)
    (hcCut : c < A.freeLevel v.val)
    (hcPositive : 0 < A.freeLevel c) :
    ∃ hcCarrier : c < A.size,
      A.kptOriginal family hAvoid (⟨c, hcCarrier⟩ : Fin A.size) ∈
        SMTree.Envelope.closure (admissibleKptSTree family) I X := by
  obtain ⟨hcCarrier, hParameter⟩ :=
    kpt_closure_contains_positive_parameter_of_seed
      family A hAvoid I
      (SMTree.Envelope.closure (admissibleKptSTree family) I X)
      v hOriginal c hcSelected hcCut hcPositive
  have hCollapse :
      SMTree.Envelope.closure (admissibleKptSTree family) I
          (SMTree.Envelope.closure (admissibleKptSTree family) I X) ⊆
        SMTree.Envelope.closure (admissibleKptSTree family) I X :=
    SMTree.Envelope.closure_minimal
      (admissibleKptSTree family) I
      (SMTree.Envelope.closure (admissibleKptSTree family) I X)
      (SMTree.Envelope.closure (admissibleKptSTree family) I X)
      (by intro a ha; exact ha)
      (SMTree.Envelope.closure_meetClosed (admissibleKptSTree family) I X)
      (SMTree.Envelope.closure_parameterClosed (admissibleKptSTree family) I X)
  exact ⟨hcCarrier, hCollapse hParameter⟩

/-- A selected actual run cut c propagates its positive ambient
parameter into the closure used at every lower cut p<c.

The source original is required in the genuine PRE-CUT closure at c+1.
It may be a previously generated parameter rather than a seed. The
run-tail identity and closure monotonicity supply the lower-stage
source membership; no final-closure or selected-only premise is used. -/
theorem algorithmRun_selected_positive_parameter_in_lower_closure
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (X : Set (AdmissibleKptNode family))
    (runHeight : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X runHeight)
    (v : Fin A.size)
    (c : Nat) (hcScan : c < runHeight)
    (hOriginal : A.kptOriginal family hAvoid v ∈
      SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (c+1)) X)
    (hcCut : c < A.freeLevel v.val)
    (hcPositive : 0 < A.freeLevel c)
    (hSelected : c ∈ R.I c)
    (p : Nat) (hp : p < c) :
    ∃ hcCarrier : c < A.size,
      A.kptOriginal family hAvoid (⟨c, hcCarrier⟩ : Fin A.size) ∈
        SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (p+1)) X := by
  have hcLe : c ≤ runHeight := Nat.le_of_lt hcScan
  have hcNextLe : c+1 ≤ runHeight := Nat.succ_le_iff.mpr hcScan
  have hpNextLe : p+1 ≤ runHeight :=
    (Nat.succ_le_iff.mpr hp).trans hcLe
  have hLevels : R.I (c+1) ⊆ R.I (p+1) := by
    intro q hq
    rw [R.I_eq_final_tail_of_run (c+1) hcNextLe] at hq
    rw [R.I_eq_final_tail_of_run (p+1) hpNextLe]
    exact ⟨hq.1, (by omega : p+1 ≤ c+1).trans hq.2⟩
  have hLowerOriginal : A.kptOriginal family hAvoid v ∈
      SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (p+1)) X :=
    (envelope_closure_mono_levels (admissibleKptSTree family)
      (R.I (c+1)) (R.I (p+1)) X hLevels) hOriginal
  have hFinal : c ∈ R.I 0 := by
    rw [R.I_eq_final_tail_of_run c hcLe] at hSelected
    exact hSelected.1
  have hLowerSelected : c ∈ R.I (p+1) := by
    rw [R.I_eq_final_tail_of_run (p+1) hpNextLe]
    exact ⟨hFinal, Nat.succ_le_iff.mpr hp⟩
  exact kpt_closure_contains_positive_parameter_of_original_mem
    family A hAvoid (R.I (p+1)) X v hLowerOriginal
    c hLowerSelected hcCut hcPositive

/-- Two actual B3 failures force two selected cuts in every supplied
AlgorithmRun. The higher one-upper failure selects c; its genuine
positive parameter enters the lower pre-cut closure; the two-upper
failure for that parameter and the seed then selects m.

Neither selected cut nor the generated parameter's closure membership
is assumed. Positivity of c and its free level follows from the lower
cut's displayed strict bounds. The full actual age tests remain
explicit hypotheses, to be verified for any particular ambient. -/
theorem algorithmRun_selects_two_step_B3_parameter_propagation
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (v : Fin A.size)
    (c : Nat) (hcCut : c < A.freeLevel v.val)
    (hFailedHigher :
      ¬ CommonSocleAgeTest family
        (prescribedOrdinarySocle (A.partialTypeAt (c+1) v.val)) c
        (fun T => T = (A.partialTypeAt (c+1) v.val).lReduct))
    (m : Nat) (hmPositive : 0 < m) (hmc : m < c)
    (hmCut : m < A.freeLevel c)
    (hFailedLower :
      ¬ CommonSocleAgeTest family
        (prescribedOrdinarySocle (A.partialTypeAt (m+1) c)) m
        (fun T =>
          T = (A.partialTypeAt (m+1) c).lReduct ∨
          T = (A.partialTypeAt (m+1) v.val).lReduct))
    (X : Set (AdmissibleKptNode family))
    (hSeed : A.kptOriginal family hAvoid v ∈ X)
    (runHeight : Nat) (hcScan : c < runHeight)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X runHeight) :
    c ∈ R.I c ∧ m ∈ R.I m ∧
      ∃ hcCarrier : c < A.size,
        A.kptOriginal family hAvoid (⟨c, hcCarrier⟩ : Fin A.size) ∈
          SMTree.Envelope.closure
            (admissibleKptSTree family) (R.I (m+1)) X := by
  have hcPositive : 0 < c := hmPositive.trans hmc
  have hcFreePositive : 0 < A.freeLevel c := hmPositive.trans hmCut
  have hSelectedHigher : c ∈ R.I c :=
    algorithmRun_selects_actual_failed_single_upper_B3
      family A hAvoid v c hcPositive hcCut hFailedHigher
      X hSeed runHeight hcScan R
  have hSource : A.kptOriginal family hAvoid v ∈
      SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (c+1)) X :=
    (SMTree.Envelope.subset_closure
      (admissibleKptSTree family) (R.I (c+1)) X) hSeed
  obtain ⟨hcCarrier, hParameter⟩ :=
    algorithmRun_selected_positive_parameter_in_lower_closure
      family A hAvoid X runHeight R v c hcScan hSource
      hcCut hcFreePositive hSelectedHigher m hmc
  have hLowerSeed : A.kptOriginal family hAvoid v ∈
      SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (m+1)) X :=
    (SMTree.Envelope.subset_closure
      (admissibleKptSTree family) (R.I (m+1)) X) hSeed
  have hSelectedLower : m ∈ R.I m :=
    algorithmRun_selects_actual_failed_two_upper_B3
      family A hAvoid (⟨c, hcCarrier⟩ : Fin A.size) v
      m hmPositive hmCut (hmc.trans hcCut) hFailedLower
      X runHeight (hmc.trans hcScan) R hParameter hLowerSeed
  exact ⟨hSelectedHigher, hSelectedLower, hcCarrier, hParameter⟩

end Kk
