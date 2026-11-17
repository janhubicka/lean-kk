import Kk.K4ActualAlgorithmRunCut10
import SuccessorTree.EnvelopeRun
import Mathlib.Tactic

/-!
# Track G: a genuinely boring finite AlgorithmRun block factors
# through ONE actual monoid map, but the factor need not be trivial.

English-first adversarial proof and K4 regression:
docs/track_g_genuine_boring_block_monoid_factor_english_audit_20261117.md

The hypothesis is the complete actual IsInterestingAt predicate on the
FULL closure_(R.I(i+1))(X), not a selected graph-age shadow.
The aggregate factor D lies in the genuine MMap H monoid by M1.

This is a finite-stage algebraic compression of the actual map:
it does NOT identify D across diary occurrences, bound its labels,
force D=id, or prove a uniform BRD upper bound.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.SMTree

/-- Every cut of a *genuinely* boring block leaves the selected
I-set unchanged, and its successive skip-only M-maps compose
to ONE genuine M-map of the distinguished monoid.

This is one ACTUAL AlgorithmRun; it uses the FULL parameter-closed
IsInterestingAt test at EVERY cut, not just ordinary graph age. -/
theorem actualAlgorithmRun_genuinely_boring_block_factors
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    {S : STree T Label}
    (H : SMTree S) (X : Set T)
    (top low high : Nat)
    (R : SMTree.Envelope.AlgorithmRun H X top)
    (hLowHigh : low ≤ high) (hHigh : high ≤ top)
    (hBoring : ∀ i : Nat, low ≤ i → i < high →
      ¬ SMTree.Envelope.IsInterestingAt H
        (SMTree.Envelope.closure S (R.I (i+1)) X) i) :
    R.I low = R.I high ∧
    ∃ D : MMap H, R.F low = MMap.comp H (R.F high) D := by
  have hStages :
      ∀ i : Nat, low ≤ i → i ≤ high →
        R.I i = R.I high ∧
          ∃ D : MMap H,
            R.F i = MMap.comp H (R.F high) D := by
    have main :
        ∀ d : Nat, ∀ i : Nat, high - i = d → low ≤ i → i ≤ high →
          R.I i = R.I high ∧
            ∃ D : MMap H,
              R.F i = MMap.comp H (R.F high) D := by
      intro d
      induction d using Nat.strong_induction_on with
      | h d ih =>
          intro i hdi hlow hi
          by_cases hieq : i = high
          · subst i
            constructor
            · rfl
            · refine ⟨MMap.id H, ?_⟩
              apply MMap.ext_apply
              intro z
              rfl
          · have hilt : i < high :=
              Nat.lt_of_le_of_ne hi hieq
            have hitop : i < top :=
              lt_of_lt_of_le hilt hHigh
            have hiLow : low ≤ i := hlow
            obtain ⟨Di, _hSkip, _hCross, hIi, hFi⟩ :=
              R.noninteresting_step i hitop (hBoring i hiLow hilt)
            obtain ⟨hNextI, Drest, hNextF⟩ :=
              ih (high - (i+1)) (by omega) (i+1) rfl (by omega) (by omega)
            constructor
            · calc
                R.I i = R.I (i+1) := hIi
                _ = R.I high := hNextI
            · refine ⟨MMap.comp H Drest Di, ?_⟩
              calc
                R.F i = MMap.comp H (R.F (i+1)) Di := hFi
                _ = MMap.comp H
                      (MMap.comp H (R.F high) Drest) Di := by
                        rw [hNextF]
                _ = MMap.comp H
                      (R.F high) (MMap.comp H Drest Di) := by
                        apply MMap.ext_apply
                        intro z
                        rfl
    intro i hlow hi
    exact main (high-i) i rfl hlow hi
  exact hStages low le_rfl hLowHigh

/-- In the literal finite numerical-H K4 fixture, NO proposed block
containing either auxiliary cut 10 or 22 can be genuinely boring:
both are selected by every qualifying actual AlgorithmRun with
the physical original x=38 among initial seeds.

This refutes inference of full-source boringness from an unchanged
selected-front ordinary-L graph-age shadow. -/
theorem k4Gadget_no_genuinely_boring_block_across_10_or_22
    (X : Set (AdmissibleKptNode k4GadgetFamily))
    (hSeed : k4GadgetH.kptOriginal
      k4GadgetFamily k4GadgetH_avoids
      (⟨38, by change 38 < 40; decide⟩ : Fin k4GadgetH.size) ∈ X)
    (ell : Nat) (hEll : 22 < ell)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree k4GadgetFamily) X ell)
    (cut low high : Nat)
    (hCut : cut = 10 ∨ cut = 22)
    (hLow : low ≤ cut) (hHigh : cut < high)
    (hHighEll : high ≤ ell) :
    ¬ (∀ i : Nat, low ≤ i → i < high →
      ¬ SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree k4GadgetFamily)
        (SMTree.Envelope.closure (admissibleKptSTree k4GadgetFamily)
          (R.I (i+1)) X) i) := by
  intro hBoring
  have hSelected : cut ∈ R.I cut := by
    obtain ⟨hTen,hTwentyTwo⟩ :=
      k4Gadget_algorithmRun_selects_cuts10_22 X hSeed ell hEll R
    rcases hCut with hTenEq | hTwentyTwoEq
    · subst cut
      exact hTen
    · subst cut
      exact hTwentyTwo
  obtain ⟨D, _hSkips, _hCross, hI, _hF⟩ :=
    R.noninteresting_step cut (by omega)
      (hBoring cut hLow hHigh)
  rw [hI] at hSelected
  have hSelectedBound :=
    (R.I_mem_bounds (cut+1) (by omega) cut hSelected).1
  omega

end Kk
