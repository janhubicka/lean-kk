import Kk.TrackDZeroMeetObstruction
import Kk.NumericHFullClosureSource
import Mathlib.Tactic

/-!
# Track D: eliminate full I1 terminals at an actual even-real numeric H cut

English-first proof and sixteen adversarial checks:
docs/audits/2026-11-19-track-d-even-real-no-i1-english.md

The closure-normal-form theorem covers ALL Kpt meets and E parameters,
not merely selected graph-age shadows. At an even real cut a nonseed
terminal is a meet of TWO genuine physical stage originals; positive
E free cuts of such originals cannot end at an even real position.
Thus both originals are eligible to cross the cut. If the ordinary
L cut bit of EVERY eligible stage original is zero, verified full
L+/E zero-column uniqueness forbids the meet at the tested level.

No current closure crossing name is presumed to represent the terminal,
and no global retained diary schedule or common source orbit is asserted.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- An actual finite numerical H+ even REAL cut has NO full Kpt
structural (I1) terminal once:
* no true initial seed ends at the tested cut;
* every eligible original in the COMPLETE physical stage pool has
  zero ORDINARY L cut bit;
* ordinary L of the physical ambient is symmetric.

The stage set I may be an arbitrary selected-level set, including
a genuine Run.I(cut+1). This is not an assumption on Run.I 0.
The proof uses the verified all-closure-source normal form and
the exact physical zero-column original-meet obstruction. -/
theorem finiteNumericH_even_real_no_full_I1_of_zero_stage
    (family : List (NormalizedForbidden 1 0 1))
    (K : AgeTestModel 1 0 1)
    (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hSym : ∀ i j : Nat,
      (finiteNumericH K k N).L.binary i j (0 : Fin 1) =
        (finiteNumericH K k N).L.binary j i (0 : Fin 1))
    (I : Set Nat)
    (X : Set (AdmissibleKptNode family))
    (U : Set (Fin (finiteNumericH K k N).size))
    (hSeeds : X ⊆
      ambientPrefixPool family (finiteNumericH K k N) hAvoid U)
    (idx g : Nat)
    (hPositive : 0 < hPosition k idx g)
    (hNoSeedAt : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ X ∧ LevelTree.lev z = hPosition k idx g)
    (hZeroStage : ∀ v : Fin (finiteNumericH K k N).size,
      v ∈ ambientStagePool
        (finiteNumericH K k N) U I →
      hPosition k idx g+1 ≤ (finiteNumericH K k N).freeLevel v.val →
      (finiteNumericH K k N).L.binary
        (hPosition k idx g) v.val (0 : Fin 1) = false) :
    ¬ ∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) I X ∧
      LevelTree.lev z = hPosition k idx g := by
  classical
  let A : EnumeratedPartialStructure 1 0 1 := finiteNumericH K k N
  let cut : Nat := hPosition k idx g
  rintro ⟨z,hz,hLev⟩
  have hNotSeed : z ∉ X := by
    intro hx
    exact hNoSeedAt ⟨z,hx,hLev⟩
  obtain ⟨v,hv,w,hw,hComp,hMeet⟩ :=
    finiteNumericH_even_real_level_nonseed_is_original_meet
      family K k N hAvoid I X U hSeeds z idx g hLev hz hNotSeed
  have hMeetLevel :
      LevelTree.lev
        (LevelTree.meet
          (A.kptOriginal family hAvoid v)
          (A.kptOriginal family hAvoid w)) = cut := by
    simpa only [A, cut, hMeet] using hLev
  have hGeV : cut ≤ A.freeLevel v.val := by
    have h := LevelTree.level_le_of_le
      (LevelTree.meet_le_left hComp)
    change LevelTree.lev
      (LevelTree.meet
        (A.kptOriginal family hAvoid v)
        (A.kptOriginal family hAvoid w)) ≤ A.freeLevel v.val at h
    omega
  have hGeW : cut ≤ A.freeLevel w.val := by
    have h := LevelTree.level_le_of_le
      (LevelTree.meet_le_right hComp)
    change LevelTree.lev
      (LevelTree.meet
        (A.kptOriginal family hAvoid v)
        (A.kptOriginal family hAvoid w)) ≤ A.freeLevel w.val at h
    omega
  have hPositiveV : 0 < A.freeLevel v.val :=
    lt_of_lt_of_le hPositive hGeV
  have hPositiveW : 0 < A.freeLevel w.val :=
    lt_of_lt_of_le hPositive hGeW
  have hNotEvenV : A.freeLevel v.val ≠ cut :=
    finiteNumericH_positive_freeLevel_ne_realPosition
      K k N v.val idx g v.isLt hPositiveV
  have hNotEvenW : A.freeLevel w.val ≠ cut :=
    finiteNumericH_positive_freeLevel_ne_realPosition
      K k N w.val idx g w.isLt hPositiveW
  have hFreeV : cut+1 ≤ A.freeLevel v.val := by omega
  have hFreeW : cut+1 ≤ A.freeLevel w.val := by omega
  have hZeroV : A.L.binary cut v.val (0 : Fin 1) = false :=
    hZeroStage v hv hFreeV
  have hZeroW : A.L.binary cut w.val (0 : Fin 1) = false :=
    hZeroStage w hw hFreeW
  exact
    (actual_zero_cut_originals_meet_level_ne_cut
      family A hSym hAvoid cut v w hFreeV hFreeW
      hZeroV hZeroW hComp) hMeetLevel

#print axioms Kk.finiteNumericH_even_real_no_full_I1_of_zero_stage

end Kk
