import Kk.TrackDZeroMeetObstruction
import Kk.TrackDZeroStarFullI2
import Kk.TrackDPhysicalHSymmetry
import Kk.TrackDPreCutStageSource
import Kk.ActualRunOddStructural
import Kk.NumericHFullClosureSource
import Mathlib.Tactic

/-!
# Track D: actual odd fake cut without seed or stage free-cut endpoint is boring

Mathematical English proof and twenty adversarial checks were committed first:
docs/audits/2026-11-19-track-d-odd-stage-freecut-english.md

All three genuine AlgorithmRun obstructions (full I1, full I2 and ordinary
L-only corrected B3) are excluded without identifying the pre-cut stage
with a selected age shadow or the unknown FINAL Run.I(0) original pool.
The absence of a seed terminal and of a same-level stage original free
E-cut remain explicit hypotheses. Odd cuts CAN genuinely be selected
when an auxiliary E parameter ends there.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The COMPLETE actual Kpt closure at a genuine ODD numeric cut
has no I1 terminal provided neither the genuine seed source nor the
ENTIRE maintained stage original pool has an endpoint at that cut.
All generated parameter/meet nodes are covered by the real closure
normal form; a terminal meet of eligible originals is excluded by
the full zero-dependent-column meet theorem. -/
theorem finiteNumericH_odd_no_full_I1_of_no_seed_or_stage_free
    (family : List (NormalizedForbidden 1 0 1))
    (K : AgeTestModel 1 0 1)
    (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hSymA : ∀ x y : Nat,
      (finiteNumericH K k N).L.binary x y (0 : Fin 1) =
        (finiteNumericH K k N).L.binary y x (0 : Fin 1))
    (I : Set Nat) (X : Set (AdmissibleKptNode family))
    (U : Set (Fin N))
    (hSeeds : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid U)
    (a : Nat)
    (hNoSeed : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ X ∧ LevelTree.lev z = 2*a+1)
    (hNoStageEnd : ∀ v : Fin N,
      v ∈ ambientStagePool (finiteNumericH K k N) U I →
      (finiteNumericH K k N).freeLevel v.val ≠ 2*a+1) :
    ¬ ∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) I X ∧
      LevelTree.lev z = 2*a+1 := by
  classical
  let A : EnumeratedPartialStructure 1 0 1 := finiteNumericH K k N
  let cut : Nat := 2*a+1
  rintro ⟨z,hz,hLev⟩
  rcases finiteNumericH_all_closure_nodes_seed_parameter_or_meet
    family K k N hAvoid I X U hSeeds z hz with
    hSeed | ⟨v,hSelected,hPositive,hOriginal⟩ |
      ⟨v,hv,w,hw,hComp,hMeet⟩
  · exact hNoSeed ⟨z,hSeed,hLev⟩
  · have hStage : v ∈ ambientStagePool A U I := by
      right
      exact ⟨hSelected,hPositive⟩
    have hActualLevel : A.freeLevel v.val = cut := by
      rw [hOriginal] at hLev
      exact hLev
    exact (hNoStageEnd v hStage) hActualLevel
  · have hMeetLev :
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
    have hNoV : A.freeLevel v.val ≠ cut := hNoStageEnd v hv
    have hNoW : A.freeLevel w.val ≠ cut := hNoStageEnd w hw
    have hFreeV : cut+1 ≤ A.freeLevel v.val := by omega
    have hFreeW : cut+1 ≤ A.freeLevel w.val := by omega
    have hZeroV : A.L.binary cut v.val (0 : Fin 1) = false := by
      change hNumericBinary K.binary k (2*a+1) v.val
        (0 : Fin 1) = false
      exact hNumericBinary_odd_left_false K.binary k a v.val (0 : Fin 1)
    have hZeroW : A.L.binary cut w.val (0 : Fin 1) = false := by
      change hNumericBinary K.binary k (2*a+1) w.val
        (0 : Fin 1) = false
      exact hNumericBinary_odd_left_false K.binary k a w.val (0 : Fin 1)
    exact (actual_zero_cut_originals_meet_level_ne_cut
      family A hSymA hAvoid v w hFreeV hFreeW
      hZeroV hZeroW hComp) hMeetLev

/-- The genuine numerical-H Henson AlgorithmRun SKIPS an odd cut if
no seed and no original of the ACTUAL pre-cut stage ends at that cut.
This excludes the entire true I1 closure source by normal form,
the true I2 meet source by finite exhaustive original indices and
full L+/E zero-column fork exclusion, and true I3 by the checked
odd-cut nonselection theorem. No proposed retained Plan is needed. -/
theorem henson_actualRun_odd_unselected_of_no_seed_or_stage_free
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N : Nat)
    (U : Finset (Fin N))
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (X : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (hX : X ⊆ ambientPrefixPool
      (hensonForbiddenFamily ell hell)
      (finiteNumericH (normalizedGraphModel E) k N)
      hAvoid (U : Set (Fin N)))
    (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell)) X top)
    (hTop : ∃ x ∈ X, LevelTree.lev x = top)
    (a : Nat) (hBelow : 2*a+1 < top) (hCut : 2*a+1 < N)
    (hNoSeed : ¬ ∃ z : AdmissibleKptNode
      (hensonForbiddenFamily ell hell),
      z ∈ X ∧ LevelTree.lev z = 2*a+1)
    (hNoStageEnd : ∀ v : Fin N,
      v ∈ ambientStagePool
        (finiteNumericH (normalizedGraphModel E) k N)
        (U : Set (Fin N)) (Run.I ((2*a+1)+1)) →
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val
        ≠ 2*a+1) :
    2*a+1 ∉ Run.I 0 := by
  classical
  let family := hensonForbiddenFamily ell hell
  let K : AgeTestModel 1 0 1 := normalizedGraphModel E
  let A : EnumeratedPartialStructure 1 0 1 := finiteNumericH K k N
  let cut : Nat := 2*a+1
  let J : Set Nat := Run.I (cut+1)
  let Stage : Finset (Fin N) := hStageOriginals K k N U J
  let original : Fin Stage.card → Fin N := hOriginalName Stage
  let Z : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family) J X
  have hSymA : ∀ x y : Nat,
      A.L.binary x y (0 : Fin 1) =
        A.L.binary y x (0 : Fin 1) :=
    finiteNumericH_graph_ordinary_L_symmetric E hSym k N
  have hNoI1 :
      ¬ ∃ z : AdmissibleKptNode family,
        z ∈ Z ∧ LevelTree.lev z = cut :=
    finiteNumericH_odd_no_full_I1_of_no_seed_or_stage_free
      family K k N hAvoid hSymA J X (U : Set (Fin N))
      hX a hNoSeed hNoStageEnd
  obtain ⟨_hSub,hPool,_hFinal⟩ :=
    finiteNumericH_run_stage_and_final_pool_exhaust_same_closure
      family K k N hAvoid U X hX top Run cut hBelow
  have hZeroFull : ∀ v : Fin Stage.card,
      closureSelectedOriginal family A hAvoid original Z cut v →
      cut+1 ≤ A.freeLevel (original v).val →
      A.L.binary cut (original v).val (0 : Fin 1) = false := by
    intro v _ _
    change hNumericBinary K.binary k (2*a+1)
      (original v).val (0 : Fin 1) = false
    exact hNumericBinary_odd_left_false
      K.binary k a (original v).val (0 : Fin 1)
  have hNoI2 :
      ¬ ∃ u : AdmissibleKptNode family, u ∈ Z ∧
        ∃ v : AdmissibleKptNode family, v ∈ Z ∧
          SMTree.Envelope.SameComponent u v ∧
          LevelTree.lev (LevelTree.meet u v) = cut :=
    full_kpt_no_i2_of_no_i1_and_zero_full_physical_star
      family A hSymA hAvoid original Z hPool cut hZeroFull hNoI1
  exact henson_numericH_odd_cut_unselected_of_no_I1_I2
    ell hell k hK E hLoops hSym hClique
    N U hAvoid X hX top Run hTop
    a hBelow hCut
    (show ¬ KptI1AtCut family Z cut from hNoI1)
    (show ¬ KptI2MeetAtCut family Z cut from hNoI2)

#print axioms Kk.finiteNumericH_odd_no_full_I1_of_no_seed_or_stage_free
#print axioms Kk.henson_actualRun_odd_unselected_of_no_seed_or_stage_free

end Kk
