import Kk.TrackEZeroColumnSocleCrossing
import Kk.TrackDEvenRealNoI1
import Kk.TrackDPhysicalHSymmetry
import Mathlib.Tactic

/-!
# Track E E73: full physical no-novelty at a true positive even-real zero stage

English-FIRST proof and 17 hostile checks:
docs/track_e_even_real_zero_stage_no_novelty_english_audit_20261119.md

Combine the independently verified Track D exact full-I1-terminal
exclusion at positive even REAL numerical-H+ zero-column cuts with
Track E E72 full dependent old/upper L+/E crossing inclusion from
complete OLD Kpt source-socle coverage. All source closures are
calculated with the ONE OLD AlgorithmRun's R.I(c+1) level tail.

No target run, auxiliary finite source index, I2-functionality,
positive-L-only projection, global diary carrier or BRD is assumed.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- At a positive even real H+ cut with NO initial Y seed
ending there, zero ordinary-L on ALL eligible physical stage
originals, and exact OLD complete Kpt socle coverage, the
entire candidate full parameter-closed source is physically
quiet: no new I1 terminal and no missing complete old/upper
dependent L+/E crossing pair.

This theorem needs only ONE old actual AlgorithmRun R on X and
candidate closure_(R.I(c+1))(Y). It does not assert that the
zero/socle hypotheses hold for the resolved Q stage. -/
theorem finiteNumericH_even_real_candidate_noNovelty_of_zero_socle
    (family : List (NormalizedForbidden 1 0 1))
    (K : AgeTestModel 1 0 1) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hSym : ∀ i j : Nat,
      (finiteNumericH K k N).L.binary i j (0 : Fin 1) =
        (finiteNumericH K k N).L.binary j i (0 : Fin 1))
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid (U : Set (Fin N)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (idx g : Nat)
    (hPositive : 0 < hPosition k idx g)
    (hNoYSeedAt : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ Y ∧ LevelTree.lev z = hPosition k idx g)
    (hZeroStage : ∀ v : Fin N,
      v ∈ hStageOriginals K k N U
        (R.I (hPosition k idx g+1)) →
      hPosition k idx g+1 ≤
        (finiteNumericH K k N).freeLevel v.val →
      (finiteNumericH K k N).L.binary
        (hPosition k idx g) v.val (0 : Fin 1) = false)
    (hOldSocle : ∀ (z : AdmissibleKptNode family),
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family)
        (R.I (hPosition k idx g+1)) Y →
      ∀ (hZCross : hPosition k idx g < LevelTree.lev z),
        ∃ w : AdmissibleKptNode family,
          w ∈ SMTree.Envelope.closure
            (admissibleKptSTree family)
            (R.I (hPosition k idx g+1)) X ∧
          ∃ (hWCross : hPosition k idx g < LevelTree.lev w),
          LevelTree.ancestor z (hPosition k idx g)
            (Nat.le_of_lt hZCross) =
          LevelTree.ancestor w (hPosition k idx g)
            (Nat.le_of_lt hWCross)) :
    NewRootNoNoveltyAtCut family
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (hPosition k idx g+1)) X)
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (hPosition k idx g+1)) Y)
      (hPosition k idx g) := by
  classical
  let cut : Nat := hPosition k idx g
  let A : EnumeratedPartialStructure 1 0 1 := finiteNumericH K k N
  have hZeroAmbient :
      ∀ v : Fin A.size,
        v ∈ ambientStagePool A
          (U : Set (Fin N)) (R.I (cut+1)) →
        cut+1 ≤ A.freeLevel v.val →
        A.L.binary cut v.val (0 : Fin 1) = false := by
    intro v hv hFree
    have hMember :
        v ∈ U ∨
          (v.val ∈ R.I (cut+1) ∧ 0 < A.freeLevel v.val) := by
      change v ∈ (U : Set (Fin N)) ∪
        {i : Fin N | i.val ∈ R.I (cut+1) ∧
          0 < A.freeLevel i.val} at hv
      rcases hv with hRoot | hParam
      · exact Or.inl (Finset.mem_coe.mp hRoot)
      · exact Or.inr hParam
    have hStage :
        v ∈ hStageOriginals K k N U (R.I (cut+1)) := by
      letI : DecidablePred (fun q : Fin N =>
          q ∈ U ∨
            (q.val ∈ R.I (cut+1) ∧
              0 < (finiteNumericH K k N).freeLevel q.val)) :=
        Classical.decPred _
      change v ∈ Finset.univ.filter (fun q : Fin N =>
        q ∈ U ∨ (q.val ∈ R.I (cut+1) ∧
          0 < (finiteNumericH K k N).freeLevel q.val))
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ v, by simpa only [A] using hMember⟩
    exact hZeroStage v hStage hFree
  have hNoI1 :
      ¬ KptI1AtCut family
        (SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) Y) cut := by
    change ¬ ∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y ∧
      LevelTree.lev z = cut
    exact finiteNumericH_even_real_no_full_I1_of_zero_stage
      family K k N hAvoid hSym (R.I (cut+1)) Y
      (U : Set (Fin N)) hY idx g hPositive
      hNoYSeedAt hZeroAmbient
  exact finiteNumericH_candidate_zero_stage_noNovelty_of_socle_and_noI1
    family K k N hAvoid hSym U X Y hXY hY top R
    cut hZeroStage hOldSocle hNoI1

/-- In a real H+ expansion of a SYMMETRIC original graph,
ambient ordinary L is automatically symmetric on EVERY physical
coordinate (including fakes), but the auxiliary E relation remains
directed. Hence the even-real no-novelty result needs only
the original graph symmetry as an input. -/
theorem finiteNumericH_graph_even_real_candidate_noNovelty_of_zero_socle
    (family : List (NormalizedForbidden 1 0 1))
    (E : Nat → Nat → Bool)
    (hGraphSym : ∀ i j, E i j = E j i)
    (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids
        (finiteNumericH (normalizedGraphModel E) k N).L)
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH (normalizedGraphModel E) k N) hAvoid
        (U : Set (Fin N)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (idx g : Nat)
    (hPositive : 0 < hPosition k idx g)
    (hNoYSeedAt : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ Y ∧ LevelTree.lev z = hPosition k idx g)
    (hZeroStage : ∀ v : Fin N,
      v ∈ hStageOriginals (normalizedGraphModel E) k N U
        (R.I (hPosition k idx g+1)) →
      hPosition k idx g+1 ≤
        (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val →
      (finiteNumericH (normalizedGraphModel E) k N).L.binary
        (hPosition k idx g) v.val (0 : Fin 1) = false)
    (hOldSocle : ∀ (z : AdmissibleKptNode family),
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family)
        (R.I (hPosition k idx g+1)) Y →
      ∀ (hZCross : hPosition k idx g < LevelTree.lev z),
        ∃ w : AdmissibleKptNode family,
          w ∈ SMTree.Envelope.closure
            (admissibleKptSTree family)
            (R.I (hPosition k idx g+1)) X ∧
          ∃ (hWCross : hPosition k idx g < LevelTree.lev w),
          LevelTree.ancestor z (hPosition k idx g)
            (Nat.le_of_lt hZCross) =
          LevelTree.ancestor w (hPosition k idx g)
            (Nat.le_of_lt hWCross)) :
    NewRootNoNoveltyAtCut family
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (hPosition k idx g+1)) X)
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (hPosition k idx g+1)) Y)
      (hPosition k idx g) := by
  exact finiteNumericH_even_real_candidate_noNovelty_of_zero_socle
    family (normalizedGraphModel E) k N hAvoid
    (fun i j => finiteNumericH_graph_ordinary_L_symmetric
      E hGraphSym k N i j)
    U X Y hXY hY top R idx g
    hPositive hNoYSeedAt hZeroStage hOldSocle

end Kk
