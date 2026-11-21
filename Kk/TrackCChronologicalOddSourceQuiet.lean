import Kk.TrackCConstructedBareRealZeroQuiet
import Kk.TrackDOddStageNoFreeEnd
import Kk.TrackEOneBareRootEvenRealNoNovelty
import Kk.TrackEOriginalPrefixSocleCover
import Mathlib.Tactic

/-!
# Track C: genuine chronological one-bare-root odd source no-novelty

English-first adversarial mathematical audit:
  docs/track_c_chronological_odd_source_audit_20261121.md

A true physical odd cut has ZERO ordinary L column on all original
coordinates, but may end a selected auxiliary E-parameter.
The no-E-free-stage-end condition therefore remains explicit.
A genuine old-boring run has no OLD initial seed terminal; in a
one-root physical extension the NEW original's E-free end is the
chronological newTop, strictly ABOVE every old-range cut.
Hence NO extra seed/root-name membership assumption is needed.

Complete old Kpt ancestor matches for active originals and true
stage no-free-end exclude both generated I1 and missing full
SAME-NODE dependent old/upper L+/E pairs, even with I2 forks.
This is the candidate closure based on the old run's I(c+1),
NOT an arbitrary larger-height AlgorithmRun synchronization theorem.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Generic graph-signature odd-source quietness. Unlike the
graph-model-specialized E83 theorem, this works for an arbitrary
AgeTestModel 1 0 1 whose physical ordinary L is symmetric.

The ONLY new seed is one true original. Its E-free level is
assumed DIFFERENT from c; the genuinely chronological physical
adapter below DERIVES this from oldTop≤newTop and c<oldTop.
The complete original stage still must have NO E-free end at c.

No global odd-source quietness or new-run conclusion follows. -/
theorem finiteNumericH_old_boring_one_bare_odd_noNovelty_general
    (family : List (NormalizedForbidden 1 0 1))
    (L : AgeTestModel 1 0 1) (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (hSym : ∀ i j : Nat,
      (finiteNumericH L k M).L.binary i j (0 : Fin 1) =
        (finiteNumericH L k M).L.binary j i (0 : Fin 1))
    (W : Finset (Fin M))
    (X Y : Set (AdmissibleKptNode family))
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH L k M) hAvoid (W : Set (Fin M)))
    (newV : Fin M)
    (hBare : Y = X ∪
      ({(finiteNumericH L k M).kptOriginal family hAvoid newV} :
        Set (AdmissibleKptNode family)))
    (oldTop : Nat)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (a : Nat)
    (hBoring : ¬ SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family)
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (Rold.I ((2*a+1)+1)) X) (2*a+1))
    (hNewRootFreeNe :
      (finiteNumericH L k M).freeLevel newV.val ≠ 2*a+1)
    (hNoStageEnd : ∀ v : Fin M,
      v ∈ ambientStagePool (finiteNumericH L k M)
        (W : Set (Fin M)) (Rold.I ((2*a+1)+1)) →
      (finiteNumericH L k M).freeLevel v.val ≠ 2*a+1)
    (hOldPrefix : KptCandidateOriginalOldPrefixCovered
      family L k M hAvoid W X Y oldTop Rold (2*a+1)) :
    NewRootNoNoveltyAtCut family
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (Rold.I ((2*a+1)+1)) X)
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (Rold.I ((2*a+1)+1)) Y)
      (2*a+1) := by
  classical
  let c : Nat := 2*a+1
  have hNoOldSeed : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ X ∧ LevelTree.lev z = c :=
    kpt_old_actual_boring_no_initial_seed_at_cut
      family X oldTop c Rold hBoring
  have hNoYSeed : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ Y ∧ LevelTree.lev z = c := by
    rintro ⟨z, hz, hLev⟩
    rw [hBare] at hz
    rcases hz with hOld | hNew
    · exact hNoOldSeed ⟨z, hOld, hLev⟩
    · have hzEq :
          z = (finiteNumericH L k M).kptOriginal
            family hAvoid newV := by
        simpa only [Set.mem_singleton_iff] using hNew
      subst z
      exact hNewRootFreeNe hLev
  have hNoI1 : ¬ KptI1AtCut family
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (Rold.I (c+1)) Y) c := by
    change ¬ ∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (Rold.I (c+1)) Y ∧
      LevelTree.lev z = c
    exact finiteNumericH_odd_no_full_I1_of_no_seed_or_stage_free
      family L k M hAvoid hSym
      (Rold.I (c+1)) Y (W : Set (Fin M))
      hY a hNoYSeed hNoStageEnd
  have hXY : X ⊆ Y := by
    rw [hBare]
    intro x hx
    exact Or.inl hx
  have hZero : ∀ v : Fin M,
      v ∈ hStageOriginals L k M W (Rold.I (c+1)) →
      c+1 ≤ (finiteNumericH L k M).freeLevel v.val →
      (finiteNumericH L k M).L.binary
        c v.val (0 : Fin 1) = false := by
    intro v _hStage _hCross
    change hNumericBinary L.binary k (2*a+1) v.val
      (0 : Fin 1) = false
    exact hNumericBinary_odd_left_false
      L.binary k a v.val (0 : Fin 1)
  have hOldSocle :=
    finiteNumericH_candidate_old_socle_of_active_original_prefixes
      family L k M hAvoid W X Y hY oldTop Rold c hOldPrefix
  have hCertificate :=
    finiteNumericH_candidate_zero_stage_noNovelty_of_socle_and_noI1
      family L k M hAvoid hSym W X Y hXY hY
      oldTop Rold c hZero hOldSocle hNoI1
  exact hCertificate

/-- Genuine two-model base-extension consequence: oldTop≤newTop
and exact freeLevel(newV)=newTop exclude the new BARE root terminal
at every c=2a+1<oldTop. One actual old run and one fixed finite
physical original support W are CONSTRUCTED. Thus at every true
old-unselected odd c below the old horizon the ONLY additional
geometric hypotheses are full stage no-free-end and complete
old-prefix coverage of active original representatives.

No new target run is assumed or synchronized. -/
theorem finiteNumericH_constructed_bare_odd_quiet_of_stage_free_and_socle
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
        ∀ a : Nat,
          2*a+1 < oldTop →
          2*a+1 ∉ Rold.I (2*a+1) →
          (∀ v : Fin M,
            v ∈ ambientStagePool (finiteNumericH L k M)
              (W : Set (Fin M)) (Rold.I ((2*a+1)+1)) →
            (finiteNumericH L k M).freeLevel v.val ≠ 2*a+1) →
          KptCandidateOriginalOldPrefixCovered
            family L k M hAvoidL W X Y oldTop Rold (2*a+1) →
          NewRootNoNoveltyAtCut family
            (SMTree.Envelope.closure (admissibleKptSTree family)
              (Rold.I ((2*a+1)+1)) X)
            (SMTree.Envelope.closure (admissibleKptSTree family)
              (Rold.I ((2*a+1)+1)) Y)
            (2*a+1) := by
  classical
  let w : Fin M := ⟨hPosition k j k, hTarget⟩
  let Y : Set (AdmissibleKptNode family) :=
    finiteNumericH_bareTopRootSeeds
      family L k M j hAvoidL hTarget X
  obtain ⟨Rold, hOldTopSeed, _oldParams, _oldLive,
      _oldFinal, _oldInj, _oldPresent, _oldExact⟩ := hOldPhysical
  have hOldTopLe : oldTop ≤ hPosition k (j-1) k+1 :=
    finiteNumericH_old_physical_top_le_new_chronological_top
      family K k N j oldTop hNTop hAvoidK U X hSeeds hOldTopSeed
  obtain ⟨V, hCover, _hBound, _hTop⟩ :=
    finiteNumericH_bareTopRoot_seeds_represented_bounded
      family K L k b N M j
      hNM hBlock hk hj hTarget hNTop
      hBin hUn hDiag hAvoidK hAvoidL U X hSeeds (Rold.I 0)
  let W : Finset (Fin M) := Finset.univ.filter (fun v : Fin M => v ∈ V)
  have hW : (W : Set (Fin M)) = V := by
    ext v
    simp [W]
  have hY :
      Y ⊆ ambientPrefixPool family
        (finiteNumericH L k M) hAvoidL (W : Set (Fin M)) := by
    simpa only [hW] using hCover
  have hBare :
      Y = X ∪
        ({(finiteNumericH L k M).kptOriginal family hAvoidL w} :
          Set (AdmissibleKptNode family)) := by
    change X ∪
      ((fun v : Fin M =>
        (finiteNumericH L k M).kptOriginal family hAvoidL v) ''
        ({w} : Set (Fin M))) = _
    simp only [Set.image_singleton]
  refine ⟨Rold, W, hY, ?_⟩
  intro a hCut hUnselected hNoStageEnd hPrefix
  let c : Nat := 2*a+1
  have hBoring : ¬ SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family)
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (Rold.I (c+1)) X) c := by
    intro hInteresting
    have hStep := (Rold.interesting_step c hCut hInteresting).1
    apply hUnselected
    rw [hStep]
    exact Set.mem_insert_iff.mpr (Or.inl rfl)
  have hRootFree : (finiteNumericH L k M).freeLevel w.val =
      hPosition k (j-1) k+1 :=
    finiteNumericH_top_freeLevel_exact L k M j hk hj hTarget
  have hRootNe :
      (finiteNumericH L k M).freeLevel w.val ≠ c := by
    rw [hRootFree]
    omega
  exact finiteNumericH_old_boring_one_bare_odd_noNovelty_general
    family L k M hAvoidL hSymL W X Y hY
    w hBare oldTop Rold a hBoring hRootNe
    hNoStageEnd hPrefix

end Kk

#check @Kk.finiteNumericH_old_boring_one_bare_odd_noNovelty_general
#print axioms Kk.finiteNumericH_old_boring_one_bare_odd_noNovelty_general
#check @Kk.finiteNumericH_constructed_bare_odd_quiet_of_stage_free_and_socle
#print axioms Kk.finiteNumericH_constructed_bare_odd_quiet_of_stage_free_and_socle
