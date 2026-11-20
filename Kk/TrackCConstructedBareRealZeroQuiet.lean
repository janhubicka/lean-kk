import Kk.TrackCOneBareEvenRealZeroQuiet
import Kk.PhysicalBareNewRootRun
import Mathlib.Tactic

/-!
# Track C: construct one finite physical original support for all old-boring real-zero cuts

English proof and hostile audit:
 docs/track_c_constructed_bare_stage_real_zero_audit_20261120.md

Starts from actual old/new numerical-H+ physical base-extension hypotheses,
constructs the OLD genuine Kpt AlgorithmRun and a single finite pool W
representing the corrected BARE one-original new-root source. At EVERY
old-unselected positive even-real source cut where the COMPLETE physical
W-stage original columns are zero and the active original OLD Kpt prefixes
are matched, the FULL candidate old/upper L+/E source is quiet.

The zero-column and complete original-prefix requirements are genuine
remaining geometric premises, not automatic from the base extension.
No new-run selected-level equality or common diary inverse orbit is asserted.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The old/new physical base-extension constructor determines ONE
finite original pool W of the larger numerical H+ structure that
faithfully represents the corrected new BARE root Kpt seed family
Y = X ∪ {one genuine original}. This W works uniformly for EVERY
tested old-boring positive even-real cut of this ONE finite extension.

Whenever the true full W-stage zeros and complete OLD original-prefix
socle matches hold at a tested cut, the candidate FULL Kpt pre-cut
source with the OLD selected level tail has no novel I1 terminal
and no novel complete dependent old/upper L+/E crossing pair.

NO new AlgorithmRun is presumed or its selected levels compared. -/
theorem finiteNumericH_constructed_bare_root_real_zero_stage_quiet
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
        ∀ (idx g : Nat),
          0 < hPosition k idx g →
          hPosition k idx g < oldTop →
          hPosition k idx g ∉ Rold.I (hPosition k idx g) →
          (∀ v : Fin M,
            v ∈ hStageOriginals L k M W
              (Rold.I (hPosition k idx g+1)) →
            hPosition k idx g+1 ≤
              (finiteNumericH L k M).freeLevel v.val →
            (finiteNumericH L k M).L.binary
              (hPosition k idx g) v.val (0 : Fin 1) = false) →
          (∀ (v : Fin M),
            v ∈ hStageOriginals L k M W
              (Rold.I (hPosition k idx g+1)) →
            (∃ z : AdmissibleKptNode family,
              z ∈ SMTree.Envelope.closure
                (admissibleKptSTree family)
                (Rold.I (hPosition k idx g+1)) Y ∧
              hPosition k idx g < LevelTree.lev z ∧
              z ≤ (finiteNumericH L k M).kptOriginal family hAvoidL v) →
            ∃ w : AdmissibleKptNode family,
              w ∈ SMTree.Envelope.closure
                (admissibleKptSTree family)
                (Rold.I (hPosition k idx g+1)) X ∧
              ∃ (hV : hPosition k idx g < LevelTree.lev
                ((finiteNumericH L k M).kptOriginal family hAvoidL v))
                (hW : hPosition k idx g < LevelTree.lev w),
                LevelTree.ancestor
                  ((finiteNumericH L k M).kptOriginal family hAvoidL v)
                  (hPosition k idx g) (Nat.le_of_lt hV) =
                LevelTree.ancestor w (hPosition k idx g)
                  (Nat.le_of_lt hW)) →
          NewRootNoNoveltyAtCut family
            (SMTree.Envelope.closure (admissibleKptSTree family)
              (Rold.I (hPosition k idx g+1)) X)
            (SMTree.Envelope.closure (admissibleKptSTree family)
              (Rold.I (hPosition k idx g+1)) Y)
            (hPosition k idx g) := by
  classical
  let w : Fin M := ⟨hPosition k j k, hTarget⟩
  let Y : Set (AdmissibleKptNode family) :=
    finiteNumericH_bareTopRootSeeds
      family L k M j hAvoidL hTarget X
  obtain ⟨Rold, _hTopSeed, _oldParams, _oldLive,
      _oldFinal, _oldInj, _oldPresent, _oldExact⟩ := hOldPhysical
  obtain ⟨V, hCover, _hBound, _hTop⟩ :=
    finiteNumericH_bareTopRoot_seeds_represented_bounded
      family K L k b N M j hNM hBlock hk hj hTarget hNTop
      hBin hUn hDiag hAvoidK hAvoidL U X hSeeds (Rold.I 0)
  let W : Finset (Fin M) :=
    Finset.univ.filter (fun v : Fin M => v ∈ V)
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
  intro idx g hPositive hCut hOldUnselected hZero hOriginalPrefix
  exact finiteNumericH_oldBoring_oneBare_real_zero_noNovelty
    family L k M hAvoidL hSymL W X Y w hBare hY
    oldTop Rold idx g hPositive hCut hOldUnselected
    hZero hOriginalPrefix

end Kk

#check @Kk.finiteNumericH_constructed_bare_root_real_zero_stage_quiet
#print axioms Kk.finiteNumericH_constructed_bare_root_real_zero_stage_quiet
