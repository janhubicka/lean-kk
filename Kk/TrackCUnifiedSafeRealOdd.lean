import Kk.TrackCChronologicalOddSourceQuiet
import Kk.TrackCMaxOriginalZeroCertificate
import Kk.TrackEOldSocleOriginalMaxFrontier
import Mathlib.Tactic

/-!
Track C: ONE old-prefix maximal-cut certificate per physical original
for the UNION of real-zero and safe-odd source cut families.

English-first adversarial audit:
  docs/track_c_unified_safe_real_odd_cuts_audit_20261121.md

The genuine K/L numerical-H+ extension supplies ONE old real Kpt
AlgorithmRun Rold and ONE finite physical original pool W covering the
correct bare seed Y=X∪{ONE physical original}. Each original v needs
at most ONE OLD complete Kpt prefix witness at the maximal eligible
cut of EITHER safe class, not independent witnesses per class.

This proves full candidate source no-novelty at all genuinely
OLD-BORING cuts in the safe union, retaining generated I1 and SAME-NODE
dependent old/upper L+/E pairs. A genuine odd E-parameter endpoint,
nonzero positive real cut, or other source event stays OUTSIDE the
safe class unless independently certified.

No assertion that the diary actually supplies the prefix witnesses,
odd free-end exclusions, real zero columns or global BRD.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Exact safe source-coordinate class for one true old-run
candidate physical source: positive even-real cuts with the
COMPLETE W-stage ordinary L column zero, UNION odd cuts with
NO complete-stage original AUXILIARY E-free endpoint.

The two branches have distinct geometry. This is NOT the set of
all boring cuts of an arbitrary proposed diary. -/
def kptActualChronologicalSafeCuts
    (family : List (NormalizedForbidden 1 0 1))
    (L : AgeTestModel 1 0 1) (k M : Nat)
    (W : Finset (Fin M))
    (X : Set (AdmissibleKptNode family))
    (oldTop : Nat)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop) : Set Nat :=
  kptActualPositiveRealZeroCuts family L k M W X oldTop Rold ∪
    {cut | ∃ a : Nat, cut = 2*a+1 ∧
      ∀ v : Fin M,
        v ∈ ambientStagePool (finiteNumericH L k M)
          (W : Set (Fin M)) (Rold.I (cut+1)) →
        (finiteNumericH L k M).freeLevel v.val ≠ cut}

/-- One MAXIMAL complete OLD Kpt prefix witness per true physical
original is sufficient to exclude all full physical candidate I1
and new paired old/upper L+/E crossings at BOTH:
  (i) positive even-real FULL original-stage zero cuts, and
  (ii) odd cuts with NO physical-stage original free-level endpoint.

The genuine old Kpt run and a SINGLE finite original source pool W
are CONSTRUCTED from the original complete K/L physical extension.

All conditions are source-exact and preserve auxiliary directed E;
there is no claim about a physically taller new AlgorithmRun. -/
theorem finiteNumericH_constructed_safe_real_odd_quiet_of_max_socle
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
              (kptActualChronologicalSafeCuts
                family L k M W X oldTop Rold) v).Nonempty),
          KptActualOldSocleCoveredAt family X oldTop Rold
            ((finiteNumericH L k M).kptOriginal family hAvoidL v)
            ((kpt_actual_original_socle_allowed_cuts
              family L k M hAvoidL W X Y oldTop Rold
              (kptActualChronologicalSafeCuts
                family L k M W X oldTop Rold) v).max' hNonempty)) →
        ∀ cut : Nat, cut < oldTop →
          ¬ SMTree.Envelope.IsInterestingAt
            (normalizedKptSMTree family)
            (SMTree.Envelope.closure (admissibleKptSTree family)
              (Rold.I (cut+1)) X) cut →
          cut ∈ kptActualChronologicalSafeCuts
            family L k M W X oldTop Rold →
          NewRootNoNoveltyAtCut family
            (SMTree.Envelope.closure (admissibleKptSTree family)
              (Rold.I (cut+1)) X)
            (SMTree.Envelope.closure (admissibleKptSTree family)
              (Rold.I (cut+1)) Y) cut) := by
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
  have hRootFree :
      (finiteNumericH L k M).freeLevel w.val =
        hPosition k (j-1) k+1 :=
    finiteNumericH_top_freeLevel_exact L k M j hk hj hTarget
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
  have hBare : Y = X ∪
      ({(finiteNumericH L k M).kptOriginal family hAvoidL w} :
        Set (AdmissibleKptNode family)) := by
    change X ∪
      ((fun v : Fin M =>
        (finiteNumericH L k M).kptOriginal family hAvoidL v) ''
        ({w} : Set (Fin M))) = _
    simp only [Set.image_singleton]
  refine ⟨Rold, W, hY, ?_⟩
  intro hMax cut hCut hBoring hSafe
  have hOldUnselected : cut ∉ Rold.I cut := by
    intro hSel
    obtain ⟨_D, _hSkip, _hCross, hIEq, _hFEq⟩ :=
      Rold.noninteresting_step cut hCut hBoring
    have hInNext : cut ∈ Rold.I (cut+1) := by
      rw [hIEq] at hSel
      exact hSel
    have hTooHigh : cut+1 ≤ cut :=
      (Rold.I_mem_bounds (cut+1) (by omega) cut hInNext).1
    omega
  have hPrefix : KptCandidateOriginalOldPrefixCovered
      family L k M hAvoidL W X Y oldTop Rold cut := by
    intro v hStage hRep
    change KptActualOldSocleCoveredAt family X oldTop Rold
      ((finiteNumericH L k M).kptOriginal family hAvoidL v) cut
    exact kpt_actual_original_socle_covered_of_all_allowed_max
      family L k M hAvoidL W X Y oldTop Rold
      (kptActualChronologicalSafeCuts
        family L k M W X oldTop Rold) hMax
      v cut hCut hSafe hBoring hStage hRep
  rcases hSafe with hReal | hOdd
  · obtain ⟨idx, g, hEq, hPositive, hStageZero⟩ := hReal
    subst cut
    exact finiteNumericH_oldBoring_oneBare_real_zero_noNovelty
      family L k M hAvoidL hSymL W X Y w hBare hY
      oldTop Rold idx g hPositive hCut hOldUnselected
      hStageZero hPrefix
  · obtain ⟨a, hEq, hNoStageEnd⟩ := hOdd
    subst cut
    have hRootNe :
        (finiteNumericH L k M).freeLevel w.val ≠ 2*a+1 := by
      rw [hRootFree]
      omega
    exact finiteNumericH_old_boring_one_bare_odd_noNovelty_general
      family L k M hAvoidL hSymL W X Y hY
      w hBare oldTop Rold a hBoring hRootNe
      hNoStageEnd hPrefix

end Kk

#check @Kk.finiteNumericH_constructed_safe_real_odd_quiet_of_max_socle
#print axioms Kk.finiteNumericH_constructed_safe_real_odd_quiet_of_max_socle
