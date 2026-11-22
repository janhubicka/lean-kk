import Kk.TrackCUnifiedSafeRealOdd
import Kk.TrackCRawOriginalOldSocle
import Kk.TrackGBoringOnlyNoNoveltyRunTransfer
import Mathlib.Tactic

/-!
# Track C: genuine old RAW seed representatives yield a same-height target run

English proof and adversarial audit COMMITTED FIRST:
 docs/track_c_raw_seed_safe_run_english_audit_20261122.md

This combines three independently verified results:
* full numerical-H+ raw old-seed/physical-original type equality gives
  an actual OLD complete Kpt socle witness (Track C raw original theorem);
* maximal complete OLD socles cover real-zero AND genuinely safe odd
  source cuts of the actual constructed finite physical extension;
* no-novelty at every old-boring cut gives a genuine SAME-HEIGHT new
  AlgorithmRun with identical TOTAL I/F maps (Track G).

The RAW representative condition and off-safe quietness are separate
explicit premises, NOT verified consequences of a resolved diary.
No physically TALLER new run or common labelled inverse-source orbit
is constructed; there is no claim of a global BRD theorem.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A genuine OLD initial Kpt seed is a complete RAW old-prefix
representative of a physical numerical-H+ target original v at cut.

The old seed x is allowed to lie below a DIFFERENT original O_u.
The matching type is the literal full dependent PartialTypeWithE,
including both auxiliary E directions and negative ordinary L atoms.
Both the seed and target original must CROSS the cut strictly. -/
def KptRawOldSeedMatchAt
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (X : Set (AdmissibleKptNode family))
    (v : Fin M) (cut : Nat) : Prop :=
  ∃ (u : Fin M) (x : AdmissibleKptNode family),
    x ∈ X ∧
    x ≤ (finiteNumericH L k M).kptOriginal family hAvoid u ∧
    cut < LevelTree.lev x ∧
    cut < LevelTree.lev
      ((finiteNumericH L k M).kptOriginal family hAvoid v) ∧
    (finiteNumericH L k M).partialTypeAt cut u.val =
      (finiteNumericH L k M).partialTypeAt cut v.val

/-- The finite concrete raw witness is enough for the COMPLETE
OLD Kpt pre-cut socle. Unlike shadow-age comparison, this preserves
the whole directed auxiliary E and old ancestor subtype. -/
theorem kpt_raw_old_seed_match_implies_actual_old_socle
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (v : Fin M) (cut : Nat)
    (hRaw : KptRawOldSeedMatchAt
      family L k M hAvoid X v cut) :
    KptActualOldSocleCoveredAt family X top Rold
      ((finiteNumericH L k M).kptOriginal family hAvoid v) cut := by
  obtain ⟨u, x, hx, hBelow, hXCross, hVCross, hOldRaw⟩ := hRaw
  exact kpt_original_old_socle_covered_of_seed_raw_type_eq
    family L k M hAvoid X top Rold
    u v x hx hBelow cut hXCross hVCross hOldRaw

/-- A TRUE chronological K/L physical numerical-H+ extension yields
an actual SAME-HEIGHT new Kpt AlgorithmRun, with entire I and F equal
to the old run, if:

(1) each genuine physical original ACTIVE at at least one safe
    old-boring candidate cut has a finite full RAW old-seed type match
    at its HIGHEST such cut, and
(2) all old-boring cuts OUTSIDE the safe union independently have
    full new-root no-novelty.

The safe union consists exactly of FULL-stage positive REAL zero-L
cuts and genuine ODD cuts with no actual stage original E-free end.
Neither condition is derived from the resolved diary here.

The constructed new run stops at oldTop; no relation to the genuine
TALLER physical newTop run, or a diary-uniform BRD, is asserted. -/
theorem finiteNumericH_constructed_sameHeight_run_of_raw_seed_safe_and_offsafe
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
          KptRawOldSeedMatchAt family L k M hAvoidL X v
            ((kpt_actual_original_socle_allowed_cuts
              family L k M hAvoidL W X Y oldTop Rold
              (kptActualChronologicalSafeCuts
                family L k M W X oldTop Rold) v).max' hNonempty)) →
        (∀ cut : Nat, cut < oldTop →
          ¬ SMTree.Envelope.IsInterestingAt
            (normalizedKptSMTree family)
            (SMTree.Envelope.closure (admissibleKptSTree family)
              (Rold.I (cut+1)) X) cut →
          cut ∉ kptActualChronologicalSafeCuts
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
  obtain ⟨Rold, W, hY, hSafe⟩ :=
    finiteNumericH_constructed_safe_real_odd_quiet_of_max_socle
      family K L k b N M j hNM hBlock hk hj hTarget hNTop
      hBin hUn hDiag hAvoidK hAvoidL hSymL U X hSeeds
      oldTop hOldPhysical
  refine ⟨Rold, W, hY, ?_⟩
  intro hRaw hOffSafe
  have hMax : ∀ (v : Fin M),
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
            family L k M W X oldTop Rold) v).max' hNonempty) := by
    intro v hNonempty
    exact kpt_raw_old_seed_match_implies_actual_old_socle
      family L k M hAvoidL X oldTop Rold v _
      (hRaw v hNonempty)
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
  by_cases hSafeCut :
      cut ∈ kptActualChronologicalSafeCuts
        family L k M W X oldTop Rold
  · exact hSafe hMax cut hCut hOldBoring hSafeCut
  · exact hOffSafe cut hCut hOldBoring hSafeCut

end Kk

#check @Kk.kpt_raw_old_seed_match_implies_actual_old_socle
#print axioms Kk.kpt_raw_old_seed_match_implies_actual_old_socle
#check @Kk.finiteNumericH_constructed_sameHeight_run_of_raw_seed_safe_and_offsafe
#print axioms Kk.finiteNumericH_constructed_sameHeight_run_of_raw_seed_safe_and_offsafe
