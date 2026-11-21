import Kk.TrackCConstructedBareRealZeroQuiet
import Kk.TrackEOldSocleOriginalMaxFrontier
import Mathlib.Tactic

/-!
# Track C: maximal complete OLD Kpt-prefix checks at real zero stages

English-first adversarial proof:
  docs/track_c_max_original_zero_certificate_audit_20261121.md

In a genuine physical K/L base extension, the previously verified
Track C constructor produces ONE finite original coordinate support W.
For EACH v:Fin M, a complete old Kpt prefix witness at the maximal
eligible positive-real-zero, old-boring, candidate-crossing cut of v
suffices at ALL such cuts. E79 downward persistence supplies the
per-cut original-prefix certificates; the verified Track C theorem
then excludes full generated I1 and missing SAME-NODE old/upper L+/E
crossing pairs in the candidate using the actual old run's I tail.

No actual target-run synchronization, zero-stage existence, original
prefix witness existence, uniform diary carrier or BRD is proved.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Exactly the positive even-real coordinates where the FULL
actual stage of physical original source W has zero ordinary L
on every eligible cut-crossing original. The set can be
disconnected and its membership is not assumed for every cut. -/
def kptActualPositiveRealZeroCuts
    (family : List (NormalizedForbidden 1 0 1))
    (L : AgeTestModel 1 0 1) (k M : Nat)
    (W : Finset (Fin M))
    (X : Set (AdmissibleKptNode family))
    (oldTop : Nat)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop) : Set Nat :=
  {cut | ∃ idx g : Nat, cut = hPosition k idx g ∧ 0 < cut ∧
    ∀ v : Fin M,
      v ∈ hStageOriginals L k M W (Rold.I (cut+1)) →
      cut+1 ≤ (finiteNumericH L k M).freeLevel v.val →
      (finiteNumericH L k M).L.binary cut v.val (0 : Fin 1) = false}

/-- At most ONE complete OLD-prefix witness for every true
original coordinate (rather than one witness at every cut)
suffices for the entire finite family's candidate real-zero
no-novelty conclusions. All actual stage zero columns must still
be checked, and the maximal tests may remain unproved in a
resolved diary. -/
theorem finiteNumericH_constructed_bare_root_real_zero_of_max_socle
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
        (∀ (v : Fin M),
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
          NewRootNoNoveltyAtCut family
            (SMTree.Envelope.closure (admissibleKptSTree family)
              (Rold.I (hPosition k idx g+1)) X)
            (SMTree.Envelope.closure (admissibleKptSTree family)
              (Rold.I (hPosition k idx g+1)) Y)
            (hPosition k idx g) := by
  classical
  let Y : Set (AdmissibleKptNode family) :=
    finiteNumericH_bareTopRootSeeds
      family L k M j hAvoidL hTarget X
  obtain ⟨Rold, W, hY, hOneCut⟩ :=
    finiteNumericH_constructed_bare_root_real_zero_stage_quiet
      family K L k b N M j hNM hBlock hk hj hTarget hNTop
      hBin hUn hDiag hAvoidK hAvoidL hSymL U X hSeeds
      oldTop hOldPhysical
  refine ⟨Rold, W, hY, ?_⟩
  intro hMax idx g hPositive hCut hOldUnselected hZero
  apply hOneCut idx g hPositive hCut hOldUnselected hZero
  intro v hStage hRepresented
  let cut : Nat := hPosition k idx g
  have hOldBoring :
      ¬ SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family)
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (Rold.I (cut+1)) X) cut := by
    intro hInteresting
    have hStep := (Rold.interesting_step cut hCut hInteresting).1
    apply hOldUnselected
    rw [hStep]
    exact Set.mem_insert_iff.mpr (Or.inl rfl)
  have hAllowed :
      cut ∈ kptActualPositiveRealZeroCuts
        family L k M W X oldTop Rold := by
    exact ⟨idx, g, rfl, hPositive, hZero⟩
  change KptActualOldSocleCoveredAt family X oldTop Rold
    ((finiteNumericH L k M).kptOriginal family hAvoidL v) cut
  exact kpt_actual_original_socle_covered_of_all_allowed_max
    family L k M hAvoidL W X Y oldTop Rold
    (kptActualPositiveRealZeroCuts
      family L k M W X oldTop Rold) hMax
    v cut hCut hAllowed hOldBoring hStage hRepresented

end Kk

#check @Kk.finiteNumericH_constructed_bare_root_real_zero_of_max_socle
#print axioms Kk.finiteNumericH_constructed_bare_root_real_zero_of_max_socle
