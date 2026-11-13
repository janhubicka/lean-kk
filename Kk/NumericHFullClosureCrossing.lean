import Kk.NumericHFullClosureSource
import SuccessorTree.V10.I3ClosureSelectedCrossing
import Mathlib.Tactic

/-!
# Track C: the complete physical finite H+ crossing source at one cut

English mathematical proof and adversarial review COMMITTED FIRST:
  docs/track_c_cut_crossing_upper_types_english_audit.md

This is NOT a selected-shadow age test. The source is the COMPLETE
meet-and-parameter closure on a genuine finite numerical H+ stage.
An actual original-prefix seed-pool hypothesis gives a full ambient
pool representation for every recursively generated closure node.

Under no actual (I2) competing meet at cut p, the canonical
closure-selected prescribed source F covers EVERY crossing in that
closure. Conversely, every F-source comes from a genuine crossing
closure node and admits one SAME physical H+ original with both
FULL old/next L+ partial types. Its positive free cut forces that
ambient representative to be a REAL H coordinate, never an odd fake
E-target. This does not delete fake numeric E-predecessors from the
old types.

No global resolved-diary schedule, full (B3) truth, or common
labelled source orbit is inferred.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A finite numerical H+ vertex with positive CANONICAL auxiliary
E free level must be a genuine REAL encoded coordinate iota(i,q)
for some q <= k. A fake odd coordinate may be E-positive as a
PREDECESSOR of another target, but it has no nonempty incoming E
column of its own. This is proved from the literal finite E generator,
not from an unsupported real/fake classification axiom. -/
theorem finiteNumericH_positive_freeLevel_has_real_target
    {db du dd : Nat} (K : AgeTestModel db du dd)
    (k N : Nat) (v : Fin (finiteNumericH K k N).size)
    (hPositive : 0 < (finiteNumericH K k N).freeLevel v.val) :
    ∃ i q : Nat, q ≤ k ∧ v.val = hPosition k i q := by
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  have hE : A.E 0 v.val = true :=
    (A.E_iff_freeLevel 0 v.val).2 hPositive
  have hFinite : finiteNumericHE k N 0 v.val = true := hE
  have hExact : exactHEBool k 0 v.val = true :=
    ((finiteNumericHE_true_iff k N 0 v.val).1 hFinite).2
  obtain ⟨i,q,hq,hReal,_hGenerated⟩ :=
    (exactHEBool_true_iff k 0 v.val).1 hExact
  exact ⟨i,q,hq,hReal⟩

/-- At any finite numerical H+ stage, under actual finite-family
avoidance and a real original-prefix representation of initial seeds,
the ENTIRE parameter-closed Kpt crossing source is visible with full
old and next L+ types.

Let Z be the genuine closure at selected level set I, and let F
be precisely the closure-selected prescribed partial function built
from that Z over the full physical carrier Fin N, not a selected
shadow. If no two elements of Z have a competing meet at level cut,
then:

(1) F covers every actual closure crossing;
(2) every F-input really comes from a closure crossing (reverse graph);
(3) every F-input has ONE genuine REAL numerical H coordinate whose
old and assigned upper L+ partial types agree exactly with F.

The physical representative may have generation zero. No result
about corrected B3, occurrence-independent sources, or full
unbounded recursive schedule is claimed. -/
theorem finiteNumericH_full_cut_crossing_and_upper_types
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Set (Fin (finiteNumericH K k N).size))
    (X : Set (AdmissibleKptNode family))
    (hSeeds : X ⊆
      ambientPrefixPool family (finiteNumericH K k N) hAvoid U)
    (I : Set Nat) (cut : Nat)
    (hNoMeet : ¬ ∃ a : AdmissibleKptNode family,
      a ∈ SMTree.Envelope.closure (admissibleKptSTree family) I X ∧
      ∃ b : AdmissibleKptNode family,
        b ∈ SMTree.Envelope.closure (admissibleKptSTree family) I X ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :
    let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
    let Z : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family) I X
    let original : Fin A.size → Fin A.size := fun v => v
    let F : PrescribedBoringData cut db du dd :=
      closureSelectedBoringData family A hAvoid original Z cut
    CoversClosureCrossing family Z cut F ∧
    IsCrossingGraphOf family Z cut F ∧
    (∀ T, T ∈ F.source →
      ∃ v : Fin A.size, ∃ i q : Nat,
        q ≤ k ∧ v.val = hPosition k i q ∧
        cut+1 ≤ A.freeLevel v.val ∧
        T = A.partialTypeAt cut v.val ∧
        F.target T = A.partialTypeAt (cut+1) v.val) := by
  classical
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  let Z : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family) I X
  let original : Fin A.size → Fin A.size := fun v => v
  let F : PrescribedBoringData cut db du dd :=
    closureSelectedBoringData family A hAvoid original Z cut
  have hStage :
      Z ⊆ ambientPrefixPool family A hAvoid
        (ambientStagePool A U I) :=
    admissibleKpt_stage_closure_subset_pool
      family A hAvoid U I X hSeeds
  have hPool : ∀ z, z ∈ Z →
      ∃ v : Fin A.size,
        z ≤ A.kptOriginal family hAvoid (original v) := by
    intro z hz
    rcases hStage hz with ⟨o, ⟨v,_hv,rfl⟩,hBelow⟩
    exact ⟨v,hBelow⟩
  have hCover : CoversClosureCrossing family Z cut F :=
    closureSelectedBoringData_covers family A hAvoid
      original Z hPool cut hNoMeet
  have hReverse : IsCrossingGraphOf family Z cut F := by
    intro T hT
    obtain ⟨v,hSelected,_hFree,hOld,hNext⟩ :=
      selectedStagePoolPrescribedData_source_original
        A cut original
        (closureSelectedOriginal family A hAvoid original Z cut)
        T hT
    change F.target T =
      A.partialTypeAt (cut+1) (original v).val at hNext
    obtain ⟨z,hz,hzCut,hZv⟩ := hSelected
    refine ⟨z,hz,hzCut,?_,?_⟩
    · calc
        (⟨cut,T⟩ : RawPartialTypeNode db du dd) =
            (⟨cut,A.partialTypeAt cut (original v).val⟩ :
              RawPartialTypeNode db du dd) := by rw [hOld]
        _ = (LevelTree.ancestor z cut
              (Nat.le_of_lt hzCut)).val :=
          (kptBelowOriginal_ancestor_raw
            family A hAvoid (original v) z hZv
            cut (Nat.le_of_lt hzCut)).symm
    · calc
        (⟨cut+1,F.target T⟩ : RawPartialTypeNode db du dd) =
            (⟨cut+1,A.partialTypeAt (cut+1) (original v).val⟩ :
              RawPartialTypeNode db du dd) := by rw [hNext]
        _ = (LevelTree.ancestor z (cut+1)
              (Nat.succ_le_iff.mpr hzCut)).val :=
          (kptBelowOriginal_ancestor_raw
            family A hAvoid (original v) z hZv
            (cut+1) (Nat.succ_le_iff.mpr hzCut)).symm
  have hSource : ∀ T, T ∈ F.source →
      ∃ v : Fin A.size, ∃ i q : Nat,
        q ≤ k ∧ v.val = hPosition k i q ∧
        cut+1 ≤ A.freeLevel v.val ∧
        T = A.partialTypeAt cut v.val ∧
        F.target T = A.partialTypeAt (cut+1) v.val := by
    intro T hT
    obtain ⟨v,_hSelected,hFree,hOld,hNext⟩ :=
      selectedStagePoolPrescribedData_source_original
        A cut original
        (closureSelectedOriginal family A hAvoid original Z cut)
        T hT
    have hPositive : 0 < A.freeLevel (original v).val := by omega
    obtain ⟨i,q,hq,hReal⟩ :=
      finiteNumericH_positive_freeLevel_has_real_target
        K k N v hPositive
    exact ⟨v,i,q,hq,hReal,hFree,hOld,hNext⟩
  exact ⟨hCover,hReverse,hSource⟩

/-- The same COMPLETE physical crossing source/upper-type theorem
at an actual downward AlgorithmRun pre-cut source Z, not a
hypothetical selected-level set. The real run cut lies inside the
scan horizon, and the exact competing-(I2) failure test is retained.

All three conclusions refer to ONE same actual run closure R.I(cut+1).
No inference is made that the run necessarily satisfies no-(I2).
-/
theorem finiteNumericH_run_cut_crossing_and_upper_types
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Set (Fin (finiteNumericH K k N).size))
    (X : Set (AdmissibleKptNode family))
    (hSeeds : X ⊆
      ambientPrefixPool family (finiteNumericH K k N) hAvoid U)
    (runHeight : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X runHeight)
    (cut : Nat) (_hScan : cut < runHeight)
    (hNoMeet : ¬ ∃ a : AdmissibleKptNode family,
      a ∈ SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1)) X ∧
      ∃ b : AdmissibleKptNode family,
        b ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (R.I (cut+1)) X ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :
    let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
    let Z : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1)) X
    let original : Fin A.size → Fin A.size := fun v => v
    let F : PrescribedBoringData cut db du dd :=
      closureSelectedBoringData family A hAvoid original Z cut
    CoversClosureCrossing family Z cut F ∧
    IsCrossingGraphOf family Z cut F ∧
    (∀ T, T ∈ F.source →
      ∃ v : Fin A.size, ∃ i q : Nat,
        q ≤ k ∧ v.val = hPosition k i q ∧
        cut+1 ≤ A.freeLevel v.val ∧
        T = A.partialTypeAt cut v.val ∧
        F.target T = A.partialTypeAt (cut+1) v.val) := by
  exact finiteNumericH_full_cut_crossing_and_upper_types
    family K k N hAvoid U X hSeeds (R.I (cut+1)) cut hNoMeet

#print axioms Kk.finiteNumericH_positive_freeLevel_has_real_target
#print axioms Kk.finiteNumericH_full_cut_crossing_and_upper_types
#print axioms Kk.finiteNumericH_run_cut_crossing_and_upper_types

end Kk
