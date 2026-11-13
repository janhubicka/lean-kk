import Kk.NumericHTopSeedFullSource
import SuccessorTree.V10.I3AlgorithmRunPool
import SuccessorTree.V10.HHighOriginalNameEnumeration
import Mathlib.Tactic

/-!
# Track C: full dependent source with labels in the FINAL maintained pool

English argument and hostile audit COMMITTED BEFORE Lean:
  docs/track_c_final_pool_full_source_english_audit.md

The prior Track C theorem used all Fin N names. Here the source
universe is the much smaller actual final AlgorithmRun original pool
V = hStageOriginals ... U (R.I 0). Each source and its entire upper
L+ type are assigned to ONE name of type Fin V.card, not Fin N.

The FULL parameter-closed closure, no-(I2) and fixed run-tail
hypotheses are explicit. No global resolved-copy schedule,
unconditional B3 truth or labelled common source orbit is claimed.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Exact two-way closure crossing and full H+ source/upper-type
assignment over an ARBITRARY finite named pool of ambient numerical
H vertices representing all closure sources. The chosen F comes
from the complete closure and the SAME finite name function.

Every source type is assigned to ONE name v : Fin M with the
actual real coordinate and its full old and next L+ partial types.
No competing I2 meet is required for crossing coverage. -/
theorem finiteNumericH_named_pool_cut_crossing_and_upper_types
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (original : Fin M → Fin (finiteNumericH K k N).size)
    (Z : Set (AdmissibleKptNode family))
    (hPool : ∀ z, z ∈ Z →
      ∃ v : Fin M,
        z ≤ (finiteNumericH K k N).kptOriginal family hAvoid (original v))
    (cut : Nat)
    (hNoMeet : ¬ ∃ a : AdmissibleKptNode family,
      a ∈ Z ∧
      ∃ b : AdmissibleKptNode family,
        b ∈ Z ∧ SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :
    let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
    let F : PrescribedBoringData cut db du dd :=
      closureSelectedBoringData family A hAvoid original Z cut
    CoversClosureCrossing family Z cut F ∧
    IsCrossingGraphOf family Z cut F ∧
    (∀ T, T ∈ F.source →
      ∃ v : Fin M, ∃ i q : Nat,
        q ≤ k ∧ (original v).val = hPosition k i q ∧
        cut+1 ≤ A.freeLevel (original v).val ∧
        T = A.partialTypeAt cut (original v).val ∧
        F.target T = A.partialTypeAt (cut+1) (original v).val) := by
  classical
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  let F : PrescribedBoringData cut db du dd :=
    closureSelectedBoringData family A hAvoid original Z cut
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
  have hSources : ∀ T, T ∈ F.source →
      ∃ v : Fin M, ∃ i q : Nat,
        q ≤ k ∧ (original v).val = hPosition k i q ∧
        cut+1 ≤ A.freeLevel (original v).val ∧
        T = A.partialTypeAt cut (original v).val ∧
        F.target T = A.partialTypeAt (cut+1) (original v).val := by
    intro T hT
    obtain ⟨v,_hSelected,hFree,hOld,hNext⟩ :=
      selectedStagePoolPrescribedData_source_original
        A cut original
        (closureSelectedOriginal family A hAvoid original Z cut)
        T hT
    have hPositive : 0 < A.freeLevel (original v).val := by omega
    obtain ⟨i,q,hq,hReal⟩ :=
      finiteNumericH_positive_freeLevel_has_real_target
        K k N (original v) hPositive
    exact ⟨v,i,q,hq,hReal,hFree,hOld,hNext⟩
  exact ⟨hCover,hReverse,hSources⟩

/-- Actual AlgorithmRun version using ONLY the FINAL maintained
finite original-name pool V, not all numerical H coordinates.

The source membership/upper-L+ labels range over Fin V.card,
which is the concrete finite pool size used by the H numerical
signature-capacity bound. The result is conditional on precisely
the no-(I2) competing meet on the actual pre-cut closure. -/
theorem finiteNumericH_run_final_pool_crossing_and_upper_types
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N : Nat)
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family (finiteNumericH K k N)
      (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
      (U : Set (Fin N)))
    (top cut : Nat) (hCut : cut < top)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (hNoMeet : ¬ ∃ a : AdmissibleKptNode family,
      a ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X ∧
      ∃ b : AdmissibleKptNode family,
        b ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) X ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :
    let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
    let hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L :=
      finiteNumericH_avoids_family family K hCarrier k N hAvoidK
    let V : Finset (Fin N) := hStageOriginals K k N U (R.I 0)
    let original : Fin V.card → Fin A.size := hOriginalName V
    let Z : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1)) X
    let F : PrescribedBoringData cut db du dd :=
      closureSelectedBoringData family A hAvoidA original Z cut
    CoversClosureCrossing family Z cut F ∧
    IsCrossingGraphOf family Z cut F ∧
    (∀ T, T ∈ F.source →
      ∃ v : Fin V.card, ∃ i q : Nat,
        q ≤ k ∧ (original v).val = hPosition k i q ∧
        cut+1 ≤ A.freeLevel (original v).val ∧
        T = A.partialTypeAt cut (original v).val ∧
        F.target T = A.partialTypeAt (cut+1) (original v).val) := by
  classical
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  let hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L :=
    finiteNumericH_avoids_family family K hCarrier k N hAvoidK
  let V : Finset (Fin N) := hStageOriginals K k N U (R.I 0)
  let original : Fin V.card → Fin A.size := hOriginalName V
  let Z : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (R.I (cut+1)) X
  have hPool : ∀ z, z ∈ Z →
      ∃ v : Fin V.card,
        z ≤ A.kptOriginal family hAvoidA (original v) := by
    intro z hz
    obtain ⟨v,hv,hzv⟩ :=
      numericH_algorithmRun_closure_original_in_final_pool
        family K hCarrier hAvoidK k N U X hX
        top cut hCut R z hz
    let j : Fin V.card := V.equivFin ⟨v,hv⟩
    have hOriginal : original j = v := by
      simp [original, hOriginalName, j] <;> rfl
    refine ⟨j, ?_⟩
    simpa only [A,hAvoidA,hOriginal] using hzv
  exact finiteNumericH_named_pool_cut_crossing_and_upper_types
    family K k N hAvoidA original Z hPool cut hNoMeet

#print axioms Kk.finiteNumericH_named_pool_cut_crossing_and_upper_types
#print axioms Kk.finiteNumericH_run_final_pool_crossing_and_upper_types

end Kk
