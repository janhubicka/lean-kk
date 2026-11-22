import Kk.TrackCRawSeedSafeRun
import Mathlib.Tactic

/-!
# Track A/C: complete physical RAW seed witness for a candidate DESCENDANT

English proof FIRST with 15 adversarial checks:
 docs/track_a_candidate_descendant_raw_seed_old_socle_english_audit_20261122.md

Previous Track C theorem covers target ORIGINAL O_v. This extends
that source-correct RAW witness to an ARBITRARY actual candidate
Kpt node z<=O_v, including generated meets or auxiliary parameters.
No assumed new AlgorithmRun or raw-to-ordinary-age shortcut.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

/-- A TRUE old initial seed x below O_u and a possibly non-original
candidate node z below O_v share their COMPLETE dependent old Kpt
cut ancestor if the two physical original raw types are identical
at cut. Old witness is x in the actual pre-cut closure of R on X. -/
theorem finiteNumericH_candidate_below_original_old_socle_of_seed_raw_type_eq
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (u v : Fin M)
    (x z : AdmissibleKptNode family)
    (hx : x ∈ X)
    (hXBelow : x ≤
      (finiteNumericH L k M).kptOriginal family hAvoid u)
    (hZBelow : z ≤
      (finiteNumericH L k M).kptOriginal family hAvoid v)
    (cut : Nat)
    (hXCross : cut < LevelTree.lev x)
    (hZCross : cut < LevelTree.lev z)
    (hOldRawEq :
      (finiteNumericH L k M).partialTypeAt cut u.val =
        (finiteNumericH L k M).partialTypeAt cut v.val) :
    KptActualOldSocleCoveredAt family X top R z cut := by
  let A : EnumeratedPartialStructure db du dd :=
    finiteNumericH L k M
  have hZRaw :
      (LevelTree.ancestor z cut (Nat.le_of_lt hZCross)).val =
        (⟨cut, A.partialTypeAt cut v.val⟩ :
          RawPartialTypeNode db du dd) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid v z hZBelow cut (Nat.le_of_lt hZCross)
  have hXRaw :
      (LevelTree.ancestor x cut (Nat.le_of_lt hXCross)).val =
        (⟨cut, A.partialTypeAt cut u.val⟩ :
          RawPartialTypeNode db du dd) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid u x hXBelow cut (Nat.le_of_lt hXCross)
  have hEq :
      LevelTree.ancestor z cut (Nat.le_of_lt hZCross) =
        LevelTree.ancestor x cut (Nat.le_of_lt hXCross) := by
    apply Subtype.ext
    calc
      (LevelTree.ancestor z cut (Nat.le_of_lt hZCross)).val =
          (⟨cut, A.partialTypeAt cut v.val⟩ :
            RawPartialTypeNode db du dd) := hZRaw
      _ = (⟨cut, A.partialTypeAt cut u.val⟩ :
            RawPartialTypeNode db du dd) := by rw [← hOldRawEq]
      _ = (LevelTree.ancestor x cut (Nat.le_of_lt hXCross)).val :=
        hXRaw.symm
  refine ⟨x, ?_, hZCross, hXCross, hEq⟩
  exact (SMTree.Envelope.subset_closure
    (admissibleKptSTree family) (R.I (cut+1)) X) hx

/-- Existing Track C's finite RAW old-seed match for the physical
original O_v also witnesses the full OLD dependent Kpt ancestor
of ANY crossing candidate node z below O_v. No Y-run is assumed. -/
theorem finiteNumericH_candidate_below_original_old_socle_of_raw_seed_match
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (v : Fin M) (z : AdmissibleKptNode family)
    (hZBelow : z ≤
      (finiteNumericH L k M).kptOriginal family hAvoid v)
    (cut : Nat) (hZCross : cut < LevelTree.lev z)
    (hSeedMatch : KptRawOldSeedMatchAt
      family L k M hAvoid X v cut) :
    KptActualOldSocleCoveredAt family X top R z cut := by
  obtain ⟨u,x,hx,hXBelow,hXCross,_hVCross,hRaw⟩ :=
    hSeedMatch
  exact finiteNumericH_candidate_below_original_old_socle_of_seed_raw_type_eq
    family L k M hAvoid X top R u v x z
    hx hXBelow hZBelow cut hXCross hZCross hRaw

#print axioms Kk.finiteNumericH_candidate_below_original_old_socle_of_seed_raw_type_eq
#print axioms Kk.finiteNumericH_candidate_below_original_old_socle_of_raw_seed_match

end Kk
