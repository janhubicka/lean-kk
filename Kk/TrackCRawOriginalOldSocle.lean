import Kk.TrackEOldSocleOriginalMaxFrontier
import Kk.TrackEZeroColumnSocleCrossing
import Mathlib.Tactic

/-!
# Track C: concrete complete numerical H+ old partial types certify OLD Kpt socles

English first, adversarially audited (20 hostile checks):
 docs/track_c_raw_original_old_socle_audit_20261121.md

An actual old initial Kpt seed x<=O_u crossing cut c and a DIFFERENT
physical original O_v crossing c have the SAME complete OLD Kpt
ancestor whenever the actual concrete numerical-H+ raw records
A.partialTypeAt(c,u)=A.partialTypeAt(c,v) match. This includes EVERY
directed auxiliary E, ordinary L negative atom, unary/diagonal and
distinguished type-vertex field, not graph-age shadow matching.

The old seed itself witnesses the actual pre-cut Kpt closure source.
This reduces E79 maximal old-prefix certification to a finite RAW
numerical original-pair comparison (if a suitable old seed exists).
It does NOT derive those raw type equalities from resolved-Q class
adjacency, nor establish any global diary/inverse monoid orbit.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Two actual physical originals of ONE numerical-H+ ambient
with identical COMPLETE OLD dependent `partialTypeAt cut`
records can share an OLD Kpt source witness even when the
literal old seed x lies only below O_u, not O_v.

The old seed x and target original O_v must both STRICTLY cross
cut. The old source witness is literally x, in the seed set X.
-/
theorem kpt_original_old_socle_covered_of_seed_raw_type_eq
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (u v : Fin M)
    (x : AdmissibleKptNode family)
    (hx : x ∈ X)
    (hBelow : x ≤
      (finiteNumericH L k M).kptOriginal family hAvoid u)
    (cut : Nat)
    (hXCross : cut < LevelTree.lev x)
    (hVCross : cut < LevelTree.lev
      ((finiteNumericH L k M).kptOriginal family hAvoid v))
    (hOldRawEq :
      (finiteNumericH L k M).partialTypeAt cut u.val =
        (finiteNumericH L k M).partialTypeAt cut v.val) :
    KptActualOldSocleCoveredAt family X top Rold
      ((finiteNumericH L k M).kptOriginal family hAvoid v) cut := by
  let A : EnumeratedPartialStructure db du dd := finiteNumericH L k M
  let O_v : AdmissibleKptNode family :=
    A.kptOriginal family hAvoid v
  have hXRaw :
      (LevelTree.ancestor x cut (Nat.le_of_lt hXCross)).val =
        (⟨cut, A.partialTypeAt cut u.val⟩ :
          RawPartialTypeNode db du dd) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid u x hBelow cut (Nat.le_of_lt hXCross)
  have hVRaw :
      (LevelTree.ancestor O_v cut (Nat.le_of_lt hVCross)).val =
        (⟨cut, A.partialTypeAt cut v.val⟩ :
          RawPartialTypeNode db du dd) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid v O_v le_rfl cut (Nat.le_of_lt hVCross)
  have hAnc :
      LevelTree.ancestor O_v cut (Nat.le_of_lt hVCross) =
        LevelTree.ancestor x cut (Nat.le_of_lt hXCross) := by
    apply Subtype.ext
    calc
      (LevelTree.ancestor O_v cut (Nat.le_of_lt hVCross)).val =
          (⟨cut, A.partialTypeAt cut v.val⟩ :
            RawPartialTypeNode db du dd) := hVRaw
      _ = (⟨cut, A.partialTypeAt cut u.val⟩ :
            RawPartialTypeNode db du dd) := by rw [← hOldRawEq]
      _ = (LevelTree.ancestor x cut (Nat.le_of_lt hXCross)).val :=
        hXRaw.symm
  refine ⟨x, ?_, hVCross, hXCross, hAnc⟩
  exact (SMTree.Envelope.subset_closure
    (admissibleKptSTree family) (Rold.I (cut+1)) X) hx

/-- The EXACT maximal old-prefix test of E79 for genuine original
v follows from ONE old genuine seed x<=O_u above that maximal
eligible cut and equality of the two physical originals'
complete OLD `partialTypeAt` records AT the maximum.

There is no claim that the resolved diary provides x or this
literal full raw type equality; these are now finite original-
coordinate geometric tests rather than abstract source matches. -/
theorem kpt_original_max_old_socle_of_seed_raw_type_eq
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (W : Finset (Fin M))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (Allowed : Set Nat)
    (u v : Fin M)
    (x : AdmissibleKptNode family)
    (hx : x ∈ X)
    (hBelow : x ≤
      (finiteNumericH L k M).kptOriginal family hAvoid u)
    (hNonempty :
      (kpt_actual_original_socle_allowed_cuts
        family L k M hAvoid W X Y top Rold Allowed v).Nonempty)
    (hXCross :
      (kpt_actual_original_socle_allowed_cuts
        family L k M hAvoid W X Y top Rold Allowed v).max' hNonempty <
        LevelTree.lev x)
    (hVCross :
      (kpt_actual_original_socle_allowed_cuts
        family L k M hAvoid W X Y top Rold Allowed v).max' hNonempty <
        LevelTree.lev
          ((finiteNumericH L k M).kptOriginal family hAvoid v))
    (hOldRawEq :
      (finiteNumericH L k M).partialTypeAt
        ((kpt_actual_original_socle_allowed_cuts
          family L k M hAvoid W X Y top Rold Allowed v).max' hNonempty)
        u.val =
      (finiteNumericH L k M).partialTypeAt
        ((kpt_actual_original_socle_allowed_cuts
          family L k M hAvoid W X Y top Rold Allowed v).max' hNonempty)
        v.val) :
    KptActualOldSocleCoveredAt family X top Rold
      ((finiteNumericH L k M).kptOriginal family hAvoid v)
      ((kpt_actual_original_socle_allowed_cuts
        family L k M hAvoid W X Y top Rold Allowed v).max' hNonempty) :=
  kpt_original_old_socle_covered_of_seed_raw_type_eq
    family L k M hAvoid X top Rold u v x hx hBelow
    _ hXCross hVCross hOldRawEq

end Kk

#check @Kk.kpt_original_old_socle_covered_of_seed_raw_type_eq
#print axioms Kk.kpt_original_old_socle_covered_of_seed_raw_type_eq
#check @Kk.kpt_original_max_old_socle_of_seed_raw_type_eq
#print axioms Kk.kpt_original_max_old_socle_of_seed_raw_type_eq
