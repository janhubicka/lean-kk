import Kk.B3OneGapInteresting
import SuccessorTree.EnvelopeRun
import SuccessorTree.V10.ConcreteOriginalPool
import SuccessorTree.V10.M2BoundaryTypedRecords
import Mathlib.Tactic

/-!
# An actual failed one-upper B3 age test forces AlgorithmRun selection

The one-gap necessity theorem shows that if a closure contains the
complete Kpt original of an ambient vertex v, and the finite L-only
age test for its next L-type at cut m fails, the level is
IsInterestingAt by the actual third (I3) clause.

This module supplies the missing run-level conclusion:
it identifies the ancestor's whole dependent Kpt record with the
literal ambient partialTypeAt(m+1,v), includes the original seed
in the actual stage closure, and uses the run's genuinely
verified interesting_step to conclude m ∈ R.I(m).

The theorem is generic for any forbidden family and actual finite
enumerated partial structure, not restricted to K4. It does not
postulate an independent source-signature injection, type shadow
projection, or equal diary orbit.

A later numerical-H application can discharge its sole age-test
hypothesis via the exact 25-vertex K4 continuation at cut 22.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Every genuine failed one-upper-type corrected B3 test from
a seed original at cut m obliges the actual Algorithm 5.4 run
to select level m. All source/target types are the ACTUAL extracted
L+ types of A, not abstract prescribed substitutes. -/
theorem algorithmRun_selects_actual_failed_single_upper_B3
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (v : Fin A.size)
    (m : Nat) (hmPos : 0 < m) (hmFree : m < A.freeLevel v.val)
    (hFailed :
      ¬ CommonSocleAgeTest family
        (prescribedOrdinarySocle (A.partialTypeAt (m+1) v.val)) m
        (fun T => T = (A.partialTypeAt (m+1) v.val).lReduct))
    (X : Set (AdmissibleKptNode family))
    (hSeed : A.kptOriginal family hAvoid v ∈ X)
    (ell : Nat) (hmEll : m < ell)
    (R : SuccessorTree.SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X ell) :
    m ∈ R.I m := by
  classical
  let z : AdmissibleKptNode family :=
    A.kptOriginal family hAvoid v
  have hzm : m < LevelTree.lev z := by
    change m < A.freeLevel v.val
    exact hmFree
  let b : AdmissibleKptNode family :=
    LevelTree.ancestor z (m+1) (Nat.succ_le_iff.mpr hzm)
  have hb : LevelTree.lev b = m+1 :=
    LevelTree.level_ancestor z (m+1) (Nat.succ_le_iff.mpr hzm)
  have hbelow : b ≤ z :=
    LevelTree.ancestor_le z (m+1) (Nat.succ_le_iff.mpr hzm)
  have hRaw : b.val =
      (⟨m+1,A.partialTypeAt (m+1) v.val⟩ :
        RawPartialTypeNode db du dd) := by
    have h := kpt_prefix_raw_eq_ambient A family hAvoid v b hbelow
    simpa only [hb] using h
  have hRecord :
      kptRecordAtLevel (m+1) b hb =
        A.partialTypeAt (m+1) v.val := by
    have hTyped : b.val =
        (⟨m+1,kptRecordAtLevel (m+1) b hb⟩ :
          RawPartialTypeNode db du dd) :=
      kptRecordAtLevel_raw (m+1) b hb
    have hEqual :
        (⟨m+1,kptRecordAtLevel (m+1) b hb⟩ :
          RawPartialTypeNode db du dd) =
        (⟨m+1,A.partialTypeAt (m+1) v.val⟩ :
          RawPartialTypeNode db du dd) :=
      hTyped.symm.trans hRaw
    exact eq_of_heq (Sigma.mk.inj_iff.mp hEqual).2
  have hFailedB :
      ¬ CommonSocleAgeTest family
        (prescribedOrdinarySocle (kptRecordAtLevel (m+1) b hb)) m
        (fun T => T = (kptRecordAtLevel (m+1) b hb).lReduct) := by
    rw [hRecord]
    exact hFailed
  have hzClosure :
      z ∈ SuccessorTree.SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (m+1)) X :=
    (SuccessorTree.SMTree.Envelope.subset_closure
      (admissibleKptSTree family) (R.I (m+1)) X) hSeed
  have hInteresting :
      SuccessorTree.SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family)
        (SuccessorTree.SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (m+1)) X) m :=
    bad_single_upper_forces_actual_interesting
      family
      (SuccessorTree.SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (m+1)) X)
      z hzClosure m hmPos hzm hFailedB
  have hSelected := (R.interesting_step m hmEll hInteresting).1
  rw [hSelected]
  simp

end Kk
