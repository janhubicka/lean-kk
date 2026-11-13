import Kk.B3ActualI3ExtraUpper
import SuccessorTree.V10.I3AlgorithmRunPool
import Mathlib.Tactic

/-!
# Track B: remove assumed finite-closure pool for actual numerical H

English-first mathematical derivation and adversarial audit:
  docs/track_b_numeric_run_extra_upper_english_audit.md

The true finite numerical-H AlgorithmRun closure is represented by
the maintained finite original set U union positive selected original
addresses, rather than an independently postulated finite name pool.

At a nonstructural interesting selected cut whose marked B3 passes,
some genuine closure-selected original in that maintained pool has a
complete upper L-reduct missing from the marked selected profile.

No full resolved diary, common labelled inverse orbit, or exact big
Ramsey degree formula is inferred.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Finite numerical-H specialization of the actual AlgorithmRun
extra-upper-original diagnostic. The fixed representing original-name
pool is BUILT from the run itself and its closure invariant, not
postulated. Source membership is tested at R.I (cut+1), while the
maintained original-name carrier uses final R.I 0.

The marked predicate has an actual eligible name, and its B3
admissibility is a separate hypothesis; it cannot be replaced by
selected-front graph-age invariance alone. -/
theorem numericH_algorithmRun_nonstructural_I3_has_extra_upper_original
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
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = top)
    (cut : Nat) (hPositive : 0 < cut)
    (hBelow : cut < top) (hCut : cut < N)
    (hSelected : cut ∈ R.I 0)
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X ∧
      LevelTree.lev z = cut)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode family,
      a ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X ∧
      ∃ b : AdmissibleKptNode family,
        b ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) X ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :
    let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
    let hAvoidA := finiteNumericH_avoids_family
      family K hCarrier k N hAvoidK
    let V : Finset (Fin N) := hStageOriginals K k N U (R.I 0)
    let original : Fin V.card → Fin A.size :=
      fun j => (V.equivFin.symm j).1
    ∀ (Marked : Fin V.card → Prop)
      (w : Fin V.card) (hw : Marked w)
      (hwCut : cut+1 ≤ A.freeLevel (original w).val)
      (hMarked :
        (selectedStagePoolPrescribedData A cut original Marked).CorrectedB3
          family),
      ∃ v : Fin V.card,
        closureSelectedOriginal family A hAvoidA original
          (SMTree.Envelope.closure
            (admissibleKptSTree family) (R.I (cut+1)) X) cut v ∧
        cut+1 ≤ A.freeLevel (original v).val ∧
        ¬ (selectedStagePoolPrescribedData A cut original Marked).PrescribedUpperLType
          ((A.partialTypeAt (cut+1) (original v).val).lReduct) := by
  classical
  intro Marked w hw hwCut hMarked
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  let hAvoidA := finiteNumericH_avoids_family
    family K hCarrier k N hAvoidK
  let V : Finset (Fin N) := hStageOriginals K k N U (R.I 0)
  let original : Fin V.card → Fin A.size :=
    fun j => (V.equivFin.symm j).1
  have hSurj : ∀ v : Fin N, v ∈ V →
      ∃ j : Fin V.card, original j = v := by
    intro v hv
    refine ⟨V.equivFin ⟨v,hv⟩,?_⟩
    simp [original]
  have hPool : ∀ z, z ∈ SMTree.Envelope.closure
      (admissibleKptSTree family) (R.I (cut+1)) X →
      ∃ j : Fin V.card,
        z ≤ A.kptOriginal family hAvoidA (original j) := by
    intro z hz
    obtain ⟨v,hv,hzv⟩ :=
      numericH_algorithmRun_closure_original_in_final_pool
        family K hCarrier hAvoidK k N U X hX top cut hBelow R z hz
    obtain ⟨j,hj⟩ := hSurj v hv
    refine ⟨j,?_⟩
    simpa [A, ←hj] using hzv
  exact algorithmRun_nonstructural_I3_has_extra_upper_original
    family A hAvoidA original X top R hTopSeed cut
    hPositive hBelow hCut hSelected hPool hNoI1 hNoI2
    Marked w hw hwCut hMarked

#print axioms numericH_algorithmRun_nonstructural_I3_has_extra_upper_original

end Kk
