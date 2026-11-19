import Kk.TrackEZeroColumnSocleCrossing
import Kk.TrackDPreCutStageSource
import Mathlib.Tactic

/-!
# Track E E74: full old Kpt socle coverage from TRUE stage-original prefixes

English-first proof and 20 adversarial checks:
docs/track_e_stage_original_old_socle_english_audit_20261119.md

The checked genuine stage representation sends every candidate new
source z to one physical stage original O_v with z <= O_v.
If every original v that ACTUALLY represents a NEW-LIVE crossing
has the SAME COMPLETE old Kpt ancestor as some OLD-LIVE source,
then the ENTIRE candidate meet/parameter closure has old full
Kpt socle coverage, with no new-run or source enumeration.

At zero ordinary-L cuts, combine this with E72's six-field full
L+/E next-column uniqueness to cover all new physical crossings.
The original prefix match remains a geometric application premise.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- An arbitrary-signature full Kpt source-socle lemma: testing
one COMPLETE old prefix per genuine active STAGE ORIGINAL suffices
to match the old prefix of EVERY candidate new-live crossing
meet/parameter source.

The representative original need not itself be a live source node.
We use actual Kpt LevelTree ancestors, not positive graph shadows.
The actual candidate closure uses the OLD AlgorithmRun's I(c+1). -/
theorem finiteNumericH_candidate_old_socle_of_active_original_prefixes
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid (U : Set (Fin N)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (cut : Nat)
    (hOriginalPrefix : ∀ (v : Fin N),
      v ∈ hStageOriginals K k N U (R.I (cut+1)) →
      (∃ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (R.I (cut+1)) Y ∧
        cut < LevelTree.lev z ∧
        z ≤ (finiteNumericH K k N).kptOriginal family hAvoid v) →
      ∃ w : AdmissibleKptNode family,
        w ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (R.I (cut+1)) X ∧
        ∃ (hV : cut < LevelTree.lev
          ((finiteNumericH K k N).kptOriginal family hAvoid v))
          (hW : cut < LevelTree.lev w),
          LevelTree.ancestor
            ((finiteNumericH K k N).kptOriginal family hAvoid v)
            cut (Nat.le_of_lt hV) =
          LevelTree.ancestor w cut (Nat.le_of_lt hW)) :
    ∀ (z : AdmissibleKptNode family),
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y →
      ∀ (hZCross : cut < LevelTree.lev z),
        ∃ w : AdmissibleKptNode family,
          w ∈ SMTree.Envelope.closure
            (admissibleKptSTree family) (R.I (cut+1)) X ∧
          ∃ (hWCross : cut < LevelTree.lev w),
            LevelTree.ancestor z cut (Nat.le_of_lt hZCross) =
            LevelTree.ancestor w cut (Nat.le_of_lt hWCross) := by
  intro z hZ hZCross
  obtain ⟨v,hStage,hBelow⟩ :=
    finiteNumericH_stage_closure_represented_by_stage_originals
      family K k N hAvoid U Y hY (R.I (cut+1)) z hZ
  obtain ⟨w,hW,hVCross,hWCross,hVPrefixEqW⟩ :=
    hOriginalPrefix v hStage ⟨z,hZ,hZCross,hBelow⟩
  have hZPrefixEqV :
      LevelTree.ancestor z cut (Nat.le_of_lt hZCross) =
      LevelTree.ancestor
        ((finiteNumericH K k N).kptOriginal family hAvoid v)
        cut (Nat.le_of_lt hVCross) := by
    exact LevelTree.eq_ancestor_of_le
      ((LevelTree.ancestor_le z cut
        (Nat.le_of_lt hZCross)).trans hBelow)
      (LevelTree.level_ancestor z cut (Nat.le_of_lt hZCross))
      (Nat.le_of_lt hVCross)
  exact ⟨w,hW,hWCross,hZPrefixEqV.trans hVPrefixEqW⟩

/-- At one actual ZERO ordinary-L stage, it is enough to check
the COMPLETE OLD Kpt ancestor of each ACTIVE REPRESENTING
original coordinate. The true new candidate Kpt closure is
possibly much larger, but all dependent old/upper L+/E
crossing pairs are physically covered in the old source.

This is source-exact, I2-fork safe, and does not assume a new
AlgorithmRun, auxiliary node enumeration or I1-terminal absence. -/
theorem finiteNumericH_candidate_zero_stage_original_prefixes_cover_full_crossings
    (family : List (NormalizedForbidden 1 0 1))
    (K : AgeTestModel 1 0 1) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hSym : ∀ i j : Nat,
      (finiteNumericH K k N).L.binary i j (0 : Fin 1) =
        (finiteNumericH K k N).L.binary j i (0 : Fin 1))
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid (U : Set (Fin N)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (cut : Nat)
    (hZeroStage : ∀ v : Fin N,
      v ∈ hStageOriginals K k N U (R.I (cut+1)) →
      cut+1 ≤ (finiteNumericH K k N).freeLevel v.val →
      (finiteNumericH K k N).L.binary
        cut v.val (0 : Fin 1) = false)
    (hOriginalPrefix : ∀ (v : Fin N),
      v ∈ hStageOriginals K k N U (R.I (cut+1)) →
      (∃ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (R.I (cut+1)) Y ∧
        cut < LevelTree.lev z ∧
        z ≤ (finiteNumericH K k N).kptOriginal family hAvoid v) →
      ∃ w : AdmissibleKptNode family,
        w ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (R.I (cut+1)) X ∧
        ∃ (hV : cut < LevelTree.lev
          ((finiteNumericH K k N).kptOriginal family hAvoid v))
          (hW : cut < LevelTree.lev w),
          LevelTree.ancestor
            ((finiteNumericH K k N).kptOriginal family hAvoid v)
            cut (Nat.le_of_lt hV) =
          LevelTree.ancestor w cut (Nat.le_of_lt hW)) :
    FullPhysicalClosureCrossing family
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1)) Y) cut ⊆
    FullPhysicalClosureCrossing family
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1)) X) cut := by
  apply finiteNumericH_candidate_zero_stage_old_socle_covers_full_crossings
    family K k N hAvoid hSym U X Y hXY hY top R cut hZeroStage
  exact finiteNumericH_candidate_old_socle_of_active_original_prefixes
    family K k N hAvoid U X Y hY top R cut hOriginalPrefix

end Kk
