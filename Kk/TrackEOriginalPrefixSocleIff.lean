import Kk.TrackEOriginalPrefixSocleCover
import Mathlib.Tactic

/-!
# Track E E78: exact equivalence of actual Kpt OLD socle coverage
# and active genuine numerical-H+ stage-original prefix matching

English-first adversarial proof and 20 hostile checks:
docs/track_e_exact_original_prefix_socle_iff_english_audit_20261120.md

E74's original English audit incorrectly treated its active-original
criterion as merely a potentially STRONGER sufficient certificate.
For each genuinely ACTIVE v, the full Kpt ancestor of any crossing
new-source z below O_v equals the ancestor of O_v. Thus any
OLD-LIVE socle witness of z also witnesses v. Conversely E74's
verified actual stage representation yields a representative v
for each new-source crossing and transports its old witness back.

Hence the finite original-coordinate test is EXACTLY equivalent
to complete candidate-source OLD-socle coverage. This is NOT a
claim that either predicate actually holds in the resolved diary.
It does NOT automatically give upper-type matching without E72's
whole-stage zero ordinary-L hypothesis.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Actual finite numerical-H+ source-exact equivalence between:

  (A) EVERY candidate new-live Kpt crossing source has an
      OLD-LIVE Kpt witness with the SAME COMPLETE old ancestor;

  (B) EVERY genuinely ACTIVE stage original v (i.e. one representing
      SOME new-live crossing source z ≤ O_v) has an OLD-LIVE witness
      for the SAME COMPLETE original's old ancestor.

A stage original not representing any crossing source has no test.
No new AlgorithmRun on Y, source-index bijection, selected shadow
or I2 functionality is involved. The reverse B→A uses exact
genuine stage-original representation from E74; A→B follows
directly from LevelTree ancestor uniqueness for z≤O_v.

This corrects E74's mistaken "not necessary" audit caveat.
It is an iff for OLD-SOCLE coverage, not a general iff for
the complete old/upper crossing relation without zero columns. -/
theorem finiteNumericH_candidate_old_socle_iff_active_original_prefixes
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
    (cut : Nat) :
    (∀ (z : AdmissibleKptNode family),
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y →
      ∀ (hZCross : cut < LevelTree.lev z),
        ∃ w : AdmissibleKptNode family,
          w ∈ SMTree.Envelope.closure
            (admissibleKptSTree family) (R.I (cut+1)) X ∧
          ∃ (hWCross : cut < LevelTree.lev w),
            LevelTree.ancestor z cut (Nat.le_of_lt hZCross) =
            LevelTree.ancestor w cut (Nat.le_of_lt hWCross)) ↔
    (∀ (v : Fin N),
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
          LevelTree.ancestor w cut (Nat.le_of_lt hW)) := by
  constructor
  · intro hSocle v _hStage ⟨z,hZ,hZCross,hBelow⟩
    obtain ⟨w,hW,hWCross,hZW⟩ := hSocle z hZ hZCross
    have hOCross :
        cut < LevelTree.lev
          ((finiteNumericH K k N).kptOriginal family hAvoid v) :=
      lt_of_lt_of_le hZCross (LevelTree.level_le_of_le hBelow)
    have hZOriginal :
        LevelTree.ancestor z cut (Nat.le_of_lt hZCross) =
        LevelTree.ancestor
          ((finiteNumericH K k N).kptOriginal family hAvoid v)
          cut (Nat.le_of_lt hOCross) := by
      exact LevelTree.eq_ancestor_of_le
        ((LevelTree.ancestor_le z cut
          (Nat.le_of_lt hZCross)).trans hBelow)
        (LevelTree.level_ancestor z cut (Nat.le_of_lt hZCross))
        (Nat.le_of_lt hOCross)
    exact ⟨w,hW,hOCross,hWCross,hZOriginal.symm.trans hZW⟩
  · intro hOriginal
    exact finiteNumericH_candidate_old_socle_of_active_original_prefixes
      family K k N hAvoid U X Y hY top R cut hOriginal

end Kk
