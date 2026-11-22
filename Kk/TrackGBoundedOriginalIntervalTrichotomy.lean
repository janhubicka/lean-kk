import Kk.TrackGOriginalSocleNoveltyCarriers
import Kk.NumericPrefixGapZero
import Mathlib.Tactic

/-!
# Track G: exact Bad cut structural trichotomy with bounded
# ORIGINAL-coordinate order-convex missing-socle interval carriers.

English proof and fifteen adversarial checks were committed FIRST:
docs/track_g_bounded_original_interval_trichotomy_english_audit_20261122.md

At any true finite numerical-H+ graph ZERO ordinary-L stage,
an exact total-factor Bad cut has either a complete candidate
I1 terminal, an actual I2 same-component meet, or a live
original coordinate whose complete OLD Kpt lower-socle
novelty is witnessed at the SAME cut. The E85 support has
cardinality ≤ |U| + |actually old selected levels|; each
original novelty cut set is order-convex by verified G487.

At an ODD numerical-H+ raw cut the zero-L premise holds
automatically by the genuine numerical left-zero identity.
Auxiliary dependent E is never symmetrized or forgotten.

NO bound is claimed on the number/connected components of
actual Bad cuts inside these original interval carriers,
nor on |I_old(0)| uniformly in an abstract resolved diary.
No common labelled inverse-source orbit or BRD claimed.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

/-- One TRUE zero ordinary-L finite numerical-H+ exact factor
Bad cut has genuine I1, genuine same-component I2, or one
ACTIVE, genuinely candidate-new ORIGINAL-coordinate interval
carrier with no complete old dependent L+/E socle match.

The same fixed original-test support contains all such carrier
choices and has at most |U|+|selected old levels| members.

The novelty set for each fixed v is RAW order-convex (G487).
Intersecting with zero-column/old-boring/Allowed cuts need NOT
remain convex; do not infer a bound on Bad-cut cardinality. -/
theorem finiteNumericH_zero_stage_exact_Bad_structural_or_original_interval
    (family : List (NormalizedForbidden 1 0 1))
    (K : AgeTestModel 1 0 1) (k N Q : Nat)
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
    (node : Fin Q → AdmissibleKptNode family)
    (live : Nat → Fin Q → Bool)
    (Allowed : Set Nat)
    (cut : Nat) (hAllowed : cut ∈ Allowed)
    (hExactY : ∀ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y ↔
      ∃ j : Fin Q, node j = z ∧ live cut j = true)
    (hZeroStage : ∀ v : Fin N,
      v ∈ hStageOriginals K k N U (R.I (cut+1)) →
      cut+1 ≤ (finiteNumericH K k N).freeLevel v.val →
      (finiteNumericH K k N).L.binary
        cut v.val (0 : Fin 1) = false)
    (hBad : cut ∈ kptExactOldFactorBadCuts
      family X top R node live) :
    ((∃ z : AdmissibleKptNode family,
       z ∈ SMTree.Envelope.closure
         (admissibleKptSTree family) (R.I (cut+1)) Y ∧
       LevelTree.lev z = cut) ∨
     (∃ z : AdmissibleKptNode family,
       z ∈ SMTree.Envelope.closure
         (admissibleKptSTree family) (R.I (cut+1)) Y ∧
       ∃ w : AdmissibleKptNode family,
         w ∈ SMTree.Envelope.closure
           (admissibleKptSTree family) (R.I (cut+1)) Y ∧
         SMTree.Envelope.SameComponent z w ∧
         LevelTree.lev (LevelTree.meet z w) = cut) ∨
     (∃ v : Fin N,
       v ∈ kpt_originals_needing_max_old_socle_test
         family K k N hAvoid U X Y top R Allowed ∧
       KptOriginalSocleNovelAt
         family K k N hAvoid U X Y top R v cut)) ∧
     (kpt_originals_needing_max_old_socle_test
       family K k N hAvoid U X Y top R Allowed).card ≤
       U.card +
       (kpt_old_actual_selected_levels family X top R).card := by
  classical
  have hBound :=
    kpt_originals_needing_max_old_socle_test_card_le_root_add_selected
      family K k N hAvoid U X Y top R Allowed
  refine ⟨?_,hBound⟩
  by_cases hI1 : ∃ z : AdmissibleKptNode family,
       z ∈ SMTree.Envelope.closure
         (admissibleKptSTree family) (R.I (cut+1)) Y ∧
       LevelTree.lev z = cut
  · exact Or.inl hI1
  · by_cases hI2 : ∃ z : AdmissibleKptNode family,
       z ∈ SMTree.Envelope.closure
         (admissibleKptSTree family) (R.I (cut+1)) Y ∧
       ∃ w : AdmissibleKptNode family,
         w ∈ SMTree.Envelope.closure
           (admissibleKptSTree family) (R.I (cut+1)) Y ∧
         SMTree.Envelope.SameComponent z w ∧
         LevelTree.lev (LevelTree.meet z w) = cut
    · exact Or.inr (Or.inl hI2)
    · have hOrig :=
        finiteNumericH_zero_stage_exact_Bad_has_active_original_novel_carrier
          family K k N Q hAvoid hSym U X Y hXY hY top
          R node live Allowed cut hAllowed hExactY
          hZeroStage hI1 hI2 hBad
      exact Or.inr (Or.inr hOrig.1)

/-- At a TRUE odd numerical-H+ raw source cut c=2a+1
the complete zero ordinary-L column for every physical
stage-original is automatic. The same full structural I1/I2
or bounded ORIGINAL-socle interval trichotomy therefore holds
without a separately assumed zero-column condition.

Oddness does NOT remove auxiliary E, terminals or I2 meets. -/
theorem finiteNumericH_odd_exact_Bad_structural_or_original_interval
    (family : List (NormalizedForbidden 1 0 1))
    (K : AgeTestModel 1 0 1) (k N Q : Nat)
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
    (node : Fin Q → AdmissibleKptNode family)
    (live : Nat → Fin Q → Bool)
    (Allowed : Set Nat)
    (a : Nat) (hAllowed : (2*a+1) ∈ Allowed)
    (hExactY : ∀ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I ((2*a+1)+1)) Y ↔
      ∃ j : Fin Q, node j = z ∧ live (2*a+1) j = true)
    (hBad : (2*a+1) ∈ kptExactOldFactorBadCuts
      family X top R node live) :
    ((∃ z : AdmissibleKptNode family,
       z ∈ SMTree.Envelope.closure
         (admissibleKptSTree family) (R.I ((2*a+1)+1)) Y ∧
       LevelTree.lev z = (2*a+1)) ∨
     (∃ z : AdmissibleKptNode family,
       z ∈ SMTree.Envelope.closure
         (admissibleKptSTree family) (R.I ((2*a+1)+1)) Y ∧
       ∃ w : AdmissibleKptNode family,
         w ∈ SMTree.Envelope.closure
           (admissibleKptSTree family) (R.I ((2*a+1)+1)) Y ∧
         SMTree.Envelope.SameComponent z w ∧
         LevelTree.lev (LevelTree.meet z w) = (2*a+1)) ∨
     (∃ v : Fin N,
       v ∈ kpt_originals_needing_max_old_socle_test
         family K k N hAvoid U X Y top R Allowed ∧
       KptOriginalSocleNovelAt
         family K k N hAvoid U X Y top R v (2*a+1))) ∧
     (kpt_originals_needing_max_old_socle_test
       family K k N hAvoid U X Y top R Allowed).card ≤
       U.card +
       (kpt_old_actual_selected_levels family X top R).card := by
  have hZeroStage : ∀ v : Fin N,
      v ∈ hStageOriginals K k N U (R.I ((2*a+1)+1)) →
      (2*a+1)+1 ≤ (finiteNumericH K k N).freeLevel v.val →
      (finiteNumericH K k N).L.binary
        (2*a+1) v.val (0 : Fin 1) = false := by
    intro v _ _
    change hNumericBinary K.binary k (2*a+1) v.val
      (0 : Fin 1) = false
    exact hNumericBinary_odd_left_false
      K.binary k a v.val (0 : Fin 1)
  exact finiteNumericH_zero_stage_exact_Bad_structural_or_original_interval
    family K k N Q hAvoid hSym U X Y hXY hY top R
    node live Allowed (2*a+1) hAllowed hExactY hZeroStage hBad

end Kk
