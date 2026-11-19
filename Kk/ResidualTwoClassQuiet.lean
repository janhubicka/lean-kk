import Kk.TrackENumericResidualTwoClass

/-!
Track C: exact separation of full residual Kpt source quietness into
NEW FINAL and EARLY OLD-FINAL source names, including SAME-NODE
complete dependent old/upper L+/E crossing pairs.

English-first audit:
 docs/track_c_residual_two_class_quiet_english_audit.md

This is a criterion, NOT a proof of either geometric quietness class.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Full dependent Kpt residual quietness restricted to a specified
class of new source indices. Both I1 terminals and complete
old/upper L+/E crossing-pair coverage are required. -/
def KptResidualClassQuiet
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool)
    (cut : Nat)
    (isClass : Fin Q → Prop) : Prop :=
  (∀ j : Fin Q, newLive cut j = true → isClass j →
    LevelTree.lev (newNode j) ≠ cut) ∧
  (∀ j : Fin Q, newLive cut j = true → isClass j →
    ∀ T : PartialTypeWithE cut db du dd,
    ∀ U : PartialTypeWithE (cut+1) db du dd,
      kptFullOldAtCut (newNode j) cut =
        some (⟨cut,T⟩ : RawPartialTypeNode db du dd) →
      kptFullUpperAtCut (newNode j) cut =
        some (⟨cut+1,U⟩ : RawPartialTypeNode db du dd) →
      (T,U) ∈ IndexedPhysicalCrossing family oldNode oldLive cut)

/-- Track C's missing physical-source check splits exactly into
two geometrically separate classes, with the complete Kpt old/upper
L+/E record retained in BOTH classes.

Injectivity is necessary for the E65 reverse residual classification.
Neither class is asserted quiet by this theorem. -/
theorem kpt_residual_quiet_iff_two_classes
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool)
    (φ : Fin P → Fin Q)
    (hInj : Function.Injective φ)
    (cut : Nat) :
    KptResidualQuietAtBoringCut family
      oldNode newNode oldLive newLive φ cut ↔
    (KptResidualClassQuiet family oldNode newNode
      oldLive newLive cut (KptNewFinalName φ) ∧
     KptResidualClassQuiet family oldNode newNode
      oldLive newLive cut
      (KptEarlyOldFinalName φ oldLive cut)) := by
  constructor
  · intro h
    constructor
    · constructor
      · intro j hj hClass
        exact h.1 j hj
          ((kpt_residual_iff_new_final_or_early_old
            φ hInj oldLive cut j).2 (Or.inl hClass))
      · intro j hj hClass T U hOld hUpper
        exact h.2 j hj
          ((kpt_residual_iff_new_final_or_early_old
            φ hInj oldLive cut j).2 (Or.inl hClass))
          T U hOld hUpper
    · constructor
      · intro j hj hClass
        exact h.1 j hj
          ((kpt_residual_iff_new_final_or_early_old
            φ hInj oldLive cut j).2 (Or.inr hClass))
      · intro j hj hClass T U hOld hUpper
        exact h.2 j hj
          ((kpt_residual_iff_new_final_or_early_old
            φ hInj oldLive cut j).2 (Or.inr hClass))
          T U hOld hUpper
  · rintro ⟨hFresh,hEarly⟩
    constructor
    · intro j hj hResidual
      rcases (kpt_residual_iff_new_final_or_early_old
        φ hInj oldLive cut j).1 hResidual with hNew | hOld
      · exact hFresh.1 j hj hNew
      · exact hEarly.1 j hj hOld
    · intro j hj hResidual T U hOld hUpper
      rcases (kpt_residual_iff_new_final_or_early_old
        φ hInj oldLive cut j).1 hResidual with hNew | hOldName
      · exact hFresh.2 j hj hNew T U hOld hUpper
      · exact hEarly.2 j hj hOldName T U hOld hUpper

end Kk

#check @Kk.kpt_residual_quiet_iff_two_classes
#print axioms Kk.kpt_residual_quiet_iff_two_classes
