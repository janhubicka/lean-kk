import Kk.TrackEUsedRecipeEventReconstruction
import Kk.PrefixCutRigidity
import Mathlib.Tactic

/-!
# Track E E58: common source top and source cuts recover a labelled event record

This substitutes one genuine common finite G+ source top and each selected
label's SOURCE code length for the older global inverse-image-set equality
premise. The verified prefix-reflection theorem gives labelled selected
G+ source equality; used dependent-Kpt recipes and full event-local
presence/old/upper-L+ recovery remain conditional exactly as in E56.

English-first proof: docs/track_e_common_top_cut_used_recipe_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- Exact conditional E58 reconstruction:
 * labelled selected G+ sources coincide by the verified genuine
   common-source-top, target-prefix and selected SOURCE-cut theorem;
 * dependent parameters coincide by USED closure recipes only;
 * full synchronized event frames, presence, assigned old and upper
   dependent L+ types are recovered by the SAME physical functions
   on event frames and the actual named source nodes.

No cross-occurrence diary-invariant source top, source cut schedule,
full event recovery or monoid transport is constructed here.
The statement remains conditional on all geometric premises.
Genuine meet witnesses must be SameComponent compatible in BOTH
presentations; the corresponding WellFormed conditions are
requirements of the proposed physical application. -/
theorem full_event_source_eq_of_common_top_cuts_and_used_recipes
    {n : Nat} {Parameters Old Upper Events Kind Character : Type}
    {Seeds Positives Originals : Type}
    (F G : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (R S : KptEventIndexedSourceRecord family n
      Parameters Old Upper Events Kind Character)
    (sourceTop targetTopF targetTopG : FiniteGPlusVertex family)
    (targetF targetG : Fin n → FiniteGPlusVertex family)
    (hTopF : gPlusShapeImage F.map sourceTop = targetTopF)
    (hTopG : gPlusShapeImage G.map sourceTop = targetTopG)
    (hSelectedF : ∀ a,
      gPlusShapeImage F.map (R.selected a) = targetF a)
    (hSelectedG : ∀ a,
      gPlusShapeImage G.map (S.selected a) = targetG a)
    (hTargetPrefF : ∀ a, (targetF a).val.IsPrefix targetTopF.val)
    (hTargetPrefG : ∀ a, (targetG a).val.IsPrefix targetTopG.val)
    (hSourceCuts : ∀ a,
      (R.selected a).val.size = (S.selected a).val.size)
    (atomsF atomsG :
      KptSourceAtomAssignment family Seeds Positives Originals)
    (recipes : Parameters → KptClosureRecipe Seeds Positives Originals)
    (hRecipeF : ∀ p,
      R.parameters p = (recipes p).evaluate atomsF)
    (hRecipeG : ∀ p,
      S.parameters p = (recipes p).evaluate atomsG)
    (hSeed : ∀ p s,
      recipes p = .seed s → atomsF.seed s = atomsG.seed s)
    (hPositive : ∀ p q,
      recipes p = .positive q →
        atomsF.positiveParameter q = atomsG.positiveParameter q)
    (hMeet : ∀ p u v,
      recipes p = .meetOf u v →
        LevelTree.meet
          (atomsF.ambientOriginal u) (atomsF.ambientOriginal v) =
        LevelTree.meet
          (atomsG.ambientOriginal u) (atomsG.ambientOriginal v))
    (hWellFormedF : ∀ p, (recipes p).WellFormed atomsF)
    (hWellFormedG : ∀ p, (recipes p).WellFormed atomsG)
    (hFrames : R.eventFrame = S.eventFrame)
    (recoverPresent : Events →
      FullSourceEventFrame (Fin n) Parameters Kind Character →
      Sum (FiniteGPlusVertex family)
        (AdmissibleKptNode family) → Bool)
    (recoverOld : Events →
      FullSourceEventFrame (Fin n) Parameters Kind Character →
      Sum (FiniteGPlusVertex family)
        (AdmissibleKptNode family) → Old)
    (recoverUpper : Events →
      FullSourceEventFrame (Fin n) Parameters Kind Character →
      Sum (FiniteGPlusVertex family)
        (AdmissibleKptNode family) → Upper)
    (hPresentR : ∀ j x,
      R.presentAt j x =
        recoverPresent j (R.eventFrame j) (R.namedNode x))
    (hPresentS : ∀ j x,
      S.presentAt j x =
        recoverPresent j (S.eventFrame j) (S.namedNode x))
    (hOldR : ∀ j x,
      R.oldAt j x = recoverOld j (R.eventFrame j) (R.namedNode x))
    (hOldS : ∀ j x,
      S.oldAt j x = recoverOld j (S.eventFrame j) (S.namedNode x))
    (hUpperR : ∀ j x,
      R.upperAt j x = recoverUpper j (R.eventFrame j) (R.namedNode x))
    (hUpperS : ∀ j x,
      S.upperAt j x = recoverUpper j (S.eventFrame j) (S.namedNode x)) :
    R = S := by
  have hSelected : R.selected = S.selected :=
    labelled_sources_eq_of_common_top_and_cuts
      F G sourceTop targetTopF targetTopG
      targetF targetG R.selected S.selected
      hTopF hTopG hSelectedF hSelectedG
      hTargetPrefF hTargetPrefG hSourceCuts
  have hParameters : R.parameters = S.parameters :=
    kpt_used_recipes_identify_parameter_nodes
      R S atomsF atomsG recipes hRecipeF hRecipeG
      hSeed hPositive hMeet
  have hNames : R.namedNode = S.namedNode := by
    funext x
    cases x with
    | inl a =>
      change Sum.inl (R.selected a) = Sum.inl (S.selected a)
      exact congrArg Sum.inl (congrFun hSelected a)
    | inr p =>
      change Sum.inr (R.parameters p) = Sum.inr (S.parameters p)
      exact congrArg Sum.inr (congrFun hParameters p)
  have hPresent : R.presentAt = S.presentAt := by
    funext j x
    calc
      R.presentAt j x =
          recoverPresent j (R.eventFrame j) (R.namedNode x) :=
        hPresentR j x
      _ = recoverPresent j (S.eventFrame j) (S.namedNode x) := by
        rw [hFrames, hNames]
      _ = S.presentAt j x := (hPresentS j x).symm
  exact full_event_source_eq_of_local_reconstruction
    R S hSelected hParameters hPresent hFrames
    recoverOld recoverUpper hOldR hOldS hUpperR hUpperS


end Kk
