import Kk.FullEventIndexedOrbitBridge
import Mathlib.Tactic

/-!
# Track E E56: reconstruct a full source record using only USED recipes

The existing conditional full event-indexed orbit bridge required
equality of all seed/positive/original atom maps and explicitly
equal presence/old/upper event fields. These are unnecessarily
strong for the *formal* comparison step.

Here only the atom VALUES used in each actual dependent-parameter
recipe are compared; presence and full L+ type fields are then
reconstructed from common deterministic functions of event frame
and named Kpt/G+ node.

The geometric assertions that these rules describe the two actual
resolved numerical-H+ diary occurrences remain separate assumptions.

English-first proof and 18 hostile tests:
  docs/track_e_used_recipe_reconstruction_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- Equality of only USED physical seed/positive/meet recipe outcomes
identifies all NAMED dependent Kpt parameter nodes. It does not
require equality of unused ambient original names or even of the
meet's two original witnesses when their actual results agree. -/
theorem kpt_used_recipes_identify_parameter_nodes
    {n : Nat} {Parameters Old Upper Events Kind Character : Type}
    {Seeds Positives Originals : Type}
    (R S : KptEventIndexedSourceRecord family n
      Parameters Old Upper Events Kind Character)
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
          (atomsG.ambientOriginal u) (atomsG.ambientOriginal v)) :
    R.parameters = S.parameters := by
  funext p
  cases h : recipes p with
  | seed s =>
    have hF : R.parameters p = atomsF.seed s := by
      simpa only [h, KptClosureRecipe.evaluate] using hRecipeF p
    have hG : S.parameters p = atomsG.seed s := by
      simpa only [h, KptClosureRecipe.evaluate] using hRecipeG p
    exact hF.trans ((hSeed p s h).trans hG.symm)
  | positive q =>
    have hF : R.parameters p = atomsF.positiveParameter q := by
      simpa only [h, KptClosureRecipe.evaluate] using hRecipeF p
    have hG : S.parameters p = atomsG.positiveParameter q := by
      simpa only [h, KptClosureRecipe.evaluate] using hRecipeG p
    exact hF.trans ((hPositive p q h).trans hG.symm)
  | meetOf u v =>
    have hF : R.parameters p =
        LevelTree.meet
          (atomsF.ambientOriginal u) (atomsF.ambientOriginal v) := by
      simpa only [h, KptClosureRecipe.evaluate] using hRecipeF p
    have hG : S.parameters p =
        LevelTree.meet
          (atomsG.ambientOriginal u) (atomsG.ambientOriginal v) := by
      simpa only [h, KptClosureRecipe.evaluate] using hRecipeG p
    exact hF.trans ((hMeet p u v h).trans hG.symm)

/-- Exact conditional E56 reconstruction:
 * the selected source tuples coincide by the independently checked
   strict-prefix-chain/unlabelled-inverse-set theorem;
 * dependent parameters coincide by USED closure recipes only;
 * full synchronized event frames, presence, assigned old and upper
   dependent L+ types are recovered by the SAME physical functions
   on event frames and the actual named source nodes.

No source orbit, numerical H+ realization or diary-level bound is
concluded unless the still-explicit geometric premises are proved.
Genuine meet witnesses must be SameComponent compatible in BOTH
presentations; the corresponding WellFormed conditions are
requirements of the proposed physical application. -/
theorem full_event_source_eq_of_used_recipes_and_recovery
    {n : Nat} {Parameters Old Upper Events Kind Character : Type}
    {Seeds Positives Originals : Type}
    (F G : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (R S : KptEventIndexedSourceRecord family n
      Parameters Old Upper Events Kind Character)
    (targetF targetG : Fin n → FiniteGPlusVertex family)
    (hSelectedF : ∀ a,
      gPlusShapeImage F.map (R.selected a) = targetF a)
    (hSelectedG : ∀ a,
      gPlusShapeImage G.map (S.selected a) = targetG a)
    (hStrictF : ∀ a b : Fin n, a < b →
      (targetF a).IsProperPrefix (targetF b))
    (hStrictG : ∀ a b : Fin n, a < b →
      (targetG a).IsProperPrefix (targetG b))
    (hInverse :
      (gPlusShapeImage F.map) ⁻¹' (Set.range targetF) =
      (gPlusShapeImage G.map) ⁻¹' (Set.range targetG))
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
    labelled_prefix_sources_eq_of_inverse_image_sets
      F G targetF targetG R.selected S.selected
      hSelectedF hSelectedG hStrictF hStrictG hInverse
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
