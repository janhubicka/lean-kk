import Kk.CommonCap
import Kk.enumerated_copies

/-!
# Countable source orbits imply labelled diary canonisation in G-omega

This is the next application layer beyond the generic finite-carrier
and enumerated-G+ interfaces.

Each diary is assigned a genuine countable forbidden-free L+ source
and an injectively labelled FINITE tuple of its prefix-code vertices.
The finite source base and the type-respecting approximation are then
constructed as conclusions, by taking a common cap above those actual
prefixes. No full-profile factorisation hypothesis is introduced.

If every selected occurrence is a global G-omega monoid image of the
chosen source copy for its labelled diary, the verified finite-family
type-respecting Ramsey theorem makes the transformed colour depend only
on the diary. This theorem isolates just ONE remaining geometric
hypothesis: the common labelled monoid orbit. It does not assert this
hypothesis for the manuscript's K_k diaries.
-/

namespace Kk

open SuccessorTree.V10

universe u v w

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}
variable {Λ : Type u}

/-- The honest labelled source copy in the fixed enumeration: read the
actual countable L+ prefix codes and take their inverse enumeration
ranks. No abstract tuple representation is used. -/
noncomputable def countableSourceCopy
    (enum : Nat ≃ FiniteGPlusVertex family)
    (C : CountableEnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L)
    (indices : Λ → Nat)
    (hInjective : Function.Injective indices) :
    LabelledGOmegaCopy Λ :=
  LabelledGOmegaCopy.fromGPlus enum
    ⟨(fun a => C.toGPlus family hAvoid (indices a)),
      by
        intro a b hab
        apply hInjective
        exact C.toGPlus_injective family hAvoid hab⟩

/-- Every genuine finite labelled countable source copy has ONE
actual admissible full-profile source and one intrinsic finite
type-respecting approximation representing it exactly.

This derives the labelled representation, including its injectivity,
from the countable prefix-code construction itself. -/
theorem countableSourceCopy_finite_representation
    (enum : Nat ≃ FiniteGPlusVertex family)
    (C : CountableEnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L)
    (indices : Λ → Nat) (N : Nat)
    (hBound : ∀ a, indices a ≤ N)
    (hInjective : Function.Injective indices) :
    ∃ (A : FiniteTypeBase family)
      (points : Λ → FiniteRepresentingPair A)
      (hinj : Function.Injective
        (fun a => (points a).vertex))
      (h : TypeRespectingEmbedding A),
      LabelledGOmegaCopy.fromPairs enum points hinj h =
        countableSourceCopy enum C hAvoid indices hInjective := by
  classical
  obtain ⟨A, points, hinj, hPoints⟩ :=
    countable_labelled_carrier C hAvoid indices N hBound hInjective
  let I : SuccessorTree.SMTree.MMap (normalizedKptSMTree family) :=
    SuccessorTree.SMTree.MMap.id (normalizedKptSMTree family)
  let h : TypeRespectingEmbedding A :=
    TypeRespectingEmbedding.ofRestriction A
      ⟨(fun u : TypeProfile A => u.1), ⟨I, rfl⟩⟩
  refine ⟨A, points, hinj, h, ?_⟩
  apply Subtype.ext
  funext a
  change enum.symm ((points a).imageVertex h) =
    enum.symm (C.toGPlus family hAvoid (indices a))
  have hImage : (points a).imageVertex h =
      gPlusShapeImage I.map (points a).vertex :=
    (points a).imageVertex_eq_of_extension h I (fun _ => rfl)
  rw [hImage, hPoints a]
  have hIdentity :
      I.map = SuccessorTree.ShapeMap.id (admissibleKptSTree family) := rfl
  rw [hIdentity]
  exact congrArg enum.symm
    (gPlusShapeImage_id (C.toGPlus family hAvoid (indices a)))

/-- A conditional G-omega diary theorem with only the TRUE geometrical
orbit hypothesis: countable source carriers and finite full-profile
factorisations are constructed, not assumed. The chosen finite source
can vary from one diary to another.

The conclusion is about the genuine conjugated induced G-omega action.
Showing the orbit premise for the K_k resolved diary normal form is
precisely the pending full-envelope comparison. -/
theorem countable_source_orbits_colour_factors
    {ι : Type v} {κ : Type w}
    [Fintype κ] [Nonempty κ]
    (enum : Nat ≃ FiniteGPlusVertex family)
    (diaryIndices : Finset ι)
    (sources : ι → CountableEnumeratedPartialStructure db du dd)
    (hAvoid : ∀ i bad, bad ∈ family → bad.Avoids (sources i).L)
    (positions : ι → Λ → Nat)
    (bound : ι → Nat)
    (hBound : ∀ i a, positions i a ≤ bound i)
    (hInjective : ∀ i, Function.Injective (positions i))
    (diary : LabelledGOmegaCopy Λ → ι)
    (selected : Set (LabelledGOmegaCopy Λ))
    (hIndexed : ∀ e, e ∈ selected → diary e ∈ diaryIndices)
    (hOrbit : ∀ e, e ∈ selected → ∀ i, diary e = i →
      ∃ F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family),
        LabelledGOmegaCopy.map enum F
          (countableSourceCopy enum (sources i)
            (hAvoid i) (positions i) (hInjective i)) = e)
    (colour : LabelledGOmegaCopy Λ → κ) :
    ∃ (F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
      (byDiary : ι → κ),
      ∀ e, e ∈ selected →
        colour (LabelledGOmegaCopy.map enum F e) =
          byDiary (diary e) := by
  classical
  have hRepresentation : ∀ i : ι,
      ∃ (A : FiniteTypeBase family)
        (points : Λ → FiniteRepresentingPair A)
        (hinj : Function.Injective (fun a => (points a).vertex))
        (h : TypeRespectingEmbedding A),
        LabelledGOmegaCopy.fromPairs enum points hinj h =
          countableSourceCopy enum (sources i)
            (hAvoid i) (positions i) (hInjective i) := by
    intro i
    exact countableSourceCopy_finite_representation enum
      (sources i) (hAvoid i) (positions i) (bound i)
      (hBound i) (hInjective i)
  choose base points hinj seed hSeed using hRepresentation
  apply LabelledGOmegaCopy.colour_factors_through_diary
    enum diaryIndices base points hinj diary selected hIndexed ?_ colour
  intro e he i hDiary
  obtain ⟨F, hF⟩ := hOrbit e he i hDiary
  refine ⟨TypeRespectingEmbedding.act (base i) F (seed i), ?_⟩
  calc
    LabelledGOmegaCopy.fromPairs enum (points i) (hinj i)
        (TypeRespectingEmbedding.act (base i) F (seed i)) =
      LabelledGOmegaCopy.map enum F
        (LabelledGOmegaCopy.fromPairs enum (points i) (hinj i) (seed i)) :=
          (LabelledGOmegaCopy.map_fromPairs enum (points i)
            (hinj i) F (seed i)).symm
    _ = LabelledGOmegaCopy.map enum F
        (countableSourceCopy enum (sources i)
          (hAvoid i) (positions i) (hInjective i)) := by
          rw [hSeed i]
    _ = e := hF

end Kk
