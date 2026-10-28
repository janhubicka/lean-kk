import Kk.CommonCap
import Kk.enumerated_copies

/-!
# Ramsey reduction from a finite labelled prefix-chain source

A minimal envelope's labelled source need not itself be an occurrence
in the selected Henson copy, nor does it need to be exhibited as
a tuple in a separate countable auxiliary structure.

It suffices to produce, for each labelled diary, ONE actual finite
prefix chain of valid G+ codes and an honest monoid map taking this
labelled source to every occurrence of that diary. The existing
common-neutral-cap construction supplies its entire admissible finite
full-profile carrier, with no extra geometry hypothesis.

This theorem removes the otherwise unnecessary countable-source
requirement from the checked diary Ramsey transfer. The K_k-specific
work remains: construct the compressed source prefix chain and prove
the common labelled orbit property using the resolved diary's entire
parameter-closed age record.
-/

namespace Kk

open SuccessorTree.V10

universe u v w

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}
variable {Λ : Type u}

/-- A single finite prefix chain already has a genuine full-profile
carrier which represents its labelled copy in the fixed G-omega
enumeration by the identity intrinsic type-respecting map. -/
theorem prefixChain_finite_representation
    (enum : Nat ≃ FiniteGPlusVertex family)
    (top : FiniteGPlusVertex family)
    (points : Λ → FiniteGPlusVertex family)
    (hPrefix : ∀ a, (points a).val.IsPrefix top.val)
    (hInjective : Function.Injective points) :
    ∃ (A : FiniteTypeBase family)
      (pairs : Λ → FiniteRepresentingPair A)
      (hinj : Function.Injective
        (fun a => (pairs a).vertex))
      (h : TypeRespectingEmbedding A),
      LabelledGOmegaCopy.fromPairs enum pairs hinj h =
        LabelledGOmegaCopy.fromGPlus enum
          (⟨points, hInjective⟩ : LabelledGPlusCopy family Λ) := by
  classical
  let A : FiniteTypeBase family := FiniteGPlusVertex.finiteCarrier top
  let pairs : Λ → FiniteRepresentingPair A :=
    FiniteGPlusVertex.carrierPoints top points hPrefix
  have hinj : Function.Injective (fun a => (pairs a).vertex) :=
    FiniteGPlusVertex.carrierPoints_injective
      top points hPrefix hInjective
  let I : SuccessorTree.SMTree.MMap (normalizedKptSMTree family) :=
    SuccessorTree.SMTree.MMap.id (normalizedKptSMTree family)
  let h : TypeRespectingEmbedding A :=
    TypeRespectingEmbedding.ofRestriction A
      ⟨(fun u : TypeProfile A => u.1), ⟨I, rfl⟩⟩
  refine ⟨A, pairs, hinj, h, ?_⟩
  apply Subtype.ext
  funext a
  change enum.symm ((pairs a).imageVertex h) = enum.symm (points a)
  have hImage : (pairs a).imageVertex h =
      gPlusShapeImage I.map (pairs a).vertex :=
    (pairs a).imageVertex_eq_of_extension h I (fun _ => rfl)
  rw [hImage, FiniteGPlusVertex.carrierPoints_vertex
    top points hPrefix a]
  have hIdentity :
      I.map = SuccessorTree.ShapeMap.id (admissibleKptSTree family) := rfl
  rw [hIdentity]
  exact congrArg enum.symm (gPlusShapeImage_id (points a))

/-- One prefix-chain source per diary is sufficient for the FULL
enumerated diary-colouring transfer. All admissible finite carriers,
intrinsic functions, action compatibility and the finite Ramsey
refinement are produced inside the proof.

The only application-specific hypothesis is that every selected
occurrence is an actual monoid image of the corresponding FIXED
labelled prefix-chain source. -/
theorem prefix_chain_orbits_colour_factors
    {ι : Type v} {κ : Type w}
    [Fintype κ] [Nonempty κ]
    (enum : Nat ≃ FiniteGPlusVertex family)
    (diaryIndices : Finset ι)
    (top : ι → FiniteGPlusVertex family)
    (points : ι → Λ → FiniteGPlusVertex family)
    (hPrefix : ∀ i a, (points i a).val.IsPrefix (top i).val)
    (hInjective : ∀ i, Function.Injective (points i))
    (diary : LabelledGOmegaCopy Λ → ι)
    (selected : Set (LabelledGOmegaCopy Λ))
    (hIndexed : ∀ e, e ∈ selected → diary e ∈ diaryIndices)
    (hOrbit : ∀ e, e ∈ selected → ∀ i, diary e = i →
      ∃ F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family),
        LabelledGOmegaCopy.map enum F
          (LabelledGOmegaCopy.fromGPlus enum
            (⟨points i, hInjective i⟩ : LabelledGPlusCopy family Λ)) = e)
    (colour : LabelledGOmegaCopy Λ → κ) :
    ∃ (F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
      (byDiary : ι → κ),
      ∀ e, e ∈ selected →
        colour (LabelledGOmegaCopy.map enum F e) =
          byDiary (diary e) := by
  classical
  have hRepresentation : ∀ i : ι,
      ∃ (A : FiniteTypeBase family)
        (pairs : Λ → FiniteRepresentingPair A)
        (hinj : Function.Injective (fun a => (pairs a).vertex))
        (h : TypeRespectingEmbedding A),
        LabelledGOmegaCopy.fromPairs enum pairs hinj h =
          LabelledGOmegaCopy.fromGPlus enum
            (⟨points i, hInjective i⟩ : LabelledGPlusCopy family Λ) := by
    intro i
    exact prefixChain_finite_representation enum
      (top i) (points i) (hPrefix i) (hInjective i)
  choose base pairs hinj seed hSeed using hRepresentation
  apply LabelledGOmegaCopy.colour_factors_through_diary
    enum diaryIndices base pairs hinj diary selected hIndexed ?_ colour
  intro e he i hDiary
  obtain ⟨F, hF⟩ := hOrbit e he i hDiary
  refine ⟨TypeRespectingEmbedding.act (base i) F (seed i), ?_⟩
  calc
    LabelledGOmegaCopy.fromPairs enum (pairs i) (hinj i)
        (TypeRespectingEmbedding.act (base i) F (seed i)) =
      LabelledGOmegaCopy.map enum F
        (LabelledGOmegaCopy.fromPairs enum (pairs i) (hinj i) (seed i)) :=
          (LabelledGOmegaCopy.map_fromPairs enum (pairs i)
            (hinj i) F (seed i)).symm
    _ = LabelledGOmegaCopy.map enum F
        (LabelledGOmegaCopy.fromGPlus enum
          (⟨points i, hInjective i⟩ : LabelledGPlusCopy family Λ)) := by
          rw [hSeed i]
    _ = e := hF

end Kk
