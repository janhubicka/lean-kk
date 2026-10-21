import Kk.LabelledCopies
import SuccessorTree.V10.GPlusSizeEnumeration

/-!
# Genuine labelled copies in the enumerated auxiliary graph G-omega

The source paper fixes a bijection iota from the unenumerated genuine G+
codes to the natural-number enumeration. The complete code-to-enumeration
equivalence is already constructed in lean-successors, including finite
layers and monotonicity of code sizes.

This file conjugates the REAL induced G+ action by that equivalence, rather
than pretending the unenumerated and enumerated actions are identical.
It then transports the verified finite type-respecting Ramsey interface
to labelled embeddings in the enumerated presentation.

An arbitrary induced G+ action need not preserve the numeric enumeration
order for equal-size codes. The selected H+ prefix-chain order is a
separate matter; no global ordered action is claimed here.

The missing K_k-specific input is still the labelled finite source
factorisation, not any further Ramsey theorem.
-/

namespace Kk

open SuccessorTree.V10

universe u v w

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- A labelled injective tuple of indices in the fixed G-omega enumeration. -/
def LabelledGOmegaCopy (Λ : Type u) :=
  {e : Λ → Nat // Function.Injective e}

namespace LabelledGOmegaCopy

variable {Λ : Type u}

/-- Read enumerated vertices as genuine finite G+ codes. -/
noncomputable def toGPlus
    (enum : Nat ≃ FiniteGPlusVertex family)
    (e : LabelledGOmegaCopy Λ) : LabelledGPlusCopy family Λ := by
  refine ⟨fun a => enum (e.1 a), ?_⟩
  intro a b hab
  exact e.2 (enum.injective hab)

/-- Encode a labelled family of actual finite G+ vertices. -/
noncomputable def fromGPlus
    (enum : Nat ≃ FiniteGPlusVertex family)
    (e : LabelledGPlusCopy family Λ) : LabelledGOmegaCopy Λ := by
  refine ⟨fun a => enum.symm (e.1 a), ?_⟩
  intro a b hab
  exact e.2 (enum.symm.injective hab)

@[simp] theorem toGPlus_fromGPlus
    (enum : Nat ≃ FiniteGPlusVertex family)
    (e : LabelledGPlusCopy family Λ) :
    toGPlus enum (fromGPlus enum e) = e := by
  apply Subtype.ext
  funext a
  exact enum.apply_symm_apply (e.1 a)

@[simp] theorem fromGPlus_toGPlus
    (enum : Nat ≃ FiniteGPlusVertex family)
    (e : LabelledGOmegaCopy Λ) :
    fromGPlus enum (toGPlus enum e) = e := by
  apply Subtype.ext
  funext a
  exact enum.symm_apply_apply (e.1 a)

/-- Actual induced action on the enumerated auxiliary graph: this is
literally conjugation through the fixed exhaustive enumeration. -/
noncomputable def map
    (enum : Nat ≃ FiniteGPlusVertex family)
    (F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (e : LabelledGOmegaCopy Λ) : LabelledGOmegaCopy Λ :=
  fromGPlus enum (LabelledGPlusCopy.map F (toGPlus enum e))

/-- The action commutes with passing to genuine finite G+ codes. -/
theorem toGPlus_map
    (enum : Nat ≃ FiniteGPlusVertex family)
    (F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (e : LabelledGOmegaCopy Λ) :
    toGPlus enum (map enum F e) =
      LabelledGPlusCopy.map F (toGPlus enum e) := by
  exact toGPlus_fromGPlus enum _

/-- A fixed source family of admissible represented pairs induces a
labelled copy in the enumerated presentation. -/
noncomputable def fromPairs
    (enum : Nat ≃ FiniteGPlusVertex family)
    {A : FiniteTypeBase family}
    (points : Λ → FiniteRepresentingPair A)
    (hinj : Function.Injective (fun a => (points a).vertex))
    (h : TypeRespectingEmbedding A) : LabelledGOmegaCopy Λ :=
  fromGPlus enum (LabelledGPlusCopy.fromPairs points hinj h)

/-- The genuine enumerated action on labelled copies is the finite
type-respecting action, conjugated by the SAME enumeration. -/
theorem map_fromPairs
    (enum : Nat ≃ FiniteGPlusVertex family)
    {A : FiniteTypeBase family}
    (points : Λ → FiniteRepresentingPair A)
    (hinj : Function.Injective (fun a => (points a).vertex))
    (F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (h : TypeRespectingEmbedding A) :
    map enum F (fromPairs enum points hinj h) =
      fromPairs enum points hinj
        (TypeRespectingEmbedding.act A F h) := by
  unfold map fromPairs
  rw [toGPlus_fromGPlus, LabelledGPlusCopy.map_fromPairs]

/-- The exact G-omega colour-transfer statement: if the finite labelled
source factorisation is available, one global genuine Kpt map makes
colours depend only on the diary. The map is the actual conjugated
G+ map, not an unrelated action assumed on natural-number indices. -/
theorem colour_factors_through_diary
    {ι : Type v} {κ : Type w} [Fintype κ] [Nonempty κ]
    (enum : Nat ≃ FiniteGPlusVertex family)
    (indices : Finset ι)
    (base : ι → FiniteTypeBase family)
    (points : (i : ι) → Λ → FiniteRepresentingPair (base i))
    (hinj : ∀ i : ι, Function.Injective
      (fun a => (points i a).vertex))
    (diary : LabelledGOmegaCopy Λ → ι)
    (selected : Set (LabelledGOmegaCopy Λ))
    (hIndexed : ∀ e, e ∈ selected → diary e ∈ indices)
    (hFactor : ∀ e, e ∈ selected → ∀ i, diary e = i →
      ∃ h : TypeRespectingEmbedding (base i),
        fromPairs enum (points i) (hinj i) h = e)
    (colour : LabelledGOmegaCopy Λ → κ) :
    ∃ (F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
      (byDiary : ι → κ),
      ∀ e, e ∈ selected →
        colour (map enum F e) = byDiary (diary e) := by
  exact diary_colouring_factors indices base
    (fun i h => fromPairs enum (points i) (hinj i) h)
    diary selected (fun F e => map enum F e)
    hIndexed hFactor
    (by
      intro F i h
      exact map_fromPairs enum (points i) (hinj i) F h)
    colour


/-- If two actual enumerated G+ vertices are strict prefix codes, their
order is preserved by every induced shape-map action, PROVIDED the
enumeration is nondecreasing by finite-code size. This does not claim
that arbitrary (incomparable) G+ vertices retain their numeric order. -/
theorem map_lt_of_prefix
    (enum : Nat ≃ FiniteGPlusVertex family)
    (hSizeMono : Monotone (fun n => (enum n).val.size))
    (F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (e : LabelledGOmegaCopy Λ)
    (a b : Λ)
    (hPrefix : (enum (e.1 a)).IsProperPrefix (enum (e.1 b))) :
    (map enum F e).1 a < (map enum F e).1 b := by
  have hImagePrefix :
      (gPlusShapeImage F.map (enum (e.1 a))).IsProperPrefix
        (gPlusShapeImage F.map (enum (e.1 b))) :=
    (gPlusShapeImage_properPrefix_iff F.map _ _).2 hPrefix
  have hSize : (gPlusShapeImage F.map (enum (e.1 a))).val.size <
      (gPlusShapeImage F.map (enum (e.1 b))).val.size :=
    hImagePrefix.2
  have hEnumA : enum ((map enum F e).1 a) =
      gPlusShapeImage F.map (enum (e.1 a)) := by
    exact enum.apply_symm_apply _
  have hEnumB : enum ((map enum F e).1 b) =
      gPlusShapeImage F.map (enum (e.1 b)) := by
    exact enum.apply_symm_apply _
  have hImageSize : (enum ((map enum F e).1 a)).val.size <
      (enum ((map enum F e).1 b)).val.size := by
    rw [hEnumA, hEnumB]
    exact hSize
  by_contra hNot
  have hReverse : (map enum F e).1 b ≤ (map enum F e).1 a :=
    Nat.le_of_not_gt hNot
  have hContrary := hSizeMono hReverse
  omega

/-- In the actual exhaustive G-omega enumeration, there is no
additional size-order hypothesis: lean-successors already constructs
and verifies the monotone layer enumeration. -/
theorem map_lt_of_prefix_in_fixed_enumeration
    (C : CountableEnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L)
    (F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (e : LabelledGOmegaCopy Λ)
    (a b : Λ)
    (hPrefix :
      ((GPlusEnumeration.enumerate C family hAvoid) (e.1 a)).IsProperPrefix
        ((GPlusEnumeration.enumerate C family hAvoid) (e.1 b))) :
    (map (GPlusEnumeration.enumerate C family hAvoid) F e).1 a <
      (map (GPlusEnumeration.enumerate C family hAvoid) F e).1 b := by
  exact map_lt_of_prefix (GPlusEnumeration.enumerate C family hAvoid)
    (GPlusEnumeration.enumerate_size_mono C family hAvoid)
    F e a b hPrefix


end LabelledGOmegaCopy
end Kk
