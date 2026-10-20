import Kk.RepresentedVertices

/-!
# Labelled finite copies in the actual auxiliary G+ structure

We regard a labelled copy as an injective map from its label set to
actual valid finite G+ codes. This retains the vertex labels. To give the
copy a specific graph isomorphism type, the required binary relation values
can be imposed on its source labelled tuple; the results below show that
every intrinsic finite type-respecting map preserves those values.

A family of pairs from ONE source finite partial structure gives a copy
under every intrinsic finite approximation. The action on these copies is
the already verified induced G+ action, applied coordinatewise.

Only the K_k-specific *factorisation* of all diary occurrences through
such fixed source pairs is left as a hypothesis in the final theorem here.
No artificial action or Ramsey axiom is introduced.
-/

namespace Kk

open SuccessorTree.V10

universe u v w

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- An injectively labelled family of genuine G+ vertices. -/
def LabelledGPlusCopy (family : List (NormalizedForbidden db du dd))
    (Λ : Type u) :=
  {vertices : Λ → FiniteGPlusVertex family // Function.Injective vertices}

namespace LabelledGPlusCopy

variable {Λ : Type u}

/-- Actual induced G+ action on a labelled copy. -/
noncomputable def map
    (F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (e : LabelledGPlusCopy family Λ) : LabelledGPlusCopy family Λ := by
  refine ⟨(fun a => gPlusShapeImage F.map (e.1 a)), ?_⟩
  intro a b hab
  exact e.2 ((gPlusShapeImage_induced_LPlus F.map).1 hab)

/-- Realise a labelled family of representing pairs from one finite
partial structure using an intrinsic type-respecting approximation. -/
noncomputable def fromPairs
    {A : FiniteTypeBase family}
    (points : Λ → FiniteRepresentingPair A)
    (hinj : Function.Injective (fun a => (points a).vertex))
    (h : TypeRespectingEmbedding A) : LabelledGPlusCopy family Λ := by
  refine ⟨(fun a => (points a).imageVertex h), ?_⟩
  obtain ⟨F, hF⟩ := TypeRespectingEmbedding.exists_extension A h
  intro a b hab
  rw [FiniteRepresentingPair.imageVertex_eq_of_extension (points a) h F hF,
    FiniteRepresentingPair.imageVertex_eq_of_extension (points b) h F hF] at hab
  exact hinj ((gPlusShapeImage_induced_LPlus F.map).1 hab)

/-- A global monoid map acts on the actual labelled image
exactly as it postcomposes the intrinsic finite approximation. -/
theorem map_fromPairs
    {A : FiniteTypeBase family}
    (points : Λ → FiniteRepresentingPair A)
    (hinj : Function.Injective (fun a => (points a).vertex))
    (F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (h : TypeRespectingEmbedding A) :
    map F (fromPairs points hinj h) =
      fromPairs points hinj (TypeRespectingEmbedding.act A F h) := by
  apply Subtype.ext
  funext a
  exact ((points a).imageVertex_act F h).symm

/-- The copied directed binary relation is identical at every pair of
labels, including the absence of an edge. -/
theorem fromPairs_binary
    {A : FiniteTypeBase family}
    (points : Λ → FiniteRepresentingPair A)
    (hinj : Function.Injective (fun a => (points a).vertex))
    (h : TypeRespectingEmbedding A) (a b : Λ) (t : Fin db) :
    finiteGPlusBinary ((fromPairs points hinj h).1 a)
        ((fromPairs points hinj h).1 b) t =
      finiteGPlusBinary (points a).vertex (points b).vertex t :=
  (points a).imageVertex_binary (points b) h t

/-- The copied auxiliary E relation is also preserved exactly. -/
theorem fromPairs_e
    {A : FiniteTypeBase family}
    (points : Λ → FiniteRepresentingPair A)
    (hinj : Function.Injective (fun a => (points a).vertex))
    (h : TypeRespectingEmbedding A) (a b : Λ) :
    finiteGPlusE ((fromPairs points hinj h).1 a)
        ((fromPairs points hinj h).1 b) =
      finiteGPlusE (points a).vertex (points b).vertex :=
  (points a).imageVertex_e (points b) h

/-- A genuine G+ version of the conditional diary bound. The
equivariance hypothesis of the abstract transfer theorem is now
discharged by `map_fromPairs`; only the geometric covering/factorisation
of the selected labelled copies is assumed. -/
theorem colour_factors_through_diary
    {ι : Type v} {κ : Type w} [Fintype κ] [Nonempty κ]
    (indices : Finset ι)
    (base : ι → FiniteTypeBase family)
    (points : (i : ι) → Λ → FiniteRepresentingPair (base i))
    (hinj : ∀ i : ι, Function.Injective
      (fun a => (points i a).vertex))
    (diary : LabelledGPlusCopy family Λ → ι)
    (selected : Set (LabelledGPlusCopy family Λ))
    (hIndexed : ∀ e, e ∈ selected → diary e ∈ indices)
    (hFactor : ∀ e, e ∈ selected → ∀ i, diary e = i →
      ∃ h : TypeRespectingEmbedding (base i),
        fromPairs (points i) (hinj i) h = e)
    (colour : LabelledGPlusCopy family Λ → κ) :
    ∃ (F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
      (byDiary : ι → κ),
      ∀ e, e ∈ selected →
        colour (map F e) = byDiary (diary e) := by
  exact diary_colouring_factors indices base
    (fun i h => fromPairs (points i) (hinj i) h)
    diary selected (fun F e => map F e)
    hIndexed hFactor
    (by
      intro F i h
      exact map_fromPairs (points i) (hinj i) F h)
    colour

end LabelledGPlusCopy

end Kk
