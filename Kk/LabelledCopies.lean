import Kk.RepresentedVertices
import SuccessorTree.V10.GPlusEnvelopePairLift

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
  change (points a).imageVertex h = (points b).imageVertex h at hab
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

/-- A stronger, geometric way to discharge labelled occurrence
factorisation: each occurrence of diary `i` is a genuine monoid image
of the same fixed *labelled* source copy for `i`.

The global-to-intrinsic step is now a theorem, not an extra axiom.
Proving the actual orbit property for resolved diaries is the remaining
K_k-specific envelope task. -/
theorem colour_factors_through_diary_of_orbits
    {ι : Type v} {κ : Type w} [Fintype κ] [Nonempty κ]
    (indices : Finset ι)
    (base : ι → FiniteTypeBase family)
    (points : (i : ι) → Λ → FiniteRepresentingPair (base i))
    (hinj : ∀ i : ι, Function.Injective
      (fun a => (points i a).vertex))
    (source : (i : ι) → TypeRespectingEmbedding (base i))
    (diary : LabelledGPlusCopy family Λ → ι)
    (selected : Set (LabelledGPlusCopy family Λ))
    (hIndexed : ∀ e, e ∈ selected → diary e ∈ indices)
    (hOrbit : ∀ e, e ∈ selected → ∀ i, diary e = i →
      ∃ F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family),
        map F (fromPairs (points i) (hinj i) (source i)) = e)
    (colour : LabelledGPlusCopy family Λ → κ) :
    ∃ (F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
      (byDiary : ι → κ),
      ∀ e, e ∈ selected →
        colour (map F e) = byDiary (diary e) := by
  apply colour_factors_through_diary indices base points hinj
    diary selected hIndexed ?_ colour
  intro e he i hDiary
  obtain ⟨F, hF⟩ := hOrbit e he i hDiary
  refine ⟨TypeRespectingEmbedding.act (base i) F (source i), ?_⟩
  exact (map_fromPairs (points i) (hinj i) F (source i)).symm.trans hF


/-- A genuine normalized Kpt envelope of the endpoints of a finite
injectively labelled family of representing pairs yields a simultaneous
labelled PREIMAGE COPY under the actual induced G+ action.

Unlike an unlabelled envelope statement, the chosen preimages preserve
all labels. This theorem needs an existing genuine monoid envelope of
the specified endpoints; it does not construct that envelope or show
that equal diaries choose the same source family. -/
theorem labelled_copy_lifts_of_envelope
    (F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (X : Set (AdmissibleKptNode family))
    (hEnvelope : SuccessorTree.SMTree.Envelope.IsEnvelope F.map X)
    (e : LabelledGPlusCopy family Λ)
    (pairs : Λ → GPlusRepresentingPair family)
    (hPairs : ∀ a, (pairs a).vertex = e.1 a)
    (hEndpoints : ∀ a, (pairs a).lower ∈ X ∧ (pairs a).upper ∈ X) :
    ∃ e0 : LabelledGPlusCopy family Λ, map F e0 = e := by
  classical
  have hLift : ∀ a, ∃ Q : GPlusRepresentingPair family,
      Q.image F.map = pairs a := by
    intro a
    exact (pairs a).lifts_from_shapeMap_range F.map
      (hEnvelope (hEndpoints a).1) (hEnvelope (hEndpoints a).2)
  choose Q hQ using hLift
  have hQInjective : Function.Injective (fun a => (Q a).vertex) := by
    intro a b hEq
    apply e.2
    rw [← hPairs a, ← hPairs b]
    have hImg := congrArg (gPlusShapeImage F.map) hEq
    rw [← (Q a).image_vertex_eq_canonicalShapeImage F.map,
        ← (Q b).image_vertex_eq_canonicalShapeImage F.map,
        hQ a, hQ b] at hImg
    exact hImg
  let e0 : LabelledGPlusCopy family Λ :=
    ⟨fun a => (Q a).vertex, hQInjective⟩
  refine ⟨e0, ?_⟩
  apply Subtype.ext
  funext a
  change gPlusShapeImage F.map ((Q a).vertex) = e.1 a
  rw [← (Q a).image_vertex_eq_canonicalShapeImage F.map,
    hQ a, hPairs a]


end LabelledGPlusCopy

end Kk
