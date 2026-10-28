import Kk.TypeRespecting

/-!
# From type-respecting Ramsey to labelled diary colourings

This module proves the Ramsey-transfer step with an explicit interface
for the remaining graph-specific geometry. A finite source partial structure
is chosen for each diary. The finite approximations produce labelled graph
embeddings, and every embedding in the selected copy is required to have
a representation by the carrier associated to its diary.

Both the carrier factorisation and the compatibility of its representation
with the induced graph action are hypotheses here, not axioms and not
claimed as proved by the successor Ramsey theorem. The subsequent
K_k-specific files must discharge them.

The proof uses the *verified* simultaneous Ramsey theorem in
`Kk.TypeRespecting` and no new Ramsey hypothesis.
-/

namespace Kk

open SuccessorTree.V10

universe u v w

/-- The colours of the transformed labelled embeddings depend only on
their diaries, provided every selected embedding has a labelled finite
carrier and the carrier action agrees with the graph action.

Crucially, `hFactor` uses the diary of each labelled embedding, not an
unlabelled isomorphism type. -/
theorem diary_colouring_constant
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    {ι : Type u} {Embedding : Type v} {κ : Type w}
    [Fintype κ]
    (indices : Finset ι)
    (base : ι → FiniteTypeBase family)
    (represented : (i : ι) → TypeRespectingEmbedding (base i) → Embedding)
    (diary : Embedding → ι)
    (selected : Set Embedding)
    (mapEmbedding :
      SuccessorTree.SMTree.MMap (normalizedKptSMTree family) →
        Embedding → Embedding)
    (hIndexed : ∀ e, e ∈ selected → diary e ∈ indices)
    (hFactor : ∀ e, e ∈ selected → ∀ i, diary e = i →
      ∃ h : TypeRespectingEmbedding (base i), represented i h = e)
    (hEquivariance : ∀ F i (h : TypeRespectingEmbedding (base i)),
      mapEmbedding F (represented i h) =
        represented i (TypeRespectingEmbedding.act (base i) F h))
    (colour : Embedding → κ) :
    ∃ F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family),
      ∀ e, e ∈ selected → ∀ e', e' ∈ selected →
        diary e = diary e' →
          colour (mapEmbedding F e) = colour (mapEmbedding F e') := by
  obtain ⟨F, hF⟩ :=
    finite_family_type_respecting_ramsey indices base
      (fun i h => colour (represented i h))
  refine ⟨F, ?_⟩
  intro e he e' he' hDiary
  obtain ⟨h, hRepresented⟩ := hFactor e he (diary e) rfl
  obtain ⟨h', hRepresented'⟩ :=
    hFactor e' he' (diary e) hDiary.symm
  calc
    colour (mapEmbedding F e) =
        colour (mapEmbedding F (represented (diary e) h)) := by
          rw [hRepresented]
    _ = colour (represented (diary e)
        (TypeRespectingEmbedding.act (base (diary e)) F h)) := by
          rw [hEquivariance]
    _ = colour (represented (diary e)
        (TypeRespectingEmbedding.act (base (diary e)) F h')) :=
          hF (diary e) (hIndexed e he) h h'
    _ = colour (mapEmbedding F (represented (diary e) h')) := by
          rw [hEquivariance]
    _ = colour (mapEmbedding F e') := by
          rw [hRepresented']

/-- With a nonempty finite colour set, the final colouring actually
factors through a function on diary indices. Diary indices that do not
occur in the selected copy are assigned an arbitrary colour. -/
theorem diary_colouring_factors
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    {ι : Type u} {Embedding : Type v} {κ : Type w}
    [Fintype κ] [Nonempty κ]
    (indices : Finset ι)
    (base : ι → FiniteTypeBase family)
    (represented : (i : ι) → TypeRespectingEmbedding (base i) → Embedding)
    (diary : Embedding → ι)
    (selected : Set Embedding)
    (mapEmbedding :
      SuccessorTree.SMTree.MMap (normalizedKptSMTree family) →
        Embedding → Embedding)
    (hIndexed : ∀ e, e ∈ selected → diary e ∈ indices)
    (hFactor : ∀ e, e ∈ selected → ∀ i, diary e = i →
      ∃ h : TypeRespectingEmbedding (base i), represented i h = e)
    (hEquivariance : ∀ F i (h : TypeRespectingEmbedding (base i)),
      mapEmbedding F (represented i h) =
        represented i (TypeRespectingEmbedding.act (base i) F h))
    (colour : Embedding → κ) :
    ∃ (F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
      (byDiary : ι → κ),
      ∀ e, e ∈ selected →
        colour (mapEmbedding F e) = byDiary (diary e) := by
  classical
  obtain ⟨F, hF⟩ := diary_colouring_constant indices base represented
    diary selected mapEmbedding hIndexed hFactor hEquivariance colour
  let byDiary : ι → κ := fun i =>
    if h : ∃ e : Embedding, e ∈ selected ∧ diary e = i then
      colour (mapEmbedding F (Classical.choose h))
    else Classical.choice ‹Nonempty κ›
  refine ⟨F, byDiary, ?_⟩
  intro e he
  have h : ∃ e' : Embedding,
      e' ∈ selected ∧ diary e' = diary e := ⟨e, he, rfl⟩
  have hs := Classical.choose_spec h
  have heq :
      colour (mapEmbedding F e) =
        colour (mapEmbedding F (Classical.choose h)) :=
    hF e he (Classical.choose h) hs.1 hs.2.symm
  change colour (mapEmbedding F e) =
    (if h' : ∃ e' : Embedding, e' ∈ selected ∧ diary e' = diary e then
        colour (mapEmbedding F (Classical.choose h'))
      else Classical.choice ‹Nonempty κ›)
  rw [dif_pos h]
  exact heq

end Kk
