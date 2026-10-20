import SuccessorTree.Library.TypeRespecting

/-!
# Simultaneous Ramsey refinement for finite families

The source finite partial structures may differ from one diary to another.
Each colour is evaluated on the intrinsic type-respecting finite
approximations of its own partial structure. The simultaneous witness is
obtained from the public successor-tree theorem by composition.

This theorem is an application of
`SuccessorTree.V10.normalizedKpt_typeRespectingRamsey`, not an axiom.
It does not construct the labelled diary carriers or prove their
factorisation property: those are independent K_k-specific obligations.
-/

namespace Kk

open SuccessorTree.V10

universe u v

/-- A single monoid map makes a finite family of colourings homogeneous,
even when the finite partial structures are different. -/
theorem finite_family_type_respecting_ramsey
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    {ι : Type u} {κ : Type v} [Fintype κ]
    (indices : Finset ι)
    (base : ι → FiniteTypeBase family)
    (colour : (i : ι) → TypeRespectingEmbedding (base i) → κ) :
    ∃ F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family),
      ∀ (i : ι), i ∈ indices →
        ∀ (f g : TypeRespectingEmbedding (base i)),
          colour i (TypeRespectingEmbedding.act (base i) F f) =
            colour i (TypeRespectingEmbedding.act (base i) F g) := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
      refine ⟨SuccessorTree.SMTree.MMap.id (normalizedKptSMTree family), ?_⟩
      intro i hi
      simp at hi
  | @insert i indices hi ih =>
      obtain ⟨F, hF⟩ := ih
      let c : TypeRespectingEmbedding (base i) → κ :=
        fun f => colour i (TypeRespectingEmbedding.act (base i) F f)
      obtain ⟨R, hR⟩ :=
        normalizedKpt_typeRespectingRamsey family (base i) c
      refine ⟨SuccessorTree.SMTree.MMap.comp (normalizedKptSMTree family) F R, ?_⟩
      intro j hj f g
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa only [TypeRespectingEmbedding.act_comp] using hR f g
      · simpa only [TypeRespectingEmbedding.act_comp] using
          hF j hj (TypeRespectingEmbedding.act (base j) R f)
            (TypeRespectingEmbedding.act (base j) R g)

end Kk
