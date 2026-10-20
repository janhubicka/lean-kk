import Kk.DiaryTransfer
import SuccessorTree.V10.GPlusShapeActionLaws
import SuccessorTree.V10.GPlusInducedAction

/-!
# Actual represented vertices and finite type-respecting maps

A finite carrier is an actual admissible partial structure. A represented
vertex is specified by two comparable admissible partial types in its
complete finite domain. Every finite type-respecting approximation acts on
these two types. The resulting vertex is defined using the actual
representation `GPlusRepresentingPair.vertex`, not a formal proxy.

The successor library proves that any global shape map induces a genuine
embedding of the auxiliary G+ structure. Since every intrinsic finite map
extends to a global shape map, we can prove representation independence,
preservation of all relational atoms (including nonrelations), and
equivariance of the finite action.

This does NOT yet construct a finite carrier for each successor diary, nor
does it establish that every diary occurrence factors through that carrier.
-/

namespace Kk

open SuccessorTree.V10

universe u

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- A pair of strictly comparable actual admissible partial types, both
belonging to the same finite source partial structure. -/
structure FiniteRepresentingPair (A : FiniteTypeBase family) where
  lower : TypeProfile A
  upper : TypeProfile A
  lower_lt_upper : lower.1 < upper.1

namespace FiniteRepresentingPair

variable {A : FiniteTypeBase family}

/-- Turn the finite data into the successor library's actual
representing pair of admissible partial types. -/
def toPair (P : FiniteRepresentingPair A) :
    GPlusRepresentingPair family :=
  ⟨P.lower.1, P.upper.1, P.lower_lt_upper⟩

/-- The genuine represented vertex in the auxiliary G+ structure. -/
noncomputable def vertex (P : FiniteRepresentingPair A) :
    FiniteGPlusVertex family :=
  P.toPair.vertex

/-- The image representing pair of an intrinsic finite type-respecting
map. Strictness follows from the *proved* global-extension theorem. -/
noncomputable def image (P : FiniteRepresentingPair A)
    (h : TypeRespectingEmbedding A) : GPlusRepresentingPair family := by
  obtain ⟨F, hF⟩ := TypeRespectingEmbedding.exists_extension A h
  refine ⟨h.1 P.lower, h.1 P.upper, ?_⟩
  calc
    h.1 P.lower = F.map P.lower.1 := (hF P.lower).symm
    _ < F.map P.upper.1 := F.map.map_lt_of_lt P.lower_lt_upper
    _ = h.1 P.upper := hF P.upper

/-- The image vertex depends only on the intrinsic finite function. -/
noncomputable def imageVertex (P : FiniteRepresentingPair A)
    (h : TypeRespectingEmbedding A) : FiniteGPlusVertex family :=
  (P.image h).vertex

/-- Equality of genuine representing pairs follows from equality
of the two endpoints; their order proofs are proof-irrelevant. -/
private theorem actualPair_ext
    {P Q : GPlusRepresentingPair family}
    (hLower : P.lower = Q.lower) (hUpper : P.upper = Q.upper) :
    P = Q := by
  cases P with
  | mk l u hp =>
    cases Q with
    | mk l' u' hq =>
      dsimp at hLower hUpper
      cases hLower
      cases hUpper
      rfl

/-- The finite image pair is identical to the pair obtained by ANY
global map agreeing with the intrinsic finite approximation. -/
theorem image_eq_of_extension (P : FiniteRepresentingPair A)
    (h : TypeRespectingEmbedding A)
    (F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (hF : ∀ u : TypeProfile A, F.map u.1 = h.1 u) :
    P.image h = P.toPair.image F.map := by
  apply actualPair_ext
  · exact (hF P.lower).symm
  · exact (hF P.upper).symm

/-- Genuine represented vertices agree with the successor library's
induced G+ action for every extension of the finite map. -/
theorem imageVertex_eq_of_extension (P : FiniteRepresentingPair A)
    (h : TypeRespectingEmbedding A)
    (F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (hF : ∀ u : TypeProfile A, F.map u.1 = h.1 u) :
    P.imageVertex h = gPlusShapeImage F.map P.vertex := by
  calc
    P.imageVertex h = (P.toPair.image F.map).vertex :=
      congrArg GPlusRepresentingPair.vertex (P.image_eq_of_extension h F hF)
    _ = gPlusShapeImage F.map P.vertex :=
      P.toPair.image_vertex_eq_canonicalShapeImage F.map

/-- Different source pairs representing the same G+ vertex have the
same image under every intrinsic finite approximation. -/
theorem imageVertex_eq_of_vertex_eq
    (P Q : FiniteRepresentingPair A)
    (h : TypeRespectingEmbedding A)
    (hPQ : P.vertex = Q.vertex) :
    P.imageVertex h = Q.imageVertex h := by
  obtain ⟨F, hF⟩ := TypeRespectingEmbedding.exists_extension A h
  rw [P.imageVertex_eq_of_extension h F hF,
    Q.imageVertex_eq_of_extension h F hF, hPQ]

/-- Composition with a genuine global map acts on the two finite
endpoints exactly by postcomposition. -/
theorem image_act (P : FiniteRepresentingPair A)
    (F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (h : TypeRespectingEmbedding A) :
    P.image (TypeRespectingEmbedding.act A F h) =
      (P.image h).image F.map := by
  apply actualPair_ext
  · rfl
  · rfl

/-- Equivariance for the actual induced G+ action, not merely a
formal action on copies. -/
theorem imageVertex_act (P : FiniteRepresentingPair A)
    (F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (h : TypeRespectingEmbedding A) :
    P.imageVertex (TypeRespectingEmbedding.act A F h) =
      gPlusShapeImage F.map (P.imageVertex h) := by
  calc
    P.imageVertex (TypeRespectingEmbedding.act A F h) =
        ((P.image h).image F.map).vertex :=
      congrArg GPlusRepresentingPair.vertex (P.image_act F h)
    _ = gPlusShapeImage F.map (P.imageVertex h) :=
      (P.image h).image_vertex_eq_canonicalShapeImage F.map

/-- The image of a labelled represented pair preserves, and reflects,
every directed binary atom in the auxiliary G+ structure. -/
theorem imageVertex_binary
    (P Q : FiniteRepresentingPair A)
    (h : TypeRespectingEmbedding A) (t : Fin db) :
    finiteGPlusBinary (P.imageVertex h) (Q.imageVertex h) t =
      finiteGPlusBinary P.vertex Q.vertex t := by
  obtain ⟨F, hF⟩ := TypeRespectingEmbedding.exists_extension A h
  rw [P.imageVertex_eq_of_extension h F hF,
    Q.imageVertex_eq_of_extension h F hF]
  exact (gPlusShapeImage_induced_LPlus F.map).2.1 P.vertex Q.vertex t

/-- The auxiliary E relation is likewise preserved exactly, including
its false values. -/
theorem imageVertex_e
    (P Q : FiniteRepresentingPair A)
    (h : TypeRespectingEmbedding A) :
    finiteGPlusE (P.imageVertex h) (Q.imageVertex h) =
      finiteGPlusE P.vertex Q.vertex := by
  obtain ⟨F, hF⟩ := TypeRespectingEmbedding.exists_extension A h
  rw [P.imageVertex_eq_of_extension h F hF,
    Q.imageVertex_eq_of_extension h F hF]
  exact (gPlusShapeImage_induced_LPlus F.map).2.2.2.2.1 P.vertex Q.vertex

/-- Any labelled finite family of represented vertices inherits the
same equivariance pointwise. Labels are never quotiented out. -/
theorem labelled_image_act
    {Λ : Type u} (points : Λ → FiniteRepresentingPair A)
    (F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (h : TypeRespectingEmbedding A) :
    (fun a : Λ => (points a).imageVertex
      (TypeRespectingEmbedding.act A F h)) =
    (fun a : Λ => gPlusShapeImage F.map ((points a).imageVertex h)) := by
  funext a
  exact (points a).imageVertex_act F h

end FiniteRepresentingPair

end Kk
