import Kk.RepresentedVertices
import SuccessorTree.V10.GPlusCommonUpperRepresentation
import Mathlib.Tactic

/-!
# A common finite carrier for a chain of genuine G+ vertices

The finite labelled carrier in the diary upper bound has two logically
different parts.

* Any finite chain of G+ vertices which are prefixes of the ordinary
  code of one admissible partial type has actual representing pairs in
  the same finite source partial structure.
* Showing that a fixed such chain represents **all** occurrences of one
  labelled successor diary still requires the diary/envelope comparison.

Only the first, elementary geometrical assertion is treated in this
module. Its construction uses the genuine admissible Kpt ancestors and
the proved common-upper representation theorem of lean-successors.
-/

namespace Kk

open SuccessorTree.V10

universe u

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

namespace FiniteRepresentingPair

variable {A : FiniteTypeBase family}

/-- An actual G+ vertex which is an ordinary-code prefix of a common
upper partial type has two source partial types in the same finite
admissible domain. -/
noncomputable def fromCommonUpper
    (U : TypeProfile A)
    (X : FiniteGPlusVertex family)
    (hX : X.val.IsPrefix (RawPartialTypeNode.ordinaryCode U.1.1)) :
    FiniteRepresentingPair A := by
  have hPos : 0 < X.val.size := finiteGPlusVertex_size_pos X
  have hBound : X.val.size ≤ U.level := hX.1
  have hLowerBound : X.val.size-1 ≤ U.level := by omega
  let S : TypeProfile A := U.ancestor (X.val.size-1) hLowerBound
  have hLe : S.1 ≤ U.1 := U.ancestor_le _ hLowerBound
  have hNe : S.1 ≠ U.1 := by
    intro hEq
    have hLev := congrArg LevelTree.lev hEq
    have hSLev : LevelTree.lev S.1 = X.val.size-1 := rfl
    have hULev : LevelTree.lev U.1 = U.level := rfl
    rw [hSLev, hULev] at hLev
    omega
  exact ⟨S, U, lt_of_le_of_ne hLe hNe⟩

/-- The source pair does not merely have the right size: it represents
precisely the prescribed genuine G+ vertex, including every L+ atom. -/
theorem fromCommonUpper_vertex
    (U : TypeProfile A)
    (X : FiniteGPlusVertex family)
    (hX : X.val.IsPrefix (RawPartialTypeNode.ordinaryCode U.1.1)) :
    (fromCommonUpper U X hX).vertex = X := by
  have hPair :
      (fromCommonUpper U X hX).toPair =
        GPlusRepresentingPair.fromUpper U.1 X.val.size
          (finiteGPlusVertex_size_pos X) hX.1 := by
    rfl
  change (fromCommonUpper U X hX).toPair.vertex = X
  rw [hPair]
  exact GPlusRepresentingPair.fromUpper_vertex_eq_of_prefix U.1 X hX

/-- An arbitrarily labelled family of prefixes uses ONE finite source
partial structure and ONE upper partial type. -/
noncomputable def fromCommonUpperFamily
    {Λ : Type u}
    (U : TypeProfile A)
    (points : Λ → FiniteGPlusVertex family)
    (hPoints : ∀ a, (points a).val.IsPrefix
      (RawPartialTypeNode.ordinaryCode U.1.1)) :
    Λ → FiniteRepresentingPair A :=
  fun a => fromCommonUpper U (points a) (hPoints a)

/-- The labelled points represented by that one finite carrier are
exactly the original points, without reindexing or losing labels. -/
theorem fromCommonUpperFamily_vertices
    {Λ : Type u}
    (U : TypeProfile A)
    (points : Λ → FiniteGPlusVertex family)
    (hPoints : ∀ a, (points a).val.IsPrefix
      (RawPartialTypeNode.ordinaryCode U.1.1)) :
    ∀ a, (fromCommonUpperFamily U points hPoints a).vertex = points a := by
  intro a
  exact fromCommonUpper_vertex U (points a) (hPoints a)

/-- Injectivity of the original labelled vertices is preserved by
their common-upper representation. -/
theorem fromCommonUpperFamily_injective
    {Λ : Type u}
    (U : TypeProfile A)
    (points : Λ → FiniteGPlusVertex family)
    (hPoints : ∀ a, (points a).val.IsPrefix
      (RawPartialTypeNode.ordinaryCode U.1.1))
    (hInjective : Function.Injective points) :
    Function.Injective
      (fun a => (fromCommonUpperFamily U points hPoints a).vertex) := by
  intro a b hab
  apply hInjective
  simpa only [fromCommonUpperFamily_vertices U points hPoints] using hab

end FiniteRepresentingPair

namespace FiniteGPlusVertex

/-- The chosen finite ordinary base under the actual neutral cap
of a genuine G+ vertex. -/
noncomputable def finiteCarrier (top : FiniteGPlusVertex family) :
    FiniteTypeBase family :=
  top.canonicalCap.finiteTypeBase

/-- The canonical neutral cap itself is an admissible partial type
over the finite ordinary base it defines. -/
noncomputable def carrierUpper (top : FiniteGPlusVertex family) :
    TypeProfile top.finiteCarrier := by
  refine ⟨top.canonicalCap, ?_⟩
  refine ⟨by rfl, ?_⟩
  exact AdmissibleKptNode.prefix_finiteTypeBase_socle (le_refl _)

/-- Every prefix of the top code is a prefix of its genuine carrier
upper partial type. All four ordinary atomic tables are retained. -/
theorem prefix_carrierUpper
    (top X : FiniteGPlusVertex family)
    (hX : X.val.IsPrefix top.val) :
    X.val.IsPrefix (RawPartialTypeNode.ordinaryCode (top.carrierUpper).1.1) := by
  change X.val.IsPrefix
    (RawPartialTypeNode.ordinaryCode top.canonicalCap.1)
  rw [top.canonicalCap_ordinaryCode]
  exact hX

/-- A labelled family in the prefix chain of one maximum code has
one actual finite admissible carrier, without extra hypotheses on
a choice of base or ambient cap. -/
noncomputable def carrierPoints
    {Λ : Type u}
    (top : FiniteGPlusVertex family)
    (points : Λ → FiniteGPlusVertex family)
    (hPoints : ∀ a, (points a).val.IsPrefix top.val) :
    Λ → FiniteRepresentingPair top.finiteCarrier :=
  FiniteRepresentingPair.fromCommonUpperFamily top.carrierUpper
    points (fun a => top.prefix_carrierUpper (points a) (hPoints a))

/-- The labelled carrier constructed above represents exactly the
given vertices, not merely an isomorphic unlabelled family. -/
theorem carrierPoints_vertex
    {Λ : Type u}
    (top : FiniteGPlusVertex family)
    (points : Λ → FiniteGPlusVertex family)
    (hPoints : ∀ a, (points a).val.IsPrefix top.val) :
    ∀ a, (top.carrierPoints points hPoints a).vertex = points a := by
  intro a
  exact FiniteRepresentingPair.fromCommonUpperFamily_vertices
    top.carrierUpper points
    (fun x => top.prefix_carrierUpper (points x) (hPoints x)) a

/-- This finite carrier preserves all labels whenever the original
selected vertices were distinct. -/
theorem carrierPoints_injective
    {Λ : Type u}
    (top : FiniteGPlusVertex family)
    (points : Λ → FiniteGPlusVertex family)
    (hPoints : ∀ a, (points a).val.IsPrefix top.val)
    (hInj : Function.Injective points) :
    Function.Injective (fun a => (top.carrierPoints points hPoints a).vertex) := by
  intro a b h
  apply hInj
  simpa only [top.carrierPoints_vertex points hPoints] using h

end FiniteGPlusVertex

end Kk
