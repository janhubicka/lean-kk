import Kk.FiniteNeighbourCertificates
import Kk.K4NumericalHAtoms
import Mathlib.Tactic

/-!
# Independent finite certificate for the K4 reserved-original seed

The concrete four-original base used in the numerical-H K4 regression
has originals p=0, q1=1, q2=2, x=3. Among the three earlier
originals, only q1--q2 is an edge; the new x is adjacent to all
three. This is a genuine K4-free one-point extension because its
complete three-vertex neighbourhood is not a triangle.

Changing only the older parameter-to-block edges p--q1, p--q2
would make the same proposed x extension forbidden. The two
Boolean decisions below are formally equivalent to existence or
nonexistence of the precise complete-neighbourhood witness.

This is a small concrete regression, NOT a proof that every stage
of the proposed globally resolved copy can use the same template.
-/

namespace Kk

/-- The selected new original x is prescribed adjacent to all
three older originals in the concrete four-original K4 seed. -/
def k4SeedNewNeighbour (i : Nat) : Bool := decide (i < 3)

/-- An inadmissible alternative old prefix: all three older
vertices (including parameter p) form a triangle. -/
def k4BadMixedParameterEdge (i j : Nat) : Bool :=
  decide (i < 3 ∧ j < 3 ∧ i ≠ j)

/-- The ACTUAL old base graph of the K4 numerical-H example passes
the complete neighbourhood test, including parameter p=0. -/
theorem k4Seed_full_neighbourhood_certificate :
    finiteNeighbourCliqueCheck k4FourOriginalEdge 3 3
      k4SeedNewNeighbour = false := by
  decide

/-- Therefore inserting selected original x with the prescribed
three neighbour edges is K4-free, as a genuine four-original
one-point extension. -/
theorem k4Seed_safe_onePoint_extension :
    ¬ HasCliqueBelow
      (onePointGraphEdge k4FourOriginalEdge 3
        k4SeedNewNeighbour) 4 4 := by
  have hOld : ¬ HasCliqueBelow k4FourOriginalEdge 3 4 :=
    no_clique_below_of_small_carrier k4FourOriginalEdge 3 4 (by decide)
  exact
    (onePointGraph_cliqueFree_iff_finite_certificate
      k4FourOriginalEdge 3 4 k4SeedNewNeighbour (by decide) hOld).2
      k4Seed_full_neighbourhood_certificate

/-- The same selected-to-old adjacency prescription becomes unsafe
if the older parameter joins the block's two vertices in a triangle. -/
theorem k4MixedParameter_triangle_certificate :
    finiteNeighbourCliqueCheck k4BadMixedParameterEdge 3 3
      k4SeedNewNeighbour = true := by
  decide

/-- The bad mixed-parameter table really produces a forbidden K4
after adding x; no selected-front calculation can rescue it. -/
theorem k4MixedParameter_forbidden_onePoint_extension :
    HasCliqueBelow
      (onePointGraphEdge k4BadMixedParameterEdge 3
        k4SeedNewNeighbour) 4 4 := by
  have hNeighbour : HasNeighbourCliqueBelow
      k4BadMixedParameterEdge 3 3 k4SeedNewNeighbour :=
    (finiteNeighbourCliqueCheck_true_iff
      k4BadMixedParameterEdge 3 3 k4SeedNewNeighbour).mp
        k4MixedParameter_triangle_certificate
  exact (onePointGraph_hasClique_iff
    k4BadMixedParameterEdge 3 4 k4SeedNewNeighbour (by decide)).mpr
      (Or.inr hNeighbour)

end Kk
