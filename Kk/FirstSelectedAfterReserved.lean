import Kk.HensonLeftDensityAge
import Kk.K4NeighbourCertificate
import Mathlib.Tactic

/-!
# The first selected original after a genuinely isolated reserved block

A reserved block inserted into the *fixed* Henson enumeration may
contain gaps in its original indices: the intervening vertices cannot
be retroactively erased. Moreover, the genuine isolated-reservation
lemma says that each chosen block vertex has no edges to earlier
nonreserved vertices; it does NOT constrain edges from earlier chosen
block vertices to LATER intervening nonreserved vertices.

For the FIRST selected original following that block, the constructor
can prescribe zero passing bits to EVERY intervening nonreserved
vertex. Assume the older selected vertices lie before the block's
starting cut. The complete neighbourhood then cannot contain a
mixed clique: any clique meeting an earlier selected vertex and a
reserved vertex contradicts the original reservation nonedges,
while every clique supported in the reserved block has fewer than
ell-1 vertices.

This proves that the *full* neighbourhood obstruction is exactly
the old selected-prefix obstruction, without checking an extra
mixed clique. It then realizes the selected original inside the
fixed Henson enumeration using the verified one-point left-density
bridge.

The proof is genuinely about the actual fixed adjacency table,
not an idealized contiguous gadget. It does not apply automatically
to LATER selected vertices which may already have edges to an
earlier reserved block, nor to the dependent E/Algorithm 5.4 B3
closure of the new original.
-/

namespace Kk

/-- Under actual isolation of a reserved set S from *earlier*
nonreserved vertices and the exclusion of intervening nonreserved
vertices from the new passing column, every sufficiently large
clique in the entire new neighbourhood lies below the start cut.

This statement covers *all* old vertices, including gaps in the
fixed enumeration; S need not be an interval or a complete clique.
The bound |S| < q is sharp. -/
theorem neighbourClique_iff_prior_of_isolated_reserved
    (E : Nat → Nat → Bool) (base front q : Nat)
    (S : Finset Nat) (neighbour : Nat → Bool)
    (hBase : base ≤ front)
    (hSLater : ∀ y ∈ S, base ≤ y)
    (hIsolated : ∀ y ∈ S, ∀ x, x < y → x ∉ S →
      E x y = false)
    (hOnlyReserved : ∀ y, y < front → base ≤ y →
      neighbour y = true → y ∈ S)
    (hSmall : S.card < q) :
    HasNeighbourCliqueBelow E front q neighbour ↔
      HasNeighbourCliqueBelow E base q neighbour := by
  constructor
  · rintro ⟨s, hCard, hBound, hClique⟩
    by_cases hOld : ∃ x ∈ s, x < base
    · obtain ⟨x, hx, hxBase⟩ := hOld
      have hAllOld : ∀ y ∈ s, y < base := by
        intro y hy
        by_contra hn
        have hyBase : base ≤ y := by omega
        have hyS : y ∈ S :=
          hOnlyReserved y (hBound y hy).1 hyBase (hBound y hy).2
        have hxNotS : x ∉ S := by
          intro hxS
          have hAfter := hSLater x hxS
          omega
        have hxy : x < y := by omega
        have hZero := hIsolated y hyS x hxy hxNotS
        have hPositive := hClique x hx y hy (by omega)
        rw [hZero] at hPositive
        cases hPositive
      refine ⟨s, hCard, ?_, hClique⟩
      intro y hy
      exact ⟨hAllOld y hy, (hBound y hy).2⟩
    · exfalso
      have hSub : s ⊆ S := by
        intro x hx
        have hBaseX : base ≤ x := by
          by_contra hNot
          have hBelow : x < base := by omega
          exact hOld ⟨x, hx, hBelow⟩
        exact hOnlyReserved x (hBound x hx).1 hBaseX
          (hBound x hx).2
      have hCardLe := Finset.card_le_card hSub
      omega
  · rintro ⟨s, hCard, hBound, hClique⟩
    refine ⟨s, hCard, ?_, hClique⟩
    intro x hx
    have hOld := hBound x hx
    exact ⟨by omega, hOld.2⟩

/-- The complete finite Bool checker at the new selected cut
reduces exactly to the original selected-prefix checker. The
reserved block need not be contiguous and cannot contain a
size-q clique because S.card < q. -/
theorem finiteNeighbourCliqueCheck_false_iff_prior_isolated
    (E : Nat → Nat → Bool) (base front q : Nat)
    (S : Finset Nat) (neighbour : Nat → Bool)
    (hBase : base ≤ front)
    (hSLater : ∀ y ∈ S, base ≤ y)
    (hIsolated : ∀ y ∈ S, ∀ x, x < y → x ∉ S →
      E x y = false)
    (hOnlyReserved : ∀ y, y < front → base ≤ y →
      neighbour y = true → y ∈ S)
    (hSmall : S.card < q) :
    finiteNeighbourCliqueCheck E front q neighbour = false ↔
      finiteNeighbourCliqueCheck E base q neighbour = false := by
  have hBridge :=
    neighbourClique_iff_prior_of_isolated_reserved
      E base front q S neighbour hBase hSLater hIsolated
      hOnlyReserved hSmall
  constructor
  · intro hFront
    apply (finiteNeighbourCliqueCheck_false_iff E base q neighbour).2
    intro hBad
    exact
      ((finiteNeighbourCliqueCheck_false_iff E front q neighbour).1
        hFront) (hBridge.mpr hBad)
  · intro hPrior
    apply (finiteNeighbourCliqueCheck_false_iff E front q neighbour).2
    intro hBad
    exact
      ((finiteNeighbourCliqueCheck_false_iff E base q neighbour).1
        hPrior) (hBridge.mp hBad)

/-- For the FIRST selected original immediately after an isolated
reserved block, it is enough to check the old selected-prefix
neighbourhood. In particular, no new "mixed parameters versus
one reserved block" test is needed for this single extension.
The conclusion is a genuine original of the unchanged Henson
enumeration, with all intervening passing bits zero.

This does not assert a negative old-prefix checker or apply after
earlier selected vertices have become adjacent to reserved blocks.
-/
theorem henson_leftDense_first_selected_after_isolated_reserved
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (base front : Nat) (S : Finset Nat)
    (neighbour : Nat → Bool)
    (hBase : base ≤ front)
    (hSLater : ∀ y ∈ S, base ≤ y)
    (hIsolated : ∀ y ∈ S, ∀ x, x < y → x ∉ S →
      E x y = false)
    (hOnlyReserved : ∀ y, y < front → base ≤ y →
      neighbour y = true → y ∈ S)
    (hSmall : S.card < ell-1)
    (hPriorCheck :
      finiteNeighbourCliqueCheck E base (ell-1) neighbour = false) :
    ∃ v : Nat, front ≤ v ∧
      ∀ x : Nat, x < v →
        E x v = (if x < front then neighbour x else false) ∧
        E v x = (if x < front then neighbour x else false) := by
  have hFullCheck :=
    (finiteNeighbourCliqueCheck_false_iff_prior_isolated
      E base front (ell-1) S neighbour hBase
      hSLater hIsolated hOnlyReserved hSmall).2 hPriorCheck
  exact henson_leftDense_realizes_certified_original
    ell hell E hAvoid hDense front neighbour hFullCheck

/-- Boundary regression: a two-vertex reserved set of cardinality
strictly less than three is NOT enough to guarantee K4 safety
without old-to-reserved isolation. The modified K4 seed has a
full mixed-parameter triangle despite the old-prefix check. -/
theorem k4_mixed_parameter_isolation_necessary :
    finiteNeighbourCliqueCheck k4BadMixedParameterEdge 1 3
      k4SeedNewNeighbour = false ∧
    finiteNeighbourCliqueCheck k4BadMixedParameterEdge 3 3
      k4SeedNewNeighbour = true := by
  decide

end Kk
