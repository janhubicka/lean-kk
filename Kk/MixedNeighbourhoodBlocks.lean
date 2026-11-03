import Kk.OnePointCliqueExtension
import Mathlib.Tactic

/-!
# Mixed neighbourhood cliques with mutually nonadjacent reserved blocks

In the KK-free resolved-copy schedule, distinct reserved clique
blocks are chosen mutually nonadjacent. This eliminates cliques
meeting TWO distinct reserved blocks, but does not eliminate
cliques combining one block with arbitrary older selected vertices
and split/coding parameters.

Here every old vertex is either unreserved (tag = none), or
belongs to a reserved block (tag = some b). The only geometrical
hypothesis is absence of edges between DIFFERENT tagged blocks.
We prove that every clique lies either entirely in unreserved
vertices or inside ONE block together with unreserved vertices.

Consequently the exact one-point admissibility test reduces to
checking (1) the pure unreserved neighbourhood and (2) the
mixed neighbourhood of each block together with *all* unreserved
parameters. Replacing (2) by checks of isolated blocks would
be wrong. No claim is made that the proposed global numerical-H
gadget schedule has passed these local checks.
-/

namespace Kk

/-- Distinct reserved block labels cannot both occur in a clique
of old vertices when cross-block edges are forbidden. -/
theorem clique_reserved_blocks_agree
    (E : Nat → Nat → Bool) (N B : Nat)
    (block : Nat → Option (Fin B))
    (hCross : ∀ x y (b c : Fin B),
      x < N → y < N →
      block x = some b → block y = some c →
      b ≠ c → E x y = false)
    (s : Finset Nat)
    (hWithin : ∀ x ∈ s, x < N)
    (hClique : IsDirectedCliqueOn E s)
    (x y : Nat) (hx : x ∈ s) (hy : y ∈ s)
    (b c : Fin B)
    (hbx : block x = some b) (hcy : block y = some c) :
    b = c := by
  by_contra hbc
  have hxy : x ≠ y := by
    intro hEq
    have hSome : (some b : Option (Fin B)) = some c := by
      calc
        some b = block x := hbx.symm
        _ = block y := congrArg block hEq
        _ = some c := hcy
    exact hbc (Option.some.inj hSome)
  have hEdge : E x y = true := hClique x hx y hy hxy
  have hMissing : E x y = false :=
    hCross x y b c (hWithin x hx) (hWithin y hy) hbx hcy hbc
  rw [hMissing] at hEdge
  cases hEdge

/-- The exact one-block reduction, with arbitrary unreserved
vertices (including split/coding parameters) retained. -/
theorem clique_unreserved_or_one_block
    (E : Nat → Nat → Bool) (N B : Nat)
    (block : Nat → Option (Fin B))
    (hCross : ∀ x y (b c : Fin B),
      x < N → y < N →
      block x = some b → block y = some c →
      b ≠ c → E x y = false)
    (s : Finset Nat)
    (hWithin : ∀ x ∈ s, x < N)
    (hClique : IsDirectedCliqueOn E s) :
    (∀ x ∈ s, block x = none) ∨
      ∃ b : Fin B, ∀ x ∈ s,
        block x = none ∨ block x = some b := by
  classical
  by_cases hExists : ∃ x ∈ s, ∃ b : Fin B, block x = some b
  · obtain ⟨x,hx,b,hbx⟩ := hExists
    right
    refine ⟨b, ?_⟩
    intro y hy
    cases hY : block y with
    | none => exact Or.inl hY
    | some c =>
      right
      have hSame : b = c :=
        clique_reserved_blocks_agree E N B block
          hCross s hWithin hClique x y hx hy b c hbx hY
      simpa [hSame] using hY
  · left
    intro y hy
    cases hY : block y with
    | none => exact hY
    | some c =>
      exact False.elim (hExists ⟨y,hy,c,hY⟩)

/-- A sound replacement for the invalid isolated-block argument:
besides a pure-parameter test, one must check EACH individual
reserved block *together with every unreserved vertex*.

The hypotheses are the exact smaller mixed-clique tests. The
cross-block nonedge condition eliminates configurations containing
vertices of two distinct reserved blocks. The theorem then invokes
the independently verified exact one-point neighbourhood criterion.
-/
theorem onePointGraph_cliqueFree_of_block_checks
    (E : Nat → Nat → Bool) (N ell B : Nat)
    (neighbour : Nat → Bool) (hEll : 0 < ell)
    (block : Nat → Option (Fin B))
    (hOld : ¬ HasCliqueBelow E N ell)
    (hCross : ∀ x y (b c : Fin B),
      x < N → y < N →
      block x = some b → block y = some c →
      b ≠ c → E x y = false)
    (hNoUnreserved :
      ∀ s : Finset Nat, s.card = ell-1 →
        (∀ x ∈ s, x < N ∧ neighbour x = true) →
        IsDirectedCliqueOn E s →
        ¬ (∀ x ∈ s, block x = none))
    (hNoMixedBlock :
      ∀ b : Fin B, ∀ s : Finset Nat, s.card = ell-1 →
        (∀ x ∈ s, x < N ∧ neighbour x = true) →
        IsDirectedCliqueOn E s →
        ¬ (∀ x ∈ s,
          block x = none ∨ block x = some b)) :
    ¬ HasCliqueBelow
        (onePointGraphEdge E N neighbour) (N+1) ell := by
  apply (onePointGraph_cliqueFree_iff
    E N ell neighbour hEll hOld).2
  rintro ⟨s,hCard,hBound,hClique⟩
  have hWithin : ∀ x ∈ s, x < N := by
    intro x hx
    exact (hBound x hx).1
  rcases clique_unreserved_or_one_block E N B block
      hCross s hWithin hClique with hPlain | ⟨b,hBlock⟩
  · exact (hNoUnreserved s hCard hBound hClique) hPlain
  · exact (hNoMixedBlock b s hCard hBound hClique) hBlock

end Kk
