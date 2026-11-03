import Kk.HensonEncoding
import Mathlib.Tactic

/-!
# Exact mixed-neighbourhood test for extending a finite K_ell-free graph

In the resolved-copy recursion, checking each reserved clique block
separately and making different blocks nonadjacent is not enough.
An older coding/split parameter can form a clique together with
vertices of ONE reserved block and the proposed new original.

This file proves the exact one-point extension criterion: if the old
finite prefix is K_ell-free, adding a new vertex is K_ell-free if and
only if its COMPLETE old neighbourhood is K_(ell-1)-free. In
particular, no parameter vertices may be omitted from that test.

The theorem is about genuine finite binary edge tables, not an
assumed property of the selected-front graph-age canonicalizer.
Specializing the criterion to a particular numerical-H gadget
still requires checking its actual adjacency table.
-/

namespace Kk

/-- A finite set is a complete *directed* clique in a Boolean graph. -/
def IsDirectedCliqueOn (E : Nat → Nat → Bool) (s : Finset Nat) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y → E x y = true

/-- A clique wholly contained in the finite initial segment [0,N). -/
def HasCliqueBelow (E : Nat → Nat → Bool) (N size : Nat) : Prop :=
  ∃ s : Finset Nat, s.card = size ∧
    (∀ x ∈ s, x < N) ∧ IsDirectedCliqueOn E s

/-- A clique of old vertices all adjacent to a proposed new vertex. -/
def HasNeighbourCliqueBelow
    (E : Nat → Nat → Bool) (N size : Nat)
    (neighbour : Nat → Bool) : Prop :=
  ∃ s : Finset Nat, s.card = size ∧
    (∀ x ∈ s, x < N ∧ neighbour x = true) ∧
    IsDirectedCliqueOn E s

/-- The finite one-point graph extension with prescribed symmetric
adjacency to every old vertex. Its new diagonal is false. -/
def onePointGraphEdge
    (E : Nat → Nat → Bool) (N : Nat) (neighbour : Nat → Bool)
    (x y : Nat) : Bool :=
  if x = N then
    if y < N then neighbour y else false
  else if y = N then
    if x < N then neighbour x else false
  else E x y

theorem onePointGraphEdge_old
    (E : Nat → Nat → Bool) (N : Nat) (neighbour : Nat → Bool)
    (x y : Nat) (hx : x < N) (hy : y < N) :
    onePointGraphEdge E N neighbour x y = E x y := by
  have hxn : x ≠ N := by omega
  have hyn : y ≠ N := by omega
  simp [onePointGraphEdge, hxn, hyn]

theorem onePointGraphEdge_right
    (E : Nat → Nat → Bool) (N : Nat) (neighbour : Nat → Bool)
    (x : Nat) (hx : x < N) :
    onePointGraphEdge E N neighbour x N = neighbour x := by
  have hxn : x ≠ N := by omega
  simp [onePointGraphEdge, hxn, hx]

theorem onePointGraphEdge_left
    (E : Nat → Nat → Bool) (N : Nat) (neighbour : Nat → Bool)
    (x : Nat) (hx : x < N) :
    onePointGraphEdge E N neighbour N x = neighbour x := by
  simp [onePointGraphEdge, hx]

/-- Exact obstruction decomposition: any new clique either is
already an old clique, or consists of the new vertex together
with a clique in its COMPLETE old neighbourhood. -/
theorem onePointGraph_hasClique_iff
    (E : Nat → Nat → Bool) (N ell : Nat)
    (neighbour : Nat → Bool) (hEll : 0 < ell) :
    HasCliqueBelow (onePointGraphEdge E N neighbour) (N+1) ell ↔
      HasCliqueBelow E N ell ∨
      HasNeighbourCliqueBelow E N (ell-1) neighbour := by
  constructor
  · rintro ⟨s, hCard, hBound, hClique⟩
    by_cases hN : N ∈ s
    · right
      refine ⟨s.erase N, ?_, ?_, ?_⟩
      · rw [Finset.card_erase_of_mem hN, hCard]
      · intro x hx
        have hs : x ∈ s := (Finset.mem_erase.mp hx).2
        have hne : x ≠ N := (Finset.mem_erase.mp hx).1
        have hlt : x < N := by
          have h := hBound x hs
          omega
        constructor
        · exact hlt
        · have hEdge := hClique x hs N hN hne
          simpa [onePointGraphEdge_right E N neighbour x hlt] using hEdge
      · intro x hx y hy hxy
        have hsx : x ∈ s := (Finset.mem_erase.mp hx).2
        have hsy : y ∈ s := (Finset.mem_erase.mp hy).2
        have hneX : x ≠ N := (Finset.mem_erase.mp hx).1
        have hneY : y ≠ N := (Finset.mem_erase.mp hy).1
        have hxlt : x < N := by
          have h := hBound x hsx
          omega
        have hylt : y < N := by
          have h := hBound y hsy
          omega
        have hEdge := hClique x hsx y hsy hxy
        simpa [onePointGraphEdge_old E N neighbour x y hxlt hylt] using hEdge
    · left
      have hOld : ∀ x ∈ s, x < N := by
        intro x hx
        have hlt := hBound x hx
        have hne : x ≠ N := by
          intro heq
          subst x
          exact hN hx
        omega
      refine ⟨s, hCard, hOld, ?_⟩
      intro x hx y hy hxy
      have hEdge := hClique x hx y hy hxy
      simpa [onePointGraphEdge_old E N neighbour x y
        (hOld x hx) (hOld y hy)] using hEdge
  · intro h
    rcases h with ⟨s,hCard,hBound,hClique⟩ |
      ⟨s,hCard,hBound,hClique⟩
    · refine ⟨s, hCard, ?_, ?_⟩
      · intro x hx
        have := hBound x hx
        omega
      · intro x hx y hy hxy
        have hEdge := hClique x hx y hy hxy
        simpa [onePointGraphEdge_old E N neighbour x y
          (hBound x hx) (hBound y hy)] using hEdge
    · have hNotN : N ∉ s := by
        intro hn
        have := (hBound N hn).1
        omega
      refine ⟨insert N s, ?_, ?_, ?_⟩
      · have hc : (insert N s).card = s.card + 1 :=
          Finset.card_insert_of_not_mem hNotN
        omega
      · intro x hx
        rcases Finset.mem_insert.mp hx with h | hxS
        · omega
        · have := (hBound x hxS).1
          omega
      · intro x hx y hy hxy
        rcases Finset.mem_insert.mp hx with hxN | hxS
        · subst x
          rcases Finset.mem_insert.mp hy with hyN | hyS
          · exact (hxy hyN.symm).elim
          · have hylt := (hBound y hyS).1
            have hp := (hBound y hyS).2
            simpa [onePointGraphEdge_left E N neighbour y hylt] using hp
        · rcases Finset.mem_insert.mp hy with hyN | hyS
          · subst y
            have hxlt := (hBound x hxS).1
            have hp := (hBound x hxS).2
            simpa [onePointGraphEdge_right E N neighbour x hxlt] using hp
          · have hEdge := hClique x hxS y hyS hxy
            simpa [onePointGraphEdge_old E N neighbour x y
              (hBound x hxS).1 (hBound y hyS).1] using hEdge

/-- Given an already K_ell-free old prefix, checking the whole
neighbourhood for K_(ell-1) is *necessary and sufficient* for a
K_ell-free extension. This includes every mixed parameter/block
clique; no blockwise shortcut is used. -/
theorem onePointGraph_cliqueFree_iff
    (E : Nat → Nat → Bool) (N ell : Nat)
    (neighbour : Nat → Bool) (hEll : 0 < ell)
    (hOld : ¬ HasCliqueBelow E N ell) :
    (¬ HasCliqueBelow (onePointGraphEdge E N neighbour) (N+1) ell) ↔
      ¬ HasNeighbourCliqueBelow E N (ell-1) neighbour := by
  rw [onePointGraph_hasClique_iff E N ell neighbour hEll]
  simp [hOld]

end Kk
