import Kk.FiniteNeighbourCertificates
import Mathlib.Tactic

/-!
# Stagewise finite certificates for an entire K_ell-free original schedule

A proposed resolved-copy construction chooses the adjacency of each
new original to all previously enumerated originals and dependent
parameters. The one-point criterion and the executable finite test
are now available. This module proves their inductive composition.

For a fixed symmetric, loop-free Boolean graph E and ell>0, the
whole first N vertices are K_ell-free if and only if, at EVERY stage
n<N, the complete old-neighbourhood certificate for the adjacency
of the new vertex n is negative.

This does not assert that the manuscript's proposed schedule
actually passes those checks, or that Algorithm 5.4 B3 closure
is determined by the selected graph-age record.
-/

namespace Kk

/-- Graphs agreeing on every ordered pair inside a finite prefix
have exactly the same directed cliques in that prefix. -/
theorem hasCliqueBelow_congr_on_prefix
    (E F : Nat → Nat → Bool) (N ell : Nat)
    (hAgree : ∀ x y, x < N → y < N → E x y = F x y) :
    HasCliqueBelow E N ell ↔ HasCliqueBelow F N ell := by
  constructor
  · rintro ⟨s, hCard, hBound, hClique⟩
    refine ⟨s, hCard, hBound, ?_⟩
    intro x hx y hy hxy
    calc
      F x y = E x y := (hAgree x y (hBound x hx) (hBound y hy)).symm
      _ = true := hClique x hx y hy hxy
  · rintro ⟨s, hCard, hBound, hClique⟩
    refine ⟨s, hCard, hBound, ?_⟩
    intro x hx y hy hxy
    calc
      E x y = F x y := hAgree x y (hBound x hx) (hBound y hy)
      _ = true := hClique x hx y hy hxy

/-- In a symmetric loop-free graph, the abstract one-point graph
built from the old prefix and the true n-th neighbour column
agrees with E on every pair below n+1. -/
theorem onePointGraphEdge_agrees_on_prefix
    (E : Nat → Nat → Bool) (N : Nat)
    (hSym : ∀ x y, E x y = E y x)
    (hLoops : ∀ x, E x x = false)
    (x y : Nat) (hx : x < N+1) (hy : y < N+1) :
    onePointGraphEdge E N (fun u => E u N) x y = E x y := by
  by_cases hxn : x = N
  · subst x
    by_cases hyn : y = N
    · subst y
      simp [onePointGraphEdge, hLoops N]
    · have hylt : y < N := by omega
      calc
        onePointGraphEdge E N (fun u => E u N) N y = E y N :=
          onePointGraphEdge_left E N (fun u => E u N) y hylt
        _ = E N y := hSym y N
  · have hxlt : x < N := by omega
    by_cases hyn : y = N
    · subst y
      exact onePointGraphEdge_right E N (fun u => E u N) x hxlt
    · have hylt : y < N := by omega
      exact onePointGraphEdge_old E N (fun u => E u N) x y hxlt hylt

/-- Every forbidden K_ell in a symmetric loop-free original
prefix either existed before the last insertion or arose from
a clique in the full old neighbourhood of that new vertex. -/
theorem hasCliqueBelow_succ_iff_old_or_neighbour
    (E : Nat → Nat → Bool) (N ell : Nat)
    (hEll : 0 < ell)
    (hSym : ∀ x y, E x y = E y x)
    (hLoops : ∀ x, E x x = false) :
    HasCliqueBelow E (N+1) ell ↔
      HasCliqueBelow E N ell ∨
      HasNeighbourCliqueBelow E N (ell-1) (fun u => E u N) := by
  have hEq := hasCliqueBelow_congr_on_prefix
    (onePointGraphEdge E N (fun u => E u N)) E
    (N+1) ell
    (fun x y hx hy =>
      onePointGraphEdge_agrees_on_prefix E N hSym hLoops x y hx hy)
  exact hEq.symm.trans
    (onePointGraph_hasClique_iff E N ell (fun u => E u N) hEll)

/-- A complete finite original-prefix schedule is K_ell-free
exactly when ALL previous stages have negative executable
full-neighbourhood certificates.

This is the useful induction principle for a future resolved-copy
schedule. The assumptions require the *actual* symmetric and loop-free
original adjacency table, not the selected-front age shadow. -/
theorem cliqueFree_prefix_iff_all_finite_neighbour_certificates
    (E : Nat → Nat → Bool) (ell N : Nat)
    (hEll : 0 < ell)
    (hSym : ∀ x y, E x y = E y x)
    (hLoops : ∀ x, E x x = false) :
    (¬ HasCliqueBelow E N ell) ↔
      (∀ n, n < N →
        finiteNeighbourCliqueCheck E n (ell-1) (fun u => E u n) = false) := by
  induction N with
  | zero =>
    constructor
    · intro _ n hn
      omega
    · intro _
      exact no_clique_below_of_small_carrier E 0 ell hEll
  | succ N ih =>
    have hStep := hasCliqueBelow_succ_iff_old_or_neighbour
      E N ell hEll hSym hLoops
    constructor
    · intro hGood n hn
      have hNoOld : ¬ HasCliqueBelow E N ell := by
        intro hBad
        exact hGood (hStep.mpr (Or.inl hBad))
      have hNoNew :
          ¬ HasNeighbourCliqueBelow E N (ell-1)
            (fun u => E u N) := by
        intro hBad
        exact hGood (hStep.mpr (Or.inr hBad))
      by_cases hlt : n < N
      · exact (ih.mp hNoOld) n hlt
      · have hnEq : n = N := by omega
        subst n
        exact (finiteNeighbourCliqueCheck_false_iff E N (ell-1)
          (fun u => E u N)).2 hNoNew
    · intro hChecks hBad
      have hNoOld : ¬ HasCliqueBelow E N ell :=
        ih.mpr (fun n hn => hChecks n (by omega))
      have hNoNew :
          ¬ HasNeighbourCliqueBelow E N (ell-1)
            (fun u => E u N) :=
        (finiteNeighbourCliqueCheck_false_iff E N (ell-1)
          (fun u => E u N)).1 (hChecks N (by omega))
      rcases hStep.mp hBad with hPrev | hNew
      · exact hNoOld hPrev
      · exact hNoNew hNew

end Kk
