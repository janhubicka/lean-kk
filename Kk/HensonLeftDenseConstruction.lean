import Kk.HensonLeftDensityBridge
import Mathlib.Logic.Equiv.Finset
import Mathlib.Data.Nat.Pairing

/-!
# Existence of a left-dense clique-free presentation

The fair schedule below constructs an actual Boolean graph on `Nat`.
Every complete finite neighbourhood request is visited at arbitrarily
large stages and is accepted exactly when safe. Thus the extra
`OnePointLeftDense` hypothesis of the physical constructors is satisfiable;
it is not being confused with clique-freeness alone or with an arbitrary
enumeration's ordinary extension property.

English proof and prior audit:
`docs/henson_left_dense_construction_20261122.md`.
-/

namespace Kk.LeftDenseConstruction

/-- Every finite set occurs cofinally, via the second pairing coordinate. -/
def scheduledSet (n : Nat) : Finset Nat :=
  (Encodable.decode (α := Finset Nat) (Nat.unpair n).1).getD ∅

theorem scheduledSet_cofinal (S : Finset Nat) (b : Nat) :
    ∃ n, b ≤ n ∧ scheduledSet n = S := by
  refine ⟨Nat.pair (Encodable.encode S) b, Nat.right_le_pair _ _, ?_⟩
  simp [scheduledSet, Nat.unpair_pair, Encodable.encodek]

/-- The entire proposed neighbourhood is checked; a failed request adds
an isolated vertex. Values at indices at or beyond `n` are irrelevant. -/
def safeColumn (ell : Nat) (E : Nat → Nat → Bool) (n : Nat) : Nat → Bool :=
  if finiteNeighbourCliqueCheck E n (ell - 1)
      (fun x => decide (x ∈ scheduledSet n)) = false then
    fun x => decide (x ∈ scheduledSet n)
  else fun _ => false

/-- Stage `n` contains the final graph on the prefix `[0,n)`. -/
def stage (ell : Nat) : Nat → Nat → Nat → Bool
  | 0 => fun _ _ => false
  | n + 1 => onePointGraphEdge (stage ell n) n (safeColumn ell (stage ell n) n)

theorem stage_symmetric (ell n : Nat) :
    ∀ x y, stage ell n x y = stage ell n y x := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro x y
    by_cases hx : x = n <;> by_cases hy : y = n <;>
      simp [stage, onePointGraphEdge, hx, hy, ih]

theorem stage_loopless (ell n : Nat) : ∀ x, stage ell n x x = false := by
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
    intro x
    by_cases hx : x = n <;> simp [stage, onePointGraphEdge, hx, ih]

/-- Later stages leave every old edge unchanged. -/
theorem stage_agrees (ell n m x y : Nat)
    (hnm : n ≤ m) (hx : x < n) (hy : y < n) :
    stage ell m x y = stage ell n x y := by
  induction m with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      rfl
  | succ m ih =>
    by_cases hnm' : n = m + 1
    · subst n; rfl
    · have hn : n ≤ m := by omega
      rw [stage, onePointGraphEdge_old _ m _ x y (by omega) (by omega)]
      exact ih hn

/-- Stabilized adjacency on the countably infinite carrier. -/
def edge (ell x y : Nat) : Bool := stage ell (max x y + 1) x y

theorem edge_agrees (ell n x y : Nat) (hx : x < n) (hy : y < n) :
    edge ell x y = stage ell n x y := by
  unfold edge
  symm
  exact stage_agrees ell (max x y + 1) n x y (by omega) (by omega) (by omega)

theorem edge_symmetric (ell x y : Nat) : edge ell x y = edge ell y x := by
  unfold edge
  rw [max_comm y x]
  exact stage_symmetric ell _ x y

theorem edge_loopless (ell x : Nat) : edge ell x x = false :=
  stage_loopless ell _ x

theorem safeColumn_has_no_neighbour_clique
    (ell : Nat) (hEll : 2 ≤ ell) (E : Nat → Nat → Bool) (n : Nat) :
    ¬ HasNeighbourCliqueBelow E n (ell - 1) (safeColumn ell E n) := by
  unfold safeColumn
  split_ifs with hSafe
  · exact (finiteNeighbourCliqueCheck_false_iff _ _ _ _).mp hSafe
  · apply no_neighbourClique_of_small_neighbour_set
    have hEmpty : oldNeighbourSet n (fun _ => false) = ∅ := by
      simp [oldNeighbourSet]
    rw [hEmpty, Finset.card_empty]
    omega

theorem stage_cliqueFree (ell : Nat) (hEll : 2 ≤ ell) (n : Nat) :
    ¬ HasCliqueBelow (stage ell n) n ell := by
  induction n with
  | zero =>
    rintro ⟨S, hCard, hBound, _⟩
    have hPos : 0 < S.card := by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hPos
    exact Nat.not_lt_zero x (hBound x hx)
  | succ n ih =>
    exact (onePointGraph_cliqueFree_iff _ n ell _ (by omega) ih).2
      (safeColumn_has_no_neighbour_clique ell hEll (stage ell n) n)

/-- Every prefix of the actual infinite graph is clique-free. -/
theorem edge_cliqueFree (ell : Nat) (hEll : 2 ≤ ell) (n : Nat) :
    ¬ HasCliqueBelow (edge ell) n ell := by
  rintro ⟨S, hCard, hBound, hClique⟩
  apply stage_cliqueFree ell hEll n
  refine ⟨S, hCard, hBound, ?_⟩
  intro x hx y hy hxy
  rw [← edge_agrees ell n x y (hBound x hx) (hBound y hy)]
  exact hClique x hx y hy hxy

/-- A safe request over a fixed old prefix remains safe when its exact
finite neighbour set is scheduled later. -/
theorem scheduled_request_safe (ell front n : Nat) (neighbour : Nat → Bool)
    (hFront : front ≤ n)
    (hSchedule : scheduledSet n = oldNeighbourSet front neighbour)
    (hSafe : ¬ HasNeighbourCliqueBelow (edge ell) front (ell - 1) neighbour) :
    ¬ HasNeighbourCliqueBelow (stage ell n) n (ell - 1)
      (fun x => decide (x ∈ scheduledSet n)) := by
  rintro ⟨S, hCard, hBound, hClique⟩
  have hOld : ∀ x ∈ S, x < front ∧ neighbour x = true := by
    intro x hx
    have hMem : x ∈ scheduledSet n := by simpa using (hBound x hx).2
    rw [hSchedule] at hMem
    simpa [oldNeighbourSet] using hMem
  apply hSafe
  refine ⟨S, hCard, hOld, ?_⟩
  intro x hx y hy hxy
  rw [edge_agrees ell n x y (by have := (hOld x hx).1; omega)
    (by have := (hOld y hy).1; omega)]
  exact hClique x hx y hy hxy

/-- Exact zero-tail realization in the constructed presentation. -/
theorem edge_onePointLeftDense (ell : Nat) (hEll : 2 ≤ ell) :
    OnePointLeftDense (edge ell) ell := by
  intro front neighbour hExtension
  have hSafe :
      ¬ HasNeighbourCliqueBelow (edge ell) front (ell - 1) neighbour := by
    intro hClique
    exact hExtension ((onePointGraph_hasClique_iff _ front ell neighbour
      (by omega)).2 (Or.inr hClique))
  obtain ⟨n, hn, hSchedule⟩ :=
    scheduledSet_cofinal (oldNeighbourSet front neighbour) front
  have hCheck : finiteNeighbourCliqueCheck (stage ell n) n (ell - 1)
      (fun x => decide (x ∈ scheduledSet n)) = false :=
    (finiteNeighbourCliqueCheck_false_iff _ _ _ _).2
      (scheduled_request_safe ell front n neighbour hn hSchedule hSafe)
  have hColumn : safeColumn ell (stage ell n) n =
      (fun x => decide (x ∈ scheduledSet n)) := by
    simp [safeColumn, hCheck]
  refine ⟨n, hn, ?_⟩
  intro x hx
  have hVal : decide (x ∈ scheduledSet n) =
      (if x < front then neighbour x else false) := by
    rw [hSchedule]
    by_cases hxf : x < front <;> cases hnx : neighbour x <;>
      simp [oldNeighbourSet, hxf, hnx]
  constructor
  · rw [edge_agrees ell (n + 1) x n (by omega) (by omega), stage,
      onePointGraphEdge_right _ n _ x hx, hColumn]
    exact hVal
  · rw [edge_agrees ell (n + 1) n x (by omega) (by omega), stage,
      onePointGraphEdge_left _ n _ x hx, hColumn]
    exact hVal

/-- The physical constructors' ambient hypotheses are jointly satisfiable
for every permitted clique size. No Ramsey conclusion is part of this result. -/
theorem exists_leftDense_cliqueFree (ell : Nat) (hEll : 2 ≤ ell) :
    ∃ E : Nat → Nat → Bool,
      (∀ x, E x x = false) ∧
      (∀ x y, E x y = E y x) ∧
      (∀ n, ¬ HasCliqueBelow E n ell) ∧ OnePointLeftDense E ell :=
  ⟨edge ell, edge_loopless ell, edge_symmetric ell,
    edge_cliqueFree ell hEll, edge_onePointLeftDense ell hEll⟩

end Kk.LeftDenseConstruction
