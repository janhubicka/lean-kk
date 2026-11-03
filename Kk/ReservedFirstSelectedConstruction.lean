import Kk.FirstSelectedAfterReserved
import Mathlib.Tactic

/-!
# Construct a genuine reserved clique and its first selected successor

The previous module gives an exact mixed-neighbourhood reduction
when a reserved set of genuine Henson originals has already been
chosen. Here we combine it with the verified Henson left-density
and reserved-original existence theorems.

Given any safe passing column on an earlier original prefix, reserve
a clique of r<ell-1 actual later originals and choose a subsequent
selected original adjacent to exactly the chosen reserved vertices
AND to its prescribed earlier neighbours. All gap vertices receive
zero passing bits. The prescribed column is realized in the
unchanged fixed Henson enumeration.

The theorem covers the first selected original after the newly
reserved block. It is NOT a general resolved-copy theorem: later
selected originals may have already acquired edges to old blocks;
those interactions and full parameter-closed B3 remain unproved.
-/

namespace Kk

/-- From an arbitrary safe old-prefix passing column, construct
actual reserved original indices followed by one genuine selected
original. The new selected vertex joins the entire reserved clique
and realizes the independently prescribed old-column bits.

The complete mixed-neighbourhood certificate is automatically
negative thanks to genuine old-to-reserved nonedges and zero
passing bits on all intervening nonreserved vertices. -/
theorem henson_leftDense_reserve_and_first_selected
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (base r : Nat) (hR : r < ell-1)
    (oldNeighbour : Nat → Bool)
    (hOldCheck :
      finiteNeighbourCliqueCheck E base (ell-1)
        oldNeighbour = false) :
    ∃ (S : Finset Nat) (front v : Nat),
      S.card = r ∧
      (∀ q ∈ S, base ≤ q ∧ q < front) ∧
      IsDirectedCliqueOn E S ∧
      (∀ q ∈ S, ∀ x, x < q → x ∉ S →
        E x q = false ∧ E q x = false) ∧
      front ≤ v ∧
      (∀ x, x < v →
        E x v =
          (if x < front then
            (if x < base then oldNeighbour x else decide (x ∈ S))
           else false) ∧
        E v x =
          (if x < front then
            (if x < base then oldNeighbour x else decide (x ∈ S))
           else false)) := by
  classical
  obtain ⟨S, hCard, hSAfter, hClique, hIso⟩ :=
    henson_leftDense_exists_reserved_originals
      ell hell E hAvoid hDense base r (by omega)
  let front : Nat := max base ((S.sup (fun u : Nat => u)) + 1)
  have hBaseFront : base ≤ front := by
    dsimp [front]
    omega
  have hSFront : ∀ q ∈ S, q < front := by
    intro q hq
    have hSup : q ≤ S.sup (fun u : Nat => u) :=
      Finset.le_sup hq
    dsimp [front]
    omega
  let neighbour : Nat → Bool :=
    fun x => if x < base then oldNeighbour x else decide (x ∈ S)
  have hOnlyS :
      ∀ y, y < front → base ≤ y →
        neighbour y = true → y ∈ S := by
    intro y hy hBaseY hPositive
    have hNot : ¬ y < base := by omega
    simpa [neighbour, hNot] using hPositive
  have hOldC :
      ¬ HasNeighbourCliqueBelow E base (ell-1) oldNeighbour :=
    (finiteNeighbourCliqueCheck_false_iff E base (ell-1)
      oldNeighbour).1 hOldCheck
  have hPrior :
      finiteNeighbourCliqueCheck E base (ell-1)
        neighbour = false := by
    apply (finiteNeighbourCliqueCheck_false_iff
      E base (ell-1) neighbour).2
    rintro ⟨s, hSize, hBounds, hSubClique⟩
    apply hOldC
    refine ⟨s, hSize, ?_, hSubClique⟩
    intro x hx
    obtain ⟨hBelow, hPositive⟩ := hBounds x hx
    refine ⟨hBelow, ?_⟩
    simpa [neighbour, hBelow] using hPositive
  have hIsoForward :
      ∀ q ∈ S, ∀ x, x < q → x ∉ S →
        E x q = false := by
    intro q hq x hx hNot
    exact (hIso q hq x hx hNot).1
  have hSmall : S.card < ell-1 := by omega
  obtain ⟨v, hv, hColumn⟩ :=
    henson_leftDense_first_selected_after_isolated_reserved
      ell hell E hAvoid hDense base front S neighbour
      hBaseFront hSAfter hIsoForward hOnlyS hSmall hPrior
  refine ⟨S, front, v, hCard, ?_, hClique, hIso, hv, ?_⟩
  · intro q hq
    exact ⟨hSAfter q hq, hSFront q hq⟩
  · intro x hx
    simpa only [neighbour] using hColumn x hx

end Kk
