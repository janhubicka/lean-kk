import Kk.IsolatedBlockContinuationAge
import Mathlib.Tactic

/-!
# Exact capacity on a supported future pool equals ALL clique-witness bounds

The English proof and adversarial audit were committed BEFORE this file in
\`docs/clique_support_all_witnesses_english_audit.md\`.

These statements are about any finite directed L graph W and any sort map
Nat → Fin d. They quantify over every directed clique witness s ⊆ W,
not merely one chosen realized top-generation future clique.
The W graph itself need not be K_ell-free; that separate age test remains
required in the four-pool gluing theorem.
-/

namespace Kk

/-- The exact clique-capacity condition on the future vertices of
sorts in T is equivalent to its inequality on the T-part of EVERY
clique witness of W, including the empty clique and empty T-part.
Neither W nor the selected part U is required to be a clique. -/
theorem finiteCliqueSupportCapacity_iff_all_witnesses
    {d : Nat} (E : Nat → Nat → Bool) (W : Finset Nat)
    (sort : Nat → Fin d) (T : Finset (Fin d))
    (a ell : Nat) :
    a + finiteDirectedCliqueCapacity E
      (W.filter (fun w => sort w ∈ T)) < ell ↔
    ∀ s : Finset Nat, s ⊆ W → IsDirectedCliqueOn E s →
      a + (s.filter (fun w => sort w ∈ T)).card < ell := by
  classical
  let U : Finset Nat := W.filter (fun w => sort w ∈ T)
  constructor
  · intro hBudget s hsW hsClique
    have hsU : s.filter (fun w => sort w ∈ T) ⊆ U := by
      intro x hx
      obtain ⟨hxS,hxT⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hsW hxS,hxT⟩
    have hsFilteredClique : IsDirectedCliqueOn E
        (s.filter (fun w => sort w ∈ T)) := by
      intro x hx y hy hxy
      exact hsClique x (Finset.mem_filter.mp hx).1
        y (Finset.mem_filter.mp hy).1 hxy
    have hBound := directedClique_card_le_capacity E U
      (s.filter (fun w => sort w ∈ T)) hsU hsFilteredClique
    change a + finiteDirectedCliqueCapacity E U < ell at hBudget
    omega
  · intro hAll
    obtain ⟨s,hsU,hsClique,hsCard⟩ :=
      finiteDirectedCliqueCapacity_attained E U
    have hsW : s ⊆ W := by
      intro x hx
      exact (Finset.mem_filter.mp (hsU hx)).1
    have hFilterEq : s.filter (fun w => sort w ∈ T) = s := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · exact And.left
      · intro hx
        exact ⟨hx,(Finset.mem_filter.mp (hsU hx)).2⟩
    have hBound := hAll s hsW hsClique
    rw [hFilterEq, hsCard] at hBound
    exact hBound

/-- The same equivalence in the exact raw clique-bound form.
The condition a<ell is ESSENTIAL for Nat subtraction (ell-1-a). -/
theorem finiteCliqueSupportCapacity_raw_iff_all_witnesses
    {d : Nat} (E : Nat → Nat → Bool) (W : Finset Nat)
    (sort : Nat → Fin d) (T : Finset (Fin d))
    (a ell : Nat) (ha : a < ell) :
    finiteDirectedCliqueCapacity E (W.filter (fun w => sort w ∈ T)) ≤
      ell - 1 - a ↔
    ∀ s : Finset Nat, s ⊆ W → IsDirectedCliqueOn E s →
      (s.filter (fun w => sort w ∈ T)).card ≤ ell - 1 - a := by
  have hBudget := finiteCliqueSupportCapacity_iff_all_witnesses
    E W sort T a ell
  constructor
  · intro hRaw s hs hc
    have hBound : a + finiteDirectedCliqueCapacity E
        (W.filter (fun w => sort w ∈ T)) < ell := by omega
    have h := hBudget.mp hBound s hs hc
    omega
  · intro hAll
    have hBound : a + finiteDirectedCliqueCapacity E
        (W.filter (fun w => sort w ∈ T)) < ell := by
      apply hBudget.mpr
      intro s hs hc
      have h := hAll s hs hc
      omega
    omega

#print axioms finiteCliqueSupportCapacity_iff_all_witnesses
#print axioms finiteCliqueSupportCapacity_raw_iff_all_witnesses

end Kk
