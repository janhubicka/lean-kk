import Kk.TrackFCollapseCliqueFeasibility
import Mathlib.Tactic

/-!
# Track F: private sort labels transfer every global feasible B-clique

English proof and twelve hostile checks were committed BEFORE Lean:
docs/track_f_private_sorted_graph_feasibility_english_audit.md

Each requested abstract vertex receives its own private sort.
Singleton supports need only positive capacity; mixed supports
pull back EXACTLY along the (possibly noninjective) parent map.
This is the genuine full-graph clique condition needed by #355,
not a claim of equality of canonical mixed raw ages.
-/

namespace Kk

/-- If a private sort label is injective on the vertices of a
finite requested graph, and the private-to-parent map recovers
the original sort on those vertices, then all original feasible
directed cliques remain feasible provided singleton private
raw ages are positive and multi-private-sort raw ages are
the exact parent-support pullbacks.

The map of private sorts into parent sorts need NOT be injective.
The private label map itself needs injectivity ONLY below N.
-/
theorem trackFPrivateSort_all_cliques_feasible
    (p d N : Nat)
    (B : Nat → Nat → Bool)
    (σ : Nat → Fin p) (τ : Nat → Fin d)
    (π : Fin d → Fin p)
    (oldRaw : Finset (Fin p) → Nat)
    (newRaw : Finset (Fin d) → Nat)
    (hInj : Set.InjOn τ (↑(Finset.range N) : Set Nat))
    (hParent : ∀ i : Nat, i < N → π (τ i) = σ i)
    (hOne : ∀ i : Fin d, 1 ≤ newRaw {i})
    (hMixed : ∀ S : Finset (Fin d),
      2 ≤ S.card → newRaw S = oldRaw (S.image π))
    (hOld : ∀ C : Finset Nat,
      C ⊆ Finset.range N → C.Nonempty →
        IsDirectedCliqueOn B C →
        C.card ≤ oldRaw (C.image σ)) :
    ∀ C : Finset Nat,
      C ⊆ Finset.range N → C.Nonempty →
        IsDirectedCliqueOn B C →
        C.card ≤ newRaw (C.image τ) := by
  classical
  intro C hC hNonempty hClique
  by_cases hCardOne : C.card = 1
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hCardOne
    subst C
    simpa using hOne (τ i)
  · have hPositive : 0 < C.card :=
      Finset.card_pos.mpr hNonempty
    have hInjC : Set.InjOn τ (↑C : Set Nat) := by
      intro a ha b hb hab
      exact hInj (hC ha) (hC hb) hab
    have hImageCard : (C.image τ).card = C.card :=
      Finset.card_image_iff.mpr hInjC
    have hAtLeastTwo : 2 ≤ (C.image τ).card := by
      omega
    have hImageParent :
        (C.image τ).image π = C.image σ := by
      apply Finset.Subset.antisymm
      · intro j hj
        obtain ⟨t, ht, htj⟩ := Finset.mem_image.mp hj
        obtain ⟨i, hi, hit⟩ := Finset.mem_image.mp ht
        have hiN : i < N := Finset.mem_range.mp (hC hi)
        refine Finset.mem_image.mpr ⟨i, hi, ?_⟩
        calc
          σ i = π (τ i) := (hParent i hiN).symm
          _ = π t := congrArg π hit
          _ = j := htj
      · intro j hj
        obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hj
        have hiN : i < N := Finset.mem_range.mp (hC hi)
        refine Finset.mem_image.mpr
          ⟨τ i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, ?_⟩
        exact (hParent i hiN).trans hij
    calc
      C.card ≤ oldRaw (C.image σ) :=
        hOld C hC hNonempty hClique
      _ = oldRaw ((C.image τ).image π) := by
        rw [hImageParent]
      _ = newRaw (C.image τ) :=
        (hMixed (C.image τ) hAtLeastTwo).symm

end Kk
