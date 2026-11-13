import Kk.IntegerAgeCoverSupport
import Mathlib.Tactic

/-!
# Track F: existence + uniqueness of the essential support of a cover

For genuine finite K_ell integer-witness graph ages F' ⋖ F,
the set of changed nonempty admissible supports is nonempty and finite.
A support of least cardinality is inclusion-minimal; the previously
verified Kk.integerGraphAgeCover_minimal_changed_unique then shows
this changed support is uniquely inclusion-minimal.

This fills the existence part of manuscript Lem:Consecutive(2);
the old Lean theorem supplied uniqueness only. Neither the one-step
cover drop nor the full diary bijection is claimed.
-/

namespace Kk

/-- A genuine graph-age cover has an inclusion-minimal nonempty
changed support. The existence proof uses finite support size and
does NOT use the existing uniqueness lemma. -/
theorem trackFCover_exists_minimal_changed
    (d ell : Nat)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper) :
    ∃ T : IntegerGraphSupport d ell,
      lower T < upper T ∧
      (∀ U : IntegerGraphSupport d ell,
        U.1 ⊆ T.1 → U.1 ≠ T.1 → lower U = upper U) := by
  classical
  have hSome : ∃ T : IntegerGraphSupport d ell,
      lower T < upper T := by
    by_contra hNone
    have hEq : lower = upper := by
      funext U
      have hLE : lower U ≤ upper U := hCover.le U
      have hNot : ¬ lower U < upper U := by
        intro hLT
        exact hNone ⟨U, hLT⟩
      omega
    exact hCover.strict hEq
  let changed : Finset (IntegerGraphSupport d ell) :=
    Finset.univ.filter (fun U => lower U < upper U)
  have hChangedNon : changed.Nonempty := by
    obtain ⟨U,hU⟩ := hSome
    exact ⟨U, Finset.mem_filter.mpr ⟨Finset.mem_univ U, hU⟩⟩
  let cards : Finset Nat := changed.image (fun U => U.1.card)
  have hCardsNon : cards.Nonempty := by
    obtain ⟨U,hU⟩ := hChangedNon
    exact ⟨U.1.card, Finset.mem_image.mpr ⟨U,hU,rfl⟩⟩
  obtain ⟨T,hTmem,hTcard⟩ :=
    Finset.mem_image.mp (Finset.min'_mem cards hCardsNon)
  have hTchanged : lower T < upper T :=
    (Finset.mem_filter.mp hTmem).2
  refine ⟨T,hTchanged,?_⟩
  intro U hUT hUNe
  by_contra hNotEq
  have hUchanged : lower U < upper U := by
    have hLE : lower U ≤ upper U := hCover.le U
    omega
  have hUmem : U ∈ changed :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ U, hUchanged⟩
  have hUcardmem : U.1.card ∈ cards :=
    Finset.mem_image.mpr ⟨U,hUmem,rfl⟩
  have hLower : cards.min' hCardsNon ≤ U.1.card := by
    exact Finset.min'_le cards U.1.card hUcardmem
  have hStrict : U.1 ⊂ T.1 :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hUT, hUNe⟩
  have hCardStrict : U.1.card < T.1.card :=
    Finset.card_lt_card hStrict
  omega

/-- A genuine K_ell graph-age cover has *exactly one* inclusion-minimal
changed support. Existence is the new finite-cardinality argument;
uniqueness invokes the already verified canonical-locality theorem
for genuine integer-witness graph-age covers. -/
theorem trackFCover_unique_minimal_changed
    (d ell : Nat) (hell : 0 < ell)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper) :
    ∃! T : IntegerGraphSupport d ell,
      lower T < upper T ∧
      (∀ U : IntegerGraphSupport d ell,
        U.1 ⊆ T.1 → U.1 ≠ T.1 → lower U = upper U) := by
  obtain ⟨T,hTchanged,hTminimal⟩ :=
    trackFCover_exists_minimal_changed d ell lower upper hCover
  refine ⟨T,⟨hTchanged,hTminimal⟩,?_⟩
  intro S hS
  exact integerGraphAgeCover_minimal_changed_unique
    d ell hell lower upper hCover S T
    hS.1 hTchanged hS.2 hTminimal

end Kk
