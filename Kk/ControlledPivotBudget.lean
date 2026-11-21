import Kk.IntegerAgeSmallFunction
import Kk.FullOriginalInsertionAge
import Mathlib.Tactic

/-!
# Derive controlled-coding budgets at the same nonfree pivot

The English proof and independent adversarial audit were committed first in
`docs/track_b_nonfree_pivot_residual_english_audit_20261121.md`, Section 6.

The controlled positive-support cap and insertion-growth identities imply
the full physical linked-neighbour budget.  The largest admissible support
cannot simply be enlarged by the pivot sort: a proper saturating support
first makes that insertion admissible.  The conclusion is a derived budget,
not an assumed preservation criterion.  All original columns in P are kept.

No auxiliary E/Kpt source, corrected B3, or infinite diary is asserted here.
-/

namespace Kk

/-- A genuine positive age whose value on T is at most ell-2 has a
nonempty saturating sub-support small enough to adjoin one more sort.
This includes the boundary |T|=ell-1 without forming an oversized support. -/
theorem integerGraphAge_controlled_support_witness
    (d ell : Nat) (hell : 2 ≤ ell)
    (F : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell F)
    (T : IntegerGraphSupport d ell) (hCap : F T ≤ ell - 2) :
    ∃ Q : IntegerGraphSupport d ell,
      Q.1 ⊆ T.1 ∧ Q.1.card < ell - 1 ∧ F Q = F T := by
  classical
  by_cases hSmall : T.1.card < ell - 1
  · exact ⟨T, Finset.Subset.refl _, hSmall, rfl⟩
  · have hCard : T.1.card = ell - 1 := by
      have hBound := T.2.2
      omega
    have hValueSmall : F T < T.1.card := by omega
    obtain ⟨Q, hQT, hNe, hValue⟩ :=
      integerGraphAge_small_support_witness d ell F hAge T T
        (Finset.Subset.refl _) hValueSmall
    have hStrict : Q.1 ⊂ T.1 :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hQT, hNe⟩
    have hQCard : Q.1.card < T.1.card := Finset.card_lt_card hStrict
    exact ⟨Q, hQT, by omega, hValue⟩

/-- A pivot's complete bilateral old type identifies its actual linked
common-neighbour pool on an arbitrary finite protected original set.
The enlarged sort set is a plain Finset and need not be admissible. -/
theorem oldSupportCommonNeighbourPool_mutual_pivot {d : Nat}
    (E : Nat → Nat → Bool) (P : Finset Nat)
    (c : Nat → Fin d → Bool) (s : Fin d) (v : Nat)
    (hColumn : ∀ p ∈ P, E p v = c p s ∧ E v p = c p s)
    (S : Finset (Fin d)) :
    mutualLinkedNeighbours E (oldSupportCommonNeighbourPool P c S) v =
      oldSupportCommonNeighbourPool P c (insert s S) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hpPool, hForward, _hReverse⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpP, hBits⟩ := Finset.mem_filter.mp hpPool
    apply Finset.mem_filter.mpr
    refine ⟨hpP, ?_⟩
    intro t ht
    rcases Finset.mem_insert.mp ht with hts | htS
    · subst t
      exact (hColumn p hpP).1.symm.trans hForward
    · exact hBits t htS
  · intro hp
    obtain ⟨hpP, hBits⟩ := Finset.mem_filter.mp hp
    have hAtS := hBits s (Finset.mem_insert_self s S)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hpP, ?_⟩, ?_, ?_⟩
    · intro t ht
      exact hBits t (Finset.mem_insert_of_mem ht)
    · exact (hColumn p hpP).1.trans hAtS
    · exact (hColumn p hpP).2.trans hAtS

/-- Controlled positive-support caps and insertion growth DERIVE the
full linked-neighbour budget for every positive support, including the
largest admissible ones.  F need only be a genuine age below the physical
raw bound; equality with the canonical age is unnecessary for this lemma.

The growth hypothesis quantifies over two already admissible supports,
so it never evaluates F on a set outside its domain.  In a controlled
coding pair X excludes s, and this is exactly the manuscript's condition
for |U|<ell-1.  The singleton and maximum-decomposition axioms are not used. -/
theorem controlledPivot_linked_budget
    (E : Nat → Nat → Bool) (d ell : Nat) (hell : 2 ≤ ell)
    (P : Finset Nat) (c : Nat → Fin d → Bool) (s : Fin d) (v : Nat)
    (hColumn : ∀ p ∈ P, E p v = c p s ∧ E v p = c p s)
    (F : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell F)
    (hBelow : AgeLe F (finiteOldColumnRawBound E ell d P c))
    (X : Finset (Fin d))
    (hCap : ∀ U : IntegerGraphSupport d ell, U.1 ⊆ X → F U ≤ ell - 2)
    (hGrowth : ∀ U V : IntegerGraphSupport d ell,
      U.1 ⊆ X → V.1 = insert s U.1 → F V = F U + 1)
    (T : IntegerGraphSupport d ell) (hTX : T.1 ⊆ X) :
    1 + finiteDirectedCliqueCapacity E
        (mutualLinkedNeighbours E (oldSupportCommonNeighbourPool P c T.1) v)
      + F T ≤ ell - 1 := by
  classical
  obtain ⟨Q, hQT, hQSmall, hQValue⟩ :=
    integerGraphAge_controlled_support_witness d ell hell F hAge T (hCap T hTX)
  have hVCard : (insert s Q.1).card ≤ ell - 1 := by
    have hInsert := Finset.card_insert_le s Q.1
    omega
  let V : IntegerGraphSupport d ell :=
    ⟨insert s Q.1, Finset.insert_nonempty _ _, hVCard⟩
  have hValue : F V = F Q + 1 := hGrowth Q V (hQT.trans hTX) rfl
  have hRaw := hBelow V
  change F V ≤ ell - 1 -
    finiteDirectedCliqueCapacity E (oldSupportCommonNeighbourPool P c V.1) at hRaw
  have hPool :
      mutualLinkedNeighbours E (oldSupportCommonNeighbourPool P c T.1) v ⊆
        oldSupportCommonNeighbourPool P c V.1 := by
    rw [oldSupportCommonNeighbourPool_mutual_pivot E P c s v hColumn]
    intro p hp
    obtain ⟨hpP, hBits⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨hpP, ?_⟩
    intro t ht
    rcases Finset.mem_insert.mp ht with hts | htQ
    · exact hBits t (Finset.mem_insert.mpr (Or.inl hts))
    · exact hBits t (Finset.mem_insert_of_mem (hQT htQ))
  have hCapacity := finiteDirectedCliqueCapacity_mono E _ _ hPool
  rw [hValue, hQValue] at hRaw
  omega

end Kk
