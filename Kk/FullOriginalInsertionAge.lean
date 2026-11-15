import Kk.FiniteNeighbourSchedule
import Kk.FiniteOldColumnAge
import Kk.LinkedCliqueCapacityUpdate
import Mathlib.Tactic

/-!
# Track B: exact arbitrary-original updates of the entire old-column age

The English proof and fifteen hostile checks were committed first in
docs/track_b_full_original_insertion_age_english_audit.md.

The *literal* old common-neighbour pool after inserting any original v is
either the old pool or that pool with v. In the latter case its directed-clique
capacity changes by EXACTLY the old-versus-mutual-neighbour max recurrence,
not the cardinality of the selected shadow.

A pointwise all-support mutual-clique budget therefore gives an age-neutral
stage even when the inserted original has positive passing bits. The derived
one-step theorem composes actual K_ell-free safety with raw/canonical age
preservation. This is a conditional finite stage interface: it does not
manufacture a genuine safe selected Henson column, the intended age drop,
Kpt closure/microevents or a common labelled inverse-source orbit.
-/

namespace Kk

/-- A new original joins the common old-neighbour set of U precisely
when it has POSITIVE passing bits to EVERY sort in U. Membership of
old originals is not changed. No freshness assumption is required
for this literal filter identity. -/
theorem oldSupportCommonNeighbourPool_insert_exact
    {d : Nat} (P : Finset Nat) (c : Nat → Fin d → Bool)
    (U : Finset (Fin d)) (v : Nat) :
    oldSupportCommonNeighbourPool (insert v P) c U =
      if (∀ t ∈ U, c v t = true) then
        insert v (oldSupportCommonNeighbourPool P c U)
      else oldSupportCommonNeighbourPool P c U := by
  classical
  by_cases hLive : ∀ t ∈ U, c v t = true
  · ext x
    simp only [oldSupportCommonNeighbourPool, Finset.mem_filter,
      Finset.mem_insert, if_pos hLive]
    constructor
    · rintro ⟨hMem, hAll⟩
      rcases hMem with hEq | hOld
      · exact Or.inl hEq
      · exact Or.inr ⟨hOld, hAll⟩
    · intro hMem
      rcases hMem with hEq | ⟨hOld, hAll⟩
      · subst x
        exact ⟨Or.inl rfl, hLive⟩
      · exact ⟨Or.inr hOld, hAll⟩
  · ext x
    simp only [oldSupportCommonNeighbourPool, Finset.mem_filter,
      Finset.mem_insert, if_neg hLive]
    constructor
    · rintro ⟨hMem, hAll⟩
      rcases hMem with hEq | hOld
      · subst x
        exact False.elim (hLive hAll)
      · exact ⟨hOld, hAll⟩
    · rintro ⟨hOld, hAll⟩
      exact ⟨Or.inr hOld, hAll⟩

/-- Literal full-support raw-age recurrence after inserting a FRESH
base original. An inserted original may have arbitrary old directed
links; their precise two-sided clique capacity occurs in the formula.

The subtraction ell-1 - capacity is NATURAL truncated subtraction.
The formula requires NO isolated-reserved or selected-only hypothesis. -/
theorem finiteOldColumnRawBound_insert_exact
    (E : Nat → Nat → Bool) (ell d : Nat)
    (P : Finset Nat) (c : Nat → Fin d → Bool)
    (U : IntegerGraphSupport d ell) (v : Nat) (hv : v ∉ P) :
    finiteOldColumnRawBound E ell d (insert v P) c U =
      ell - 1 -
        (if (∀ t ∈ U.1, c v t = true) then
          max (finiteDirectedCliqueCapacity E
                (oldSupportCommonNeighbourPool P c U.1))
              (1 + finiteDirectedCliqueCapacity E
                (mutualLinkedNeighbours E
                  (oldSupportCommonNeighbourPool P c U.1) v))
         else finiteDirectedCliqueCapacity E
                (oldSupportCommonNeighbourPool P c U.1)) := by
  classical
  unfold finiteOldColumnRawBound
  rw [oldSupportCommonNeighbourPool_insert_exact]
  by_cases hLive : ∀ t ∈ U.1, c v t = true
  · simp only [if_pos hLive]
    have hvPool : v ∉ oldSupportCommonNeighbourPool P c U.1 := by
      intro hMem
      exact hv (Finset.mem_filter.mp hMem).1
    rw [finiteDirectedCliqueCapacity_insert_eq E
      (oldSupportCommonNeighbourPool P c U.1) v hvPool]
  · simp only [if_neg hLive]

/-- Off an insertion's actual positive future support, all literal
raw old-column ages remain exactly unchanged. -/
theorem finiteOldColumnRawBound_insert_off
    (E : Nat → Nat → Bool) (ell d : Nat)
    (P : Finset Nat) (c : Nat → Fin d → Bool)
    (U : IntegerGraphSupport d ell) (v : Nat) (hv : v ∉ P)
    (hOff : ¬ ∀ t ∈ U.1, c v t = true) :
    finiteOldColumnRawBound E ell d (insert v P) c U =
      finiteOldColumnRawBound E ell d P c U := by
  rw [finiteOldColumnRawBound_insert_exact E ell d P c U v hv]
  simp only [if_neg hOff]
  rfl

/-- Even when the new original is positive on all sorts of U, the
entire literal raw old age stays fixed if extending old common
neighbours by that vertex cannot increase their clique capacity. -/
theorem finiteOldColumnRawBound_insert_no_growth
    (E : Nat → Nat → Bool) (ell d : Nat)
    (P : Finset Nat) (c : Nat → Fin d → Bool)
    (U : IntegerGraphSupport d ell) (v : Nat) (hv : v ∉ P)
    (hLive : ∀ t ∈ U.1, c v t = true)
    (hBudget :
      1 + finiteDirectedCliqueCapacity E
        (mutualLinkedNeighbours E
          (oldSupportCommonNeighbourPool P c U.1) v) ≤
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool P c U.1)) :
    finiteOldColumnRawBound E ell d (insert v P) c U =
      finiteOldColumnRawBound E ell d P c U := by
  rw [finiteOldColumnRawBound_insert_exact E ell d P c U v hv]
  simp only [if_pos hLive]
  rw [max_eq_left hBudget]
  rfl

/-- On a genuinely nonsaturated support, the mutual-clique budget is
also NECESSARY for literal raw-age neutrality. The new maximum
capacity bound (< ell) prevents truncated subtraction from hiding
growth at an already zero raw bound. This is automatic for a
genuinely K_ell-free new original prefix, but the latter is not
constructed here. Canonical age equality alone is weaker. -/
theorem finiteOldColumnRawBound_insert_eq_iff_mutual_budget_of_cap_lt
    (E : Nat → Nat → Bool) (ell d : Nat)
    (P : Finset Nat) (c : Nat → Fin d → Bool)
    (U : IntegerGraphSupport d ell) (v : Nat) (hv : v ∉ P)
    (hLive : ∀ t ∈ U.1, c v t = true)
    (hCapacity :
      max (finiteDirectedCliqueCapacity E
            (oldSupportCommonNeighbourPool P c U.1))
          (1 + finiteDirectedCliqueCapacity E
            (mutualLinkedNeighbours E
              (oldSupportCommonNeighbourPool P c U.1) v)) < ell) :
    (finiteOldColumnRawBound E ell d (insert v P) c U =
      finiteOldColumnRawBound E ell d P c U) ↔
      1 + finiteDirectedCliqueCapacity E
        (mutualLinkedNeighbours E
          (oldSupportCommonNeighbourPool P c U.1) v) ≤
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool P c U.1) := by
  rw [finiteOldColumnRawBound_insert_exact E ell d P c U v hv]
  simp only [if_pos hLive]
  constructor
  · intro hEq
    have hOldLe :
        finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool P c U.1) ≤
        max (finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool P c U.1))
          (1 + finiteDirectedCliqueCapacity E
            (mutualLinkedNeighbours E
              (oldSupportCommonNeighbourPool P c U.1) v)) :=
      le_max_left _ _
    have hNewLe :
        1 + finiteDirectedCliqueCapacity E
          (mutualLinkedNeighbours E
            (oldSupportCommonNeighbourPool P c U.1) v) ≤
        max (finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool P c U.1))
          (1 + finiteDirectedCliqueCapacity E
            (mutualLinkedNeighbours E
              (oldSupportCommonNeighbourPool P c U.1) v)) :=
      le_max_right _ _
    change ell - 1 -
      max (finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool P c U.1))
        (1 + finiteDirectedCliqueCapacity E
          (mutualLinkedNeighbours E
            (oldSupportCommonNeighbourPool P c U.1) v)) =
      ell - 1 - finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool P c U.1) at hEq
    omega
  · intro hBudget
    rw [max_eq_left hBudget]
    rfl

/-- The nonsaturation premise above follows automatically when
the ENTIRE newly enlarged original pool is genuinely K_ell-free.
Therefore, for a positive support, age neutrality is EQUIVALENT to
the true mutual-clique budget at every safe physical stage.

This is raw-age equivalence, not a full corrected B3 or canonical
diary equivalence. -/
theorem finiteOldColumnRawBound_insert_eq_iff_mutual_budget_of_safe_pool
    (E : Nat → Nat → Bool) (ell d : Nat)
    (P : Finset Nat) (c : Nat → Fin d → Bool)
    (U : IntegerGraphSupport d ell) (v : Nat) (hv : v ∉ P)
    (hLive : ∀ t ∈ U.1, c v t = true)
    (hSafe : finitePoolCliqueCheck E ell (insert v P) = false) :
    (finiteOldColumnRawBound E ell d (insert v P) c U =
      finiteOldColumnRawBound E ell d P c U) ↔
      1 + finiteDirectedCliqueCapacity E
        (mutualLinkedNeighbours E
          (oldSupportCommonNeighbourPool P c U.1) v) ≤
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool P c U.1) := by
  classical
  have hPoolSub :
      oldSupportCommonNeighbourPool (insert v P) c U.1 ⊆ insert v P := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hMono := finiteDirectedCliqueCapacity_mono E
    (oldSupportCommonNeighbourPool (insert v P) c U.1)
    (insert v P) hPoolSub
  have hFull :
      finiteDirectedCliqueCapacity E (insert v P) < ell :=
    (finitePoolCliqueCheck_false_iff_capacity_lt
      E ell (insert v P)).mp hSafe
  have hvPool : v ∉ oldSupportCommonNeighbourPool P c U.1 := by
    intro hx
    exact hv (Finset.mem_filter.mp hx).1
  have hExact :
      finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool (insert v P) c U.1) =
        max (finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool P c U.1))
          (1 + finiteDirectedCliqueCapacity E
            (mutualLinkedNeighbours E
              (oldSupportCommonNeighbourPool P c U.1) v)) := by
    rw [oldSupportCommonNeighbourPool_insert_exact]
    simp only [if_pos hLive]
    rw [finiteDirectedCliqueCapacity_insert_eq E
      (oldSupportCommonNeighbourPool P c U.1) v hvPool]
  have hCapacity :
      max (finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool P c U.1))
        (1 + finiteDirectedCliqueCapacity E
          (mutualLinkedNeighbours E
            (oldSupportCommonNeighbourPool P c U.1) v)) < ell := by
    rw [← hExact]
    exact lt_of_le_of_lt hMono hFull
  exact finiteOldColumnRawBound_insert_eq_iff_mutual_budget_of_cap_lt
    E ell d P c U v hv hLive hCapacity

/-- Literal raw old-column ages are antitone under extension of
the original pool, provided the old typed columns are UNCHANGED.
This is weaker than exact support-by-support formulas, but needs
neither freshness nor any hypothesis on E's directed edge atoms. -/
theorem finiteOldColumnRawBound_antitone_old_pool
    (E : Nat → Nat → Bool) (ell d : Nat)
    (P Q : Finset Nat) (c : Nat → Fin d → Bool)
    (U : IntegerGraphSupport d ell)
    (hPQ : P ⊆ Q) :
    finiteOldColumnRawBound E ell d Q c U ≤
      finiteOldColumnRawBound E ell d P c U := by
  classical
  have hCommon :
      oldSupportCommonNeighbourPool P c U.1 ⊆
      oldSupportCommonNeighbourPool Q c U.1 := by
    intro x hx
    obtain ⟨hxP, hAll⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hPQ hxP, hAll⟩
  have hCap := finiteDirectedCliqueCapacity_mono E
    (oldSupportCommonNeighbourPool P c U.1)
    (oldSupportCommonNeighbourPool Q c U.1) hCommon
  unfold finiteOldColumnRawBound
  omega

/-- Local form of the finite-prefix successor identity; avoids relying
on a removed Finset.range_succ name in the pinned Mathlib version. -/
private theorem range_next_eq_insert (b : Nat) :
    Finset.range (b+1) = insert b (Finset.range b) := by
  ext x
  simp only [Finset.mem_range, Finset.mem_insert]
  omega

/-- The special old-prefix version required by a chronological
Henson schedule. Every tested support may have its own mutual
old-neighbour capacity. The SAME c is used at both stages. -/
theorem finiteOldColumnRawBound_next_prefix_exact
    (E : Nat → Nat → Bool) (ell d b : Nat)
    (c : Nat → Fin d → Bool)
    (U : IntegerGraphSupport d ell) :
    finiteOldColumnRawBound E ell d (Finset.range (b+1)) c U =
      ell - 1 -
        (if (∀ t ∈ U.1, c b t = true) then
          max (finiteDirectedCliqueCapacity E
            (oldSupportCommonNeighbourPool (Finset.range b) c U.1))
            (1 + finiteDirectedCliqueCapacity E
              (mutualLinkedNeighbours E
                (oldSupportCommonNeighbourPool (Finset.range b) c U.1) b))
         else finiteDirectedCliqueCapacity E
            (oldSupportCommonNeighbourPool (Finset.range b) c U.1)) := by
  rw [range_next_eq_insert b]
  exact finiteOldColumnRawBound_insert_exact E ell d
    (Finset.range b) c U b (by simp)

/-- A nonzero future passing column is permitted at a RAW-age-neutral
original stage if its capacity increment fits inside the previous
true clique capacity on EVERY positively seen nonempty support. -/
theorem finiteOldColumnRawBound_next_prefix_eq_of_mutual_budgets
    (E : Nat → Nat → Bool) (ell d b : Nat)
    (c : Nat → Fin d → Bool)
    (hBudget : ∀ U : IntegerGraphSupport d ell,
      (∀ t ∈ U.1, c b t = true) →
      1 + finiteDirectedCliqueCapacity E
        (mutualLinkedNeighbours E
          (oldSupportCommonNeighbourPool (Finset.range b) c U.1) b) ≤
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b) c U.1)) :
    finiteOldColumnRawBound E ell d (Finset.range (b+1)) c =
      finiteOldColumnRawBound E ell d (Finset.range b) c := by
  funext U
  rw [range_next_eq_insert b]
  by_cases hLive : ∀ t ∈ U.1, c b t = true
  · exact finiteOldColumnRawBound_insert_no_growth E ell d
      (Finset.range b) c U b (by simp) hLive (hBudget U hLive)
  · exact finiteOldColumnRawBound_insert_off E ell d
      (Finset.range b) c U b (by simp) hLive

/-- The complete CANONICAL integer graph-age function also stays
fixed when the literal raw ages agree. No converse from canonical
equality to raw equality is used. -/
theorem integerGraphAgeCanonical_next_prefix_eq_of_mutual_budgets
    (E : Nat → Nat → Bool) (ell d b : Nat)
    (c : Nat → Fin d → Bool)
    (hBudget : ∀ U : IntegerGraphSupport d ell,
      (∀ t ∈ U.1, c b t = true) →
      1 + finiteDirectedCliqueCapacity E
        (mutualLinkedNeighbours E
          (oldSupportCommonNeighbourPool (Finset.range b) c U.1) b) ≤
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b) c U.1)) :
    integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range (b+1)) c) =
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range b) c) := by
  rw [finiteOldColumnRawBound_next_prefix_eq_of_mutual_budgets
    E ell d b c hBudget]

/-- One CONDITIONAL physical stage preservation principle:
the actual full old-neighbourhood checker certifies forbidden-clique
safety while the independent all-support mutual budget certifies
exact raw+canonical age neutrality.

There is no claim that the canonical resolved diary supplies these
two certificates at every stage, or that Algorithm 5.4 I3/B3 tests
are unchanged when the ordinary old graph age is unchanged. -/
theorem actual_original_stage_preserves_free_and_all_support_age
    (E : Nat → Nat → Bool) (ell d b : Nat)
    (hEll : 0 < ell)
    (hSym : ∀ x y, E x y = E y x)
    (hLoops : ∀ x, E x x = false)
    (c : Nat → Fin d → Bool)
    (hOld : ¬ HasCliqueBelow E b ell)
    (hNext : finiteNeighbourCliqueCheck E b (ell-1)
      (fun x => E x b) = false)
    (hBudget : ∀ U : IntegerGraphSupport d ell,
      (∀ t ∈ U.1, c b t = true) →
      1 + finiteDirectedCliqueCapacity E
        (mutualLinkedNeighbours E
          (oldSupportCommonNeighbourPool (Finset.range b) c U.1) b) ≤
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b) c U.1)) :
    (¬ HasCliqueBelow E (b+1) ell) ∧
    (finiteOldColumnRawBound E ell d (Finset.range (b+1)) c =
      finiteOldColumnRawBound E ell d (Finset.range b) c) ∧
    (integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range (b+1)) c) =
     integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hBad
    rcases (hasCliqueBelow_succ_iff_old_or_neighbour
      E b ell hEll hSym hLoops).mp hBad with hPrior | hFresh
    · exact hOld hPrior
    · exact ((finiteNeighbourCliqueCheck_false_iff E b (ell-1)
        (fun x => E x b)).mp hNext) hFresh
  · exact finiteOldColumnRawBound_next_prefix_eq_of_mutual_budgets
      E ell d b c hBudget
  · exact integerGraphAgeCanonical_next_prefix_eq_of_mutual_budgets
      E ell d b c hBudget

#print axioms Kk.oldSupportCommonNeighbourPool_insert_exact
#print axioms Kk.finiteOldColumnRawBound_insert_exact
#print axioms Kk.finiteOldColumnRawBound_insert_off
#print axioms Kk.finiteOldColumnRawBound_insert_no_growth
#print axioms Kk.finiteOldColumnRawBound_insert_eq_iff_mutual_budget_of_cap_lt
#print axioms Kk.finiteOldColumnRawBound_insert_eq_iff_mutual_budget_of_safe_pool
#print axioms Kk.finiteOldColumnRawBound_antitone_old_pool
#print axioms Kk.finiteOldColumnRawBound_next_prefix_exact
#print axioms Kk.finiteOldColumnRawBound_next_prefix_eq_of_mutual_budgets
#print axioms Kk.integerGraphAgeCanonical_next_prefix_eq_of_mutual_budgets
#print axioms Kk.actual_original_stage_preserves_free_and_all_support_age

end Kk
