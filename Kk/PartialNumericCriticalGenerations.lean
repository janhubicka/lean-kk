import Kk.PartialNumericForbiddenSharpStability
import Mathlib.Tactic

/-!
# Track A: finite ordinary-L raw event schedule of a genuine Henson block

English-first audit in
  docs/track_a_critical_generation_schedule_english_audit_20261119.md

The same genuine original graph E, same b and same later top-original
family j are fixed throughout. This schedule records ordinary binary L
raw support events ONLY. It deliberately does not infer dependent Kpt
I1/I2/I3, complete L+/E crossings or parameter-closed (B3).
-/

namespace Kk

open SuccessorTree.V10

/-- The old original common-neighbour clique capacity of support U. -/
noncomputable def trackAOldCapacity
    {d ell : Nat} (E : Nat → Nat → Bool)
    (b : Nat) (j : Fin d → Nat)
    (U : IntegerGraphSupport d ell) : Nat :=
  finiteDirectedCliqueCapacity E
    (oldSupportCommonNeighbourPool (Finset.range b)
      (fun i t => E i (j t)) U.1)

/-- A support is *critical* for the current original b when its
true b-column is positive and linking b to the existing original
pool preserves the maximum clique capacity. -/
def trackACriticalSupport
    {d ell : Nat} (E : Nat → Nat → Bool)
    (b : Nat) (j : Fin d → Nat)
    (U : IntegerGraphSupport d ell) : Prop :=
  (∀ t ∈ U.1, E b (j t) = true) ∧
  finiteDirectedCliqueCapacity E
    ((oldSupportCommonNeighbourPool (Finset.range b)
      (fun i t => E i (j t)) U.1).filter
        (fun i => E i b = true)) =
  trackAOldCapacity E b j U

/-- Entire finite support-derived raw-event schedule for one
genuine Henson original block. A support U contributes the unique
candidate generation cap_E(P_U), if it is critical. Multiple
supports can contribute the same generation. -/
noncomputable def trackACriticalGenerations
    {d : Nat} (ell : Nat) (E : Nat → Nat → Bool)
    (b : Nat) (j : Fin d → Nat) : Finset Nat := by
  classical
  exact ((Finset.univ : Finset (IntegerGraphSupport d ell)).filter
    (trackACriticalSupport E b j)).image
      (trackAOldCapacity E b j)

/-- Literal finite-membership characterization: no hypothetical
diary witness, closure or relative age is substituted for a
genuine original common-neighbour capacity. -/
theorem mem_trackACriticalGenerations_iff
    {d ell : Nat} (E : Nat → Nat → Bool)
    (b : Nat) (j : Fin d → Nat) (p : Nat) :
    p ∈ trackACriticalGenerations ell E b j ↔
      ∃ U : IntegerGraphSupport d ell,
        trackACriticalSupport E b j U ∧
        trackAOldCapacity E b j U = p := by
  classical
  simp only [trackACriticalGenerations, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and]

/-- The complete ACTUAL ordinary-L raw profile changes across
two partial cuts precisely when the finite critical-generation
schedule intersects their half-open interval [g,h). This is NOT
an iff for a canonical *cover*, full Kpt interestingness or B3. -/
theorem trackA_henson_raw_change_iff_critical_generation
    {d : Nat} (E : Nat → Nat → Bool)
    (ell : Nat) (hell : 2 ≤ ell)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (k b g h M : Nat) (hgh : g ≤ h) (hh : h ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t) :
    finiteNumericHPartialActualRawAt E ell k b h M j ≠
      finiteNumericHPartialActualRawAt E ell k b g M j ↔
    ∃ p : Nat,
      p ∈ trackACriticalGenerations ell E b j ∧ g ≤ p ∧ p < h := by
  classical
  rw [trackA_henson_raw_function_change_iff_exists_support
    E ell hell hAvoid k b g h M hgh hh j hj]
  constructor
  · rintro ⟨U,hEligible,hCap,hCut,hLater⟩
    let p := trackAOldCapacity E b j U
    refine ⟨p, (mem_trackACriticalGenerations_iff (ell := ell) E b j p).2
      ⟨U, ?_, rfl⟩, ?_, ?_⟩
    · exact ⟨hEligible,hCap⟩
    · exact hCut
    · exact hLater
  · rintro ⟨p,hMem,hCut,hLater⟩
    obtain ⟨U,hCrit,hEq⟩ :=
      (mem_trackACriticalGenerations_iff (ell := ell) E b j p).1 hMem
    refine ⟨U,hCrit.1,hCrit.2,?_,?_⟩
    · change g ≤ trackAOldCapacity E b j U
      omega
    · change trackAOldCapacity E b j U < h
      omega


/-- Under genuine normalized Henson K_ell-freeness, EVERY critical
ordinary-L event generation is strictly before ell-2. The proof
adjoins two distinct real original vertices to an actual capacity-
attaining old original clique, not to a graph-age shadow. -/
theorem trackA_henson_critical_generation_lt_ell_sub_two
    {d : Nat} (E : Nat → Nat → Bool)
    (ell : Nat) (hell : 2 ≤ ell)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (b : Nat) (j : Fin d → Nat)
    (hj : ∀ t, b < j t)
    (p : Nat) (hp : p ∈ trackACriticalGenerations ell E b j) :
    p < ell - 2 := by
  classical
  obtain ⟨U,hCrit,hEq⟩ :=
    (mem_trackACriticalGenerations_iff (ell := ell) E b j p).1 hp
  let P : Finset Nat :=
    oldSupportCommonNeighbourPool (Finset.range b)
      (fun i t => E i (j t)) U.1
  let S : Finset Nat := P.filter (fun i => E i b = true)
  obtain ⟨t,ht⟩ := U.2.1
  have hBefore : ∀ x ∈ S, x < b := by
    intro x hx
    exact Finset.mem_range.mp
      (Finset.mem_filter.mp
        ((Finset.mem_filter.mp hx).1)).1
  have hLinkB : ∀ x ∈ S, E x b = true := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hLinkT : ∀ x ∈ S, E x (j t) = true := by
    intro x hx
    exact (Finset.mem_filter.mp
      ((Finset.mem_filter.mp hx).1)).2 t ht
  have hFree : finitePoolCliqueCheck E ell
      (insert (j t) (insert b S)) = false :=
    trackA_finite_pool_free_of_henson ell hell E hAvoid _
  have hBudget := trackA_linked_clique_capacity_two_vertex_budget
    E (hensonForbiddenFamily_symmetric ell hell E hAvoid)
    ell b (j t) S hBefore (hj t)
    hLinkB hLinkT (hCrit.1 t ht) hFree
  have hCap : finiteDirectedCliqueCapacity E S =
      finiteDirectedCliqueCapacity E P := hCrit.2
  have hP : finiteDirectedCliqueCapacity E P = p := hEq
  omega

/-- The number of distinct ordinary-L raw event generations
inside a genuine Henson original block is at most ell-2,
independently of the number d of labelled future sorts. -/
theorem trackA_henson_critical_generation_card_le
    {d : Nat} (E : Nat → Nat → Bool)
    (ell : Nat) (hell : 2 ≤ ell)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (b : Nat) (j : Fin d → Nat)
    (hj : ∀ t, b < j t) :
    (trackACriticalGenerations ell E b j).card ≤ ell - 2 := by
  classical
  have hSub : trackACriticalGenerations ell E b j ⊆
      Finset.range (ell - 2) := by
    intro p hp
    exact Finset.mem_range.mpr
      (trackA_henson_critical_generation_lt_ell_sub_two
        E ell hell hAvoid b j hj p hp)
  have hCard := Finset.card_le_card hSub
  simpa using hCard

#print axioms Kk.trackA_henson_critical_generation_lt_ell_sub_two
#print axioms Kk.trackA_henson_critical_generation_card_le
#print axioms Kk.mem_trackACriticalGenerations_iff
#print axioms Kk.trackA_henson_raw_change_iff_critical_generation

end Kk
