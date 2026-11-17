import Kk.TrackFCollapseMixedOccupancy
import Kk.TrackFCollapseCliqueFeasibility
import Kk.TrackFDisjointDaughterMarkers
import Mathlib.Tactic

/-!
# Track F: physical full-support feasibility for mixed daughter occupancy

English proof and hostile audit committed BEFORE Lean:
docs/track_f_physical_collapse_english_audit.md

All old and fresh neighbourhoods come from the ACTUAL finite
chronological ordinary-graph edge table, not a published diary
definition. Newly split daughters may each carry at most one
selected clique vertex; untouched lower-rank sorts can carry
several, according to their unchanged old singleton capacities.

This closes one FINITE combinatorial implication of the proposed
richness induction. It does not construct the rank-large daughter
fibres or synchronize source and target types under an embedding.
-/

namespace Kk

/-- Genuine Henson graph common-neighbour pools and raw ages
make the corrected mixed-occupancy daughter-to-parent clique
transfer fully physical.

The only unproved application inputs remaining are displayed
explicitly: actual fresh disjoint marker sets with zero markers
on untouched sorts, positive singleton bounds on newly split
daughters, and the original parent-clique feasibility of B.

No arbitrary mixed raw equality or untouched singleton bound
is assumed: both are DERIVED from the actual old-neighbour sets. -/
theorem trackFPhysicalCollapse_cliqueFeasible
    (d p ell m n : Nat) (hmn : m ≤ n)
    (E : Nat → Nat → Bool)
    (π : Fin d → Fin p)
    (U : Fin p → Finset Nat)
    (V : Fin d → Finset Nat)
    (hParentBelow : ∀ a x, x ∈ U a → x < m)
    (hFresh : ∀ i x, x ∈ V i → m ≤ x ∧ x < n)
    (hDisjoint : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (B : Finset Nat) (sort : Nat → Fin d)
    (newDaughters : Finset (Fin d))
    (hOldFeasible : ∀ T : Finset (Fin p), T.Nonempty →
      (B.filter (fun x => π (sort x) ∈ T)).card ≤
        trackFCommonRawAge p ell m E U T)
    (hNewOne : ∀ i ∈ newDaughters,
      (B.filter (fun x => sort x = i)).card ≤ 1)
    (hNewPositive : ∀ i ∈ newDaughters,
      1 ≤ trackFCommonRawAge d ell n E
        (trackFAddDisjointMarkers d (fun j => U (π j)) V) {i})
    (hUntouchedZero : ∀ i : Fin d, i ∉ newDaughters → V i = ∅) :
    ∀ S : Finset (Fin d), S.Nonempty →
      (B.filter (fun x => sort x ∈ S)).card ≤
        trackFCommonRawAge d ell n E
          (trackFAddDisjointMarkers d (fun j => U (π j)) V) S := by
  classical
  let oldRaw : Finset (Fin p) → Nat :=
    fun T => trackFCommonRawAge p ell m E U T
  let newRaw : Finset (Fin d) → Nat :=
    fun S => trackFCommonRawAge d ell n E
      (trackFAddDisjointMarkers d (fun j => U (π j)) V) S
  have hBelowPull : ∀ i x, x ∈ U (π i) → x < m := by
    intro i x hx
    exact hParentBelow (π i) x hx
  apply trackFCollapse_split_untouched_preserve_raw
    d p π sort B newDaughters oldRaw newRaw
  · intro T hT
    exact hOldFeasible T hT
  · exact hNewOne
  · exact hNewPositive
  · intro i hi
    have hNewPool :
        trackFCommonNeighbourPool d n
          (trackFAddDisjointMarkers d (fun j => U (π j)) V) {i} =
          U (π i) := by
      calc
        trackFCommonNeighbourPool d n
            (trackFAddDisjointMarkers d (fun j => U (π j)) V) {i} =
          U (π i) ∪ V i :=
            trackFCommonNeighbourPool_disjoint_singleton
              d m n hmn (fun j => U (π j)) V hBelowPull hFresh i
        _ = U (π i) := by simp [hUntouchedZero i hi]
    have hOldPool :
        trackFCommonNeighbourPool p m U {π i} = U (π i) :=
      trackFCommonNeighbourPool_singleton p m U hParentBelow (π i)
    have heq : oldRaw {π i} = newRaw {i} := by
      change
        ell - 1 - finiteDirectedCliqueCapacity E
          (trackFCommonNeighbourPool p m U {π i}) =
        ell - 1 - finiteDirectedCliqueCapacity E
          (trackFCommonNeighbourPool d n
            (trackFAddDisjointMarkers d (fun j => U (π j)) V) {i})
      rw [hOldPool, hNewPool]
    exact heq.le
  · intro S hCard
    have hNonempty : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i, hi⟩ := hNonempty
    have hTwo : ∃ i ∈ S, ∃ j ∈ S, i ≠ j := by
      by_contra hNo
      have hSub : S ⊆ {i} := by
        intro j hj
        have hji : j = i := by
          by_contra hne
          exact hNo ⟨j, hj, i, hi, hne⟩
        simpa [hji]
      have hLe : S.card ≤ 1 := by
        calc
          S.card ≤ ({i} : Finset (Fin d)).card :=
            Finset.card_le_card hSub
          _ = 1 := by simp
      omega
    exact trackFCommonRawAge_disjoint_collapse
      d p ell m n hmn E π U V hBelowPull hFresh
      hDisjoint S hTwo

end Kk
