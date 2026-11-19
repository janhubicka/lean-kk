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
    {d ell : Nat} (E : Nat → Nat → Bool)
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
    p ∈ trackACriticalGenerations E b j ↔
      ∃ U : IntegerGraphSupport d ell,
        trackACriticalSupport E b j U ∧
        trackAOldCapacity E b j U = p := by
  classical
  simp only [trackACriticalGenerations, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨U,hCritical,hEq⟩
    exact ⟨U,hCritical,hEq⟩
  · rintro ⟨U,hCritical,hEq⟩
    exact ⟨U,hCritical,hEq⟩

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
      p ∈ trackACriticalGenerations E b j ∧ g ≤ p ∧ p < h := by
  classical
  rw [trackA_henson_raw_function_change_iff_exists_support
    E ell hell hAvoid k b g h M hgh hh j hj]
  constructor
  · rintro ⟨U,hEligible,hCap,hCut,hLater⟩
    let p := trackAOldCapacity E b j U
    refine ⟨p, (mem_trackACriticalGenerations_iff E b j p).2
      ⟨U, ?_, rfl⟩, ?_, ?_⟩
    · exact ⟨hEligible,hCap⟩
    · exact hCut
    · exact hLater
  · rintro ⟨p,hMem,hCut,hLater⟩
    obtain ⟨U,hCrit,hEq⟩ :=
      (mem_trackACriticalGenerations_iff E b j p).1 hMem
    refine ⟨U,hCrit.1,hCrit.2,?_,?_⟩
    · change g ≤ trackAOldCapacity E b j U
      omega
    · change trackAOldCapacity E b j U < h
      omega

#print axioms Kk.mem_trackACriticalGenerations_iff
#print axioms Kk.trackA_henson_raw_change_iff_critical_generation

end Kk
