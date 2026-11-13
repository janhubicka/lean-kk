import Kk.FiniteCliqueIntegerWitness
import Kk.FiniteCliqueSupportWitness
import Mathlib.Tactic

/-!
# Track A: a reserved-support budget is exactly one raw cover constraint

English proof and hostile audit BEFORE formalization:
  docs/finite_support_cover_profile_english_audit.md

Adding a reserved clique capacity a joined to exactly the future
sorts in support T is equivalent, for ALL finite directed clique
witnesses and ALL nonempty supports, to imposing the canonical
cover-block raw constraint on coordinate T. The physical raw
capacity table may also change pointwise at smaller U⊆T; only
the full feasible-vector systems, not those raw functions, are
claimed equal.

The result is finite ordinary-L arithmetic; physical original
stage existence, full numerical-H+ E/B3 and labelled inverse-source
orbit are not claimed.
-/

namespace Kk

/-- ALL old raw bounds plus the ONE extra reserved-support clique
capacity budget are equivalent to the joint support constraints
for the existing ideal raw cover-block function. Neither W nor
its supported part need be a clique; the actual clique capacity
(not cardinality) is essential.

The guard a<ell is required for subtraction in Nat. -/
theorem finiteClique_full_constraints_raw_block_iff
    {d ell : Nat} (E : Nat → Nat → Bool)
    (W : Finset Nat) (sort : Nat → Fin d)
    (F : IntegerGraphSupport d ell → Nat)
    (T : IntegerGraphSupport d ell)
    (a : Nat) (ha : a < ell) :
    ((∀ s : Finset Nat, s ⊆ W → IsDirectedCliqueOn E s →
        ∀ U : IntegerGraphSupport d ell,
          (s.filter (fun w => sort w ∈ U.1)).card ≤ F U) ∧
      a + finiteDirectedCliqueCapacity E
        (W.filter (fun w => sort w ∈ T.1)) < ell) ↔
      (∀ s : Finset Nat, s ⊆ W → IsDirectedCliqueOn E s →
        ∀ U : IntegerGraphSupport d ell,
          (s.filter (fun w => sort w ∈ U.1)).card ≤
            rawCliqueBlockBound ell a F T U) := by
  classical
  have hCapacity :=
    finiteCliqueSupportCapacity_iff_all_witnesses
      E W sort T.1 a ell
  constructor
  · rintro ⟨hOld,hBudget⟩ s hsW hsClique U
    by_cases hSame : U = T
    · subst U
      have hOldAt := hOld s hsW hsClique T
      have hBudgetAt := hCapacity.mp hBudget s hsW hsClique
      change (s.filter (fun w => sort w ∈ T.1)).card ≤
        min (F T) (ell - 1 - a)
      apply le_min hOldAt
      omega
    · have hOldAt := hOld s hsW hsClique U
      simpa [rawCliqueBlockBound, hSame] using hOldAt
  · intro hRaw
    have hOld :
        ∀ s : Finset Nat, s ⊆ W → IsDirectedCliqueOn E s →
        ∀ U : IntegerGraphSupport d ell,
          (s.filter (fun w => sort w ∈ U.1)).card ≤ F U := by
      intro s hsW hsClique U
      exact (hRaw s hsW hsClique U).trans
        (rawCliqueBlockBound_le_upper ell a F T U)
    have hBudget :
        a + finiteDirectedCliqueCapacity E
          (W.filter (fun w => sort w ∈ T.1)) < ell := by
      apply hCapacity.mpr
      intro s hsW hsClique
      have hAt := hRaw s hsW hsClique T
      have hAtBound :
          (s.filter (fun w => sort w ∈ T.1)).card ≤ ell - 1 - a := by
        have hRawAt :
            rawCliqueBlockBound ell a F T T =
              min (F T) (ell - 1 - a) := by
          simp [rawCliqueBlockBound]
        rw [hRawAt] at hAt
        exact hAt.trans (Nat.min_le_right _ _)
      omega
    exact ⟨hOld,hBudget⟩

/-- For a K_ell-free arbitrary finite future W, applying the verified
integer-witness canonicalizer to the raw cover block does not change
the whole jointly permitted labelled clique profile. -/
theorem finiteClique_full_constraints_canonical_block_iff
    {d ell : Nat} (E : Nat → Nat → Bool)
    (W : Finset Nat) (sort : Nat → Fin d)
    (F : IntegerGraphSupport d ell → Nat)
    (T : IntegerGraphSupport d ell)
    (a : Nat) (ha : a < ell)
    (hWFree : finitePoolCliqueCheck E ell W = false) :
    ((∀ s : Finset Nat, s ⊆ W → IsDirectedCliqueOn E s →
        ∀ U : IntegerGraphSupport d ell,
          (s.filter (fun w => sort w ∈ U.1)).card ≤ F U) ∧
      a + finiteDirectedCliqueCapacity E
        (W.filter (fun w => sort w ∈ T.1)) < ell) ↔
      (∀ s : Finset Nat, s ⊆ W → IsDirectedCliqueOn E s →
        ∀ U : IntegerGraphSupport d ell,
          (s.filter (fun w => sort w ∈ U.1)).card ≤
            integerGraphAgeCanonical d ell
              (rawCliqueBlockBound ell a F T) U) := by
  have hRaw := finiteClique_full_constraints_raw_block_iff
    E W sort F T a ha
  have hCanonical := finiteClique_all_constraints_integerCanonical_iff
    E W sort (rawCliqueBlockBound ell a F T) hWFree
  exact hRaw.trans hCanonical.symm

/-- The precise finite witness form of a single canonical graph-age
COVER step. The whole-profile age is upper for capacity a<r and
lower exactly when a=r, provided the stated genuine integer-age
cover has the documented one-step arithmetic at T.

This theorem is conditional on the pre-block full clique constraints
being those of upper. It does not construct the physical front. -/
theorem finiteClique_full_constraints_cover_step_iff
    (d ell r : Nat)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (T : IntegerGraphSupport d ell)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (hEll : ell = lower T + r + 1)
    (hAt : upper T = lower T + 1)
    (a : Nat) (ha : a ≤ r)
    (E : Nat → Nat → Bool)
    (W : Finset Nat) (sort : Nat → Fin d)
    (hWFree : finitePoolCliqueCheck E ell W = false) :
    ((∀ s : Finset Nat, s ⊆ W → IsDirectedCliqueOn E s →
        ∀ U : IntegerGraphSupport d ell,
          (s.filter (fun w => sort w ∈ U.1)).card ≤ upper U) ∧
      a + finiteDirectedCliqueCapacity E
        (W.filter (fun w => sort w ∈ T.1)) < ell) ↔
      (∀ s : Finset Nat, s ⊆ W → IsDirectedCliqueOn E s →
        ∀ U : IntegerGraphSupport d ell,
          (s.filter (fun w => sort w ∈ U.1)).card ≤
            (if a < r then upper else lower) U) := by
  have haEll : a < ell := by omega
  have hProfile := finiteClique_full_constraints_canonical_block_iff
    E W sort upper T a haEll hWFree
  have hCoverEq :=
    integerGraphAge_canonical_cover_block
      d ell r lower upper T hCover hEll hAt a ha
  rw [hCoverEq] at hProfile
  exact hProfile

#print axioms Kk.finiteClique_full_constraints_raw_block_iff
#print axioms Kk.finiteClique_full_constraints_canonical_block_iff
#print axioms Kk.finiteClique_full_constraints_cover_step_iff

end Kk
