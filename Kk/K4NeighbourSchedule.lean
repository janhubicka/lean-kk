import Kk.FiniteNeighbourSchedule
import Kk.K4NumericalHAtoms
import Mathlib.Tactic

/-!
# Complete stagewise certificates for the four-original K4 seed

The actual K4 numerical-H base has four originals indexed 0..3.
All four of its finite prefix-extension certificates are negative,
including the final step with an older two-vertex reserved clique
and the additional older parameter p.

This is a checked finite illustration of the schedule-induction
theorem. It does not verify the unbounded global resolved copy.
-/

namespace Kk

/-- The four stages of the actual numerical-H K4 original table
have no forbidden three-clique in the COMPLETE past neighbourhood. -/
theorem k4FourOriginal_all_stage_certificates :
    ∀ n, n < 4 →
      finiteNeighbourCliqueCheck k4FourOriginalEdge n 3
        (fun u => k4FourOriginalEdge u n) = false := by
  intro n hn
  interval_cases n <;> decide

/-- An independent proof of the first four original vertices'
K4-freeness, obtained by the finite-stage certificate induction. -/
theorem k4FourOriginal_initial_prefix_cliqueFree :
    ¬ HasCliqueBelow k4FourOriginalEdge 4 4 := by
  exact (cliqueFree_prefix_iff_all_finite_neighbour_certificates
    k4FourOriginalEdge 4 4
    (by decide)
    k4FourOriginalEdge_symmetric
    k4FourOriginalEdge_irreflexive).2
    k4FourOriginal_all_stage_certificates

end Kk
