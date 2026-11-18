import Kk.PhysicalCrossingTerminalBlindness
import Kk.TrackGFullEventProfileTransport
import Mathlib.Tactic

/-!
# Track G adversarial regression: all-cut full local Kpt event profiles
# do NOT necessarily identify the underlying Kpt source-node SET.

English proof and 12 hostile checks committed FIRST:
docs/track_g_event_profile_not_full_source_english_audit_20261118.md

If x ≤ y and y belongs to a genuine Kpt node set Z, then adding
x contributes no new complete paired dependent old/upper L+/E
crossings at ANY cut. If some old source node w already witnesses
the terminal flag at level(x), then adding x does not change ANY
I1 terminal-existence flag, either. If x is genuinely absent from Z,
the physical node sets differ despite equal complete event profiles
at EVERY numerical cut and thus equal local IsInterestingAt tests.

This is a CONDITIONAL literal admissible Kpt-source-set example, not
a claim that the sets are two actual AlgorithmRun pre-cut closures,
nor a counterexample to the global refined diary or exact BRD theorem.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- An actual redundant ancestor x ≤ y is invisible to EVERY complete
paired Kpt crossing relation (verified already), and is invisible
to all TERMINAL EXISTENCE flags provided Z has an independent
terminal at level(x). Here Z need not be an actual run closure. -/
theorem kpt_all_cut_full_event_profile_ignores_covered_ancestor
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family))
    (x y : AdmissibleKptNode family)
    (hxy : x ≤ y) (hy : y ∈ Z)
    (hTerminal : KptI1AtCut family Z (LevelTree.lev x)) :
    ∀ cut : Nat,
      (KptI1AtCut family (Set.insert x Z) cut ↔
       KptI1AtCut family Z cut) ∧
      FullPhysicalClosureCrossing family (Set.insert x Z) cut =
        FullPhysicalClosureCrossing family Z cut := by
  intro cut
  constructor
  · constructor
    · rintro ⟨z,hz,hLev⟩
      rcases Set.mem_insert_iff.mp hz with hzx | hzZ
      · subst z
        obtain ⟨w,hw,hWLev⟩ := hTerminal
        exact ⟨w,hw,hWLev.trans hLev⟩
      · exact ⟨z,hzZ,hLev⟩
    · rintro ⟨z,hz,hLev⟩
      exact ⟨z,Set.mem_insert_of_mem x hz,hLev⟩
  · exact full_physical_crossing_ignores_redundant_terminal_ancestor
      family Z x y hxy hy cut

/-- Even complete per-cut I1 flags AND complete paired dependent
L+/E crossing relations over ALL cuts can forget actual Kpt
source-node identity. The extra x is a literal new source node,
but its profile is already covered by y and by an old terminal.

As a result the true local I1/I2/I3 interestingness decisions
are equal at every cut, despite the two source SETS being unequal.
This does NOT construct two actual different AlgorithmRun closures. -/
theorem kpt_distinct_source_sets_equal_all_cut_profiles_and_decisions
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family))
    (x y : AdmissibleKptNode family)
    (hxy : x ≤ y) (hy : y ∈ Z)
    (hxNot : x ∉ Z)
    (hTerminal : KptI1AtCut family Z (LevelTree.lev x)) :
    Set.insert x Z ≠ Z ∧
    ∀ cut : Nat,
      (KptI1AtCut family (Set.insert x Z) cut ↔
       KptI1AtCut family Z cut) ∧
      FullPhysicalClosureCrossing family (Set.insert x Z) cut =
        FullPhysicalClosureCrossing family Z cut ∧
      (SMTree.Envelope.IsInterestingAt (normalizedKptSMTree family)
        (Set.insert x Z) cut ↔
       SMTree.Envelope.IsInterestingAt (normalizedKptSMTree family)
        Z cut) := by
  constructor
  · intro hEq
    apply hxNot
    have hx : x ∈ Set.insert x Z :=
      Set.mem_insert_iff.mpr (Or.inl rfl)
    rw [hEq] at hx
    exact hx
  · intro cut
    obtain ⟨hTerm,hPairs⟩ :=
      kpt_all_cut_full_event_profile_ignores_covered_ancestor
        family Z x y hxy hy hTerminal cut
    exact ⟨hTerm,hPairs,
      kpt_IsInterestingAt_iff_of_terminal_and_full_crossing_eq
        family (Set.insert x Z) Z cut hTerm hPairs⟩

end Kk
