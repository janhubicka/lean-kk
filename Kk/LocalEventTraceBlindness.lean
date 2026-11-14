import Kk.ActualRunLevelProfileSync
import Kk.PhysicalCrossingTerminalBlindness
import Mathlib.Tactic

/-!
# Track E: hostile regression against recovering full Kpt sources
# from all local physical crossing and structural-event profiles

For genuine Kpt nodes x ≤ y with y already in Z, adding x changes
no complete old/upper L+ crossing pair at ANY cut. If Z already
has some terminal node t at the same level as x, this changes
not even the I1 existence flag at any cut.

The proved genuine Kpt monoid-level transfer therefore makes ALL
local Algorithm-5.4 interestingness verdicts, and all PRIORITIZED
I1/I2/nonstructural tags, literally agree, although the underlying
actual Kpt node SETS differ if x was absent.

This is a regression for arbitrary literal Kpt sets. It does
NOT claim both sets are closures arising from two AlgorithmRuns.
It prevents promoting local-tag equality into a named envelope orbit.

English proof and adversarial scope:
  docs/track_e_priority_cut_comparison_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A terminal prefix x already covered by longer y, whose level
also has another genuine existing terminal witness t, can be
inserted without changing ANY local terminal-existence flags
or ANY complete physical L+ crossing relation. Every old/upper
pair, including negative bits and auxiliary E, remains identical.

The existing t need not be unique and the source may be infinite.
No assumption of an actual AlgorithmRun closure is made. -/
theorem redundant_Kpt_node_invisible_to_all_local_source_profiles
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family))
    (x y t : AdmissibleKptNode family)
    (hxy : x ≤ y)
    (hy : y ∈ Z)
    (ht : t ∈ Z)
    (hSameLevel : LevelTree.lev t = LevelTree.lev x) :
    ∀ cut : Nat,
      (KptI1AtCut family (Set.insert x Z) cut ↔
        KptI1AtCut family Z cut) ∧
      FullPhysicalClosureCrossing family (Set.insert x Z) cut =
        FullPhysicalClosureCrossing family Z cut := by
  intro cut
  constructor
  · constructor
    · rintro ⟨z,hz,hLev⟩
      rcases (Set.mem_insert_iff.mp hz) with hzEq | hzZ
      · subst z
        exact ⟨t,ht,hSameLevel.trans hLev⟩
      · exact ⟨z,hzZ,hLev⟩
    · rintro ⟨z,hz,hLev⟩
      exact ⟨z,Set.mem_insert_of_mem x hz,hLev⟩
  · exact full_physical_crossing_ignores_redundant_terminal_ancestor
      family Z x y hxy hy cut

/-- Complete hostile negative: ALL source-cut physical old/upper
L+ crossing relations, ALL I1 terminal existence flags, and the
ACTUAL monoid I3/noninteresting verdicts can agree for two
DIFFERENT genuine Kpt NODE SETS. Even their prioritized structural
I1/I2 flags are identical.

The difference is real x∉Z, but this theorem does not assert
that both node sets arise as separate closed AlgorithmRun sources
or that two diary occurrences realize them. -/
theorem distinct_Kpt_node_sets_same_all_I1_I2_I3_local_verdicts
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family))
    (x y t : AdmissibleKptNode family)
    (hxy : x ≤ y) (hy : y ∈ Z) (ht : t ∈ Z)
    (hSameLevel : LevelTree.lev t = LevelTree.lev x)
    (hNot : x ∉ Z) :
    Set.insert x Z ≠ Z ∧
      (∀ cut,
        KptI1AtCut family (Set.insert x Z) cut ↔
          KptI1AtCut family Z cut) ∧
      (∀ cut,
        FullPhysicalClosureCrossing family (Set.insert x Z) cut =
          FullPhysicalClosureCrossing family Z cut) ∧
      (∀ cut,
        kptPriorityStructuralTag family (Set.insert x Z) cut =
          kptPriorityStructuralTag family Z cut) ∧
      (∀ cut,
        SMTree.Envelope.IsInterestingAt
          (normalizedKptSMTree family) (Set.insert x Z) cut ↔
        SMTree.Envelope.IsInterestingAt
          (normalizedKptSMTree family) Z cut) := by
  have hProfile :=
    redundant_Kpt_node_invisible_to_all_local_source_profiles
      family Z x y t hxy hy ht hSameLevel
  have hDiff : Set.insert x Z ≠ Z := by
    intro hEq
    have hx : x ∈ Set.insert x Z :=
      Set.mem_insert_iff.mpr (Or.inl rfl)
    rw [hEq] at hx
    exact hNot hx
  refine ⟨hDiff,?_,?_,?_,?_⟩
  · exact fun cut => (hProfile cut).1
  · exact fun cut => (hProfile cut).2
  · intro cut
    exact kpt_priority_tag_eq_of_terminal_and_crossings
      family (Set.insert x Z) Z cut
      (hProfile cut).1 (hProfile cut).2
  · intro cut
    exact kpt_actual_interesting_iff_of_terminal_and_crossing_eq
      family (Set.insert x Z) Z cut
      (hProfile cut).1 (hProfile cut).2

end Kk
