import Kk.NumericHStructuralCutClassifier
import Kk.IndexedPhysicalStructuralEvents
import Mathlib.Tactic

/-!
# Track E: source-normalized priority I1/I2 comparison across two Kpt closures

An actual Kpt AlgorithmRun first checks (I1), and only then (I2).
The raw I2 meet predicate can be true for the SELF-MEET of a node
already witnessing I1, so an unconditional I2 = full crossing fork
claim is false.

Track C has proved no-I1 => I2 iff complete old/upper L+ crossing
nonfunctionality. Thus agreement of just
  (i) the true full terminal-node flag at cut, and
  (ii) the entire full physical crossing relation at cut
forces the same PRIORITIZED I1/I2/nonstructural tag for two possibly
different physical Kpt closures. No pairwise meet matching of all
indexed nodes is required for the structural *tag*. It is still
needed for reconstructing full named source geometry and monoid orbit.

English-first argument and hostile self-meet audit:
  docs/track_e_priority_cut_comparison_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The actual Algorithm-5.4 structural priority: I1 before I2,
otherwise continue to the nonstructural (B3/I3) test.

A raw I2 self-meet at an I1 cut is deliberately not reported as I2. -/
inductive KptPriorityStructuralTag
  | I1
  | I2
  | nonstructural
  deriving DecidableEq

/-- For an arbitrary actual Kpt closure Z, the priority tag is
defined from real source membership and full same-component meets.
No finite selected original-name shadow appears in the definition. -/
noncomputable def kptPriorityStructuralTag
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family)) (cut : Nat) :
    KptPriorityStructuralTag := by
  classical
  exact if KptI1AtCut family Z cut then .I1
    else if KptI2MeetAtCut family Z cut then .I2
    else .nonstructural

/-- Hostile regression: a genuine Kpt node terminating at the cut
already witnesses BOTH raw I1 and raw I2 via its own self-meet.
Hence a raw I2 ↔ nonfunctional crossing claim is false at an I1
cut; the true AlgorithmRun uses a PRIORITY decision tree. -/
theorem terminal_kpt_node_witnesses_raw_I1_and_I2
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family)) (cut : Nat)
    (x : AdmissibleKptNode family)
    (hx : x ∈ Z) (hLevel : LevelTree.lev x = cut) :
    KptI1AtCut family Z cut ∧ KptI2MeetAtCut family Z cut := by
  have hComponent : SMTree.Envelope.SameComponent x x :=
    ⟨x, le_rfl, le_rfl⟩
  have hMeet : LevelTree.meet x x = x := by
    apply le_antisymm
    · exact LevelTree.meet_le_left hComponent
    · exact LevelTree.le_meet le_rfl le_rfl
  exact ⟨⟨x,hx,hLevel⟩, ⟨x,hx,x,hx,hComponent,by rw [hMeet]; exact hLevel⟩⟩

/-- The critical Track E comparison with NO source-node bijection:
the terminal I1 flag and the complete full-L+ crossing relation at
one COMMON source-coordinate cut determine the exact prioritized
structural alternatives for TWO different closures.

The three outputs respectively compare:
  I1;
  non-I1 genuine I2;
  neither I1 nor I2 (hence proceed to B3/I3).

Raw I2 is not asserted equal at I1 cuts; it may have degenerate
self-meets invisible to crossing spectra. -/
theorem kpt_priority_structural_flags_eq_of_terminal_and_crossings
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z₁ Z₂ : Set (AdmissibleKptNode family))
    (cut : Nat)
    (hTerminal : KptI1AtCut family Z₁ cut ↔
      KptI1AtCut family Z₂ cut)
    (hPhysical : FullPhysicalClosureCrossing family Z₁ cut =
      FullPhysicalClosureCrossing family Z₂ cut) :
    (KptI1AtCut family Z₁ cut ↔ KptI1AtCut family Z₂ cut) ∧
    ((¬ KptI1AtCut family Z₁ cut ∧ KptI2MeetAtCut family Z₁ cut) ↔
      (¬ KptI1AtCut family Z₂ cut ∧ KptI2MeetAtCut family Z₂ cut)) ∧
    ((¬ KptI1AtCut family Z₁ cut ∧ ¬ KptI2MeetAtCut family Z₁ cut) ↔
      (¬ KptI1AtCut family Z₂ cut ∧ ¬ KptI2MeetAtCut family Z₂ cut)) := by
  have hFork :
      (∃ T : PartialTypeWithE cut db du dd,
        ∃ U V : PartialTypeWithE (cut+1) db du dd,
          (T,U) ∈ FullPhysicalClosureCrossing family Z₁ cut ∧
          (T,V) ∈ FullPhysicalClosureCrossing family Z₁ cut ∧ U ≠ V) ↔
      (∃ T : PartialTypeWithE cut db du dd,
        ∃ U V : PartialTypeWithE (cut+1) db du dd,
          (T,U) ∈ FullPhysicalClosureCrossing family Z₂ cut ∧
          (T,V) ∈ FullPhysicalClosureCrossing family Z₂ cut ∧ U ≠ V) := by
    rw [hPhysical]
  have hNoI1 : (¬ KptI1AtCut family Z₁ cut) ↔
      (¬ KptI1AtCut family Z₂ cut) := not_congr hTerminal
  have hI2 (hNo₁ : ¬ KptI1AtCut family Z₁ cut) :
      KptI2MeetAtCut family Z₁ cut ↔
      KptI2MeetAtCut family Z₂ cut := by
    have hNo₂ : ¬ KptI1AtCut family Z₂ cut := hNoI1.mp hNo₁
    have h₁ :=
      kpt_no_I1_I2_iff_physical_crossing_nonfunctional
        family Z₁ cut hNo₁
    have h₂ :=
      kpt_no_I1_I2_iff_physical_crossing_nonfunctional
        family Z₂ cut hNo₂
    exact h₁.trans (hFork.trans h₂.symm)
  refine ⟨hTerminal, ?_, ?_⟩
  · constructor
    · rintro ⟨hNo₁,hMeet₁⟩
      exact ⟨hNoI1.mp hNo₁, (hI2 hNo₁).mp hMeet₁⟩
    · rintro ⟨hNo₂,hMeet₂⟩
      have hNo₁ := hNoI1.mpr hNo₂
      exact ⟨hNo₁,(hI2 hNo₁).mpr hMeet₂⟩
  · constructor
    · rintro ⟨hNo₁,hNotMeet₁⟩
      exact ⟨hNoI1.mp hNo₁, mt (hI2 hNo₁).mpr hNotMeet₁⟩
    · rintro ⟨hNo₂,hNotMeet₂⟩
      have hNo₁ := hNoI1.mpr hNo₂
      exact ⟨hNo₁,mt (hI2 hNo₁).mp hNotMeet₂⟩

/-- The same profile hypotheses identify the actual 3-valued
priority tag, not merely the disjunction I1-or-I2. -/
theorem kpt_priority_tag_eq_of_terminal_and_crossings
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z₁ Z₂ : Set (AdmissibleKptNode family))
    (cut : Nat)
    (hTerminal : KptI1AtCut family Z₁ cut ↔
      KptI1AtCut family Z₂ cut)
    (hPhysical : FullPhysicalClosureCrossing family Z₁ cut =
      FullPhysicalClosureCrossing family Z₂ cut) :
    kptPriorityStructuralTag family Z₁ cut =
      kptPriorityStructuralTag family Z₂ cut := by
  classical
  have hFlags :=
    kpt_priority_structural_flags_eq_of_terminal_and_crossings
      family Z₁ Z₂ cut hTerminal hPhysical
  by_cases hI1₁ : KptI1AtCut family Z₁ cut
  · have hI1₂ := hTerminal.mp hI1₁
    simp [kptPriorityStructuralTag, hI1₁, hI1₂]
  · have hI1₂ : ¬ KptI1AtCut family Z₂ cut :=
      fun h => hI1₁ (hTerminal.mpr h)
    by_cases hI2₁ : KptI2MeetAtCut family Z₁ cut
    · have hI2₂ : KptI2MeetAtCut family Z₂ cut :=
        (hFlags.2.1.mp ⟨hI1₁,hI2₁⟩).2
      simp [kptPriorityStructuralTag, hI1₁, hI1₂, hI2₁, hI2₂]
    · have hI2₂ : ¬ KptI2MeetAtCut family Z₂ cut :=
        (hFlags.2.2.mp ⟨hI1₁,hI2₁⟩).2
      simp [kptPriorityStructuralTag, hI1₁, hI1₂, hI2₁, hI2₂]

/-- The finite INDEXED minimal profile criterion from merged Track C/E.

Two independent finite parameter indices (possibly different sizes)
need not be matched name-by-name. Exact physical source coverage,
the terminal-node witness flag, and equality of complete indexed
old+upper L+ crossing RELATIONS suffice for equality of PRIORITY
structural event tags at an aligned cut.

Full labelled envelope/orbit recovery still needs parameter identity,
meet incidence and outgoing monoid map compatibility; this theorem
only determines the priority structural kind. -/
theorem kpt_priority_tag_eq_of_indexed_terminal_and_crossings
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {Params₁ Params₂ : Type}
    (Z₁ Z₂ : Set (AdmissibleKptNode family))
    (node₁ : Params₁ → AdmissibleKptNode family)
    (node₂ : Params₂ → AdmissibleKptNode family)
    (live₁ : Nat → Params₁ → Bool)
    (live₂ : Nat → Params₂ → Bool)
    (cut : Nat)
    (hExact₁ : ∀ z : AdmissibleKptNode family,
      z ∈ Z₁ ↔ ∃ j : Params₁,
        node₁ j = z ∧ live₁ cut j = true)
    (hExact₂ : ∀ z : AdmissibleKptNode family,
      z ∈ Z₂ ↔ ∃ j : Params₂,
        node₂ j = z ∧ live₂ cut j = true)
    (hTerminal :
      (∃ j : Params₁, live₁ cut j = true ∧
        LevelTree.lev (node₁ j) = cut) ↔
      (∃ j : Params₂, live₂ cut j = true ∧
        LevelTree.lev (node₂ j) = cut))
    (hIndexed :
      IndexedPhysicalCrossing family node₁ live₁ cut =
      IndexedPhysicalCrossing family node₂ live₂ cut) :
    kptPriorityStructuralTag family Z₁ cut =
      kptPriorityStructuralTag family Z₂ cut := by
  have hTerm₁ :=
    (physical_I1_I2_iff_indexed_active_nodes
      family node₁ live₁ Z₁ cut hExact₁).1
  have hTerm₂ :=
    (physical_I1_I2_iff_indexed_active_nodes
      family node₂ live₂ Z₂ cut hExact₂).1
  have hI1 : KptI1AtCut family Z₁ cut ↔
      KptI1AtCut family Z₂ cut :=
    hTerm₁.trans (hTerminal.trans hTerm₂.symm)
  have hCross :
      FullPhysicalClosureCrossing family Z₁ cut =
      FullPhysicalClosureCrossing family Z₂ cut := by
    calc
      FullPhysicalClosureCrossing family Z₁ cut =
          IndexedPhysicalCrossing family node₁ live₁ cut :=
        (indexed_physical_crossing_eq_full_closure_relation
          family node₁ live₁ Z₁ cut hExact₁).symm
      _ = IndexedPhysicalCrossing family node₂ live₂ cut := hIndexed
      _ = FullPhysicalClosureCrossing family Z₂ cut :=
        indexed_physical_crossing_eq_full_closure_relation
          family node₂ live₂ Z₂ cut hExact₂
  exact kpt_priority_tag_eq_of_terminal_and_crossings
    family Z₁ Z₂ cut hI1 hCross

end Kk
