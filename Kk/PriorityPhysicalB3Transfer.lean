import Kk.PriorityPhysicalCutComparison
import Kk.CrossClosurePhysicalComparison
import Mathlib.Tactic

/-!
# Track E: transfer genuine numerical H+ no-I2 and corrected B3

Two different physical finite H+ occurrences may have different
ambient graph models, sizes and complete original-name pools.

If one closure has no structural I1/I2 at a common source cut, and
the OTHER has the same terminal I1 flag and full old+upper L+ crossing
relation, Track C's no-I1 fork equivalence proves that the second
closure also has no structural I2. The already checked physical
cross-closure source/upper-B3 comparison then applies WITHOUT separately
assuming no-I2 of the second closure.

This is conditional on actual full physical profile agreement, not on
a selected-shadow diary or an abstract B3 verdict. The global common
labelled inverse-source orbit remains open.

English-first proof and hostile audits:
  docs/track_e_priority_cut_comparison_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Once the genuine (I1) flag and full dependent L+ crossing
relation agree, absence of BOTH structural interesting conditions
in ONE physical Kpt closure forces their absence in the OTHER.
No original-name pool or actual numerical H is needed for this step. -/
theorem kpt_no_structural_event_transfers_of_local_profile
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z₁ Z₂ : Set (AdmissibleKptNode family))
    (cut : Nat)
    (hNoI1₁ : ¬ KptI1AtCut family Z₁ cut)
    (hNoI2₁ : ¬ KptI2MeetAtCut family Z₁ cut)
    (hTerminal : KptI1AtCut family Z₁ cut ↔
      KptI1AtCut family Z₂ cut)
    (hPhysical : FullPhysicalClosureCrossing family Z₁ cut =
      FullPhysicalClosureCrossing family Z₂ cut) :
    ¬ KptI1AtCut family Z₂ cut ∧
    ¬ KptI2MeetAtCut family Z₂ cut := by
  have hFlags :=
    kpt_priority_structural_flags_eq_of_terminal_and_crossings
      family Z₁ Z₂ cut hTerminal hPhysical
  exact (hFlags.2.2.mp ⟨hNoI1₁,hNoI2₁⟩)

/-- A cross-presentation physical B3 theorem with a **derived**
no-I2 condition in the second occurrence, not an extra assumed
condition.

Two actual numerical H+ models may use different physical original
name pools and different finite universes. The only cross-occurrence
profile input is the exact full L+ crossing relation equality, plus
the source I1 terminal-flag equality. From a single nonstructural
source cut, prove the second cut nonstructural and then invoke the
physically verified full-source B3 transfer, including complete
auxiliary-E records of every chosen prescribed successor.

No unrefined macrodiary equality, global resolved-copy embedding,
or upper big Ramsey degree assertion is inferred. -/
theorem two_numericH_nonstructural_B3_of_terminal_and_crossing_profile
    {db du dd M₁ M₂ : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K₁ K₂ : AgeTestModel db du dd)
    (k₁ N₁ k₂ N₂ : Nat)
    (hAvoid₁ : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K₁ k₁ N₁).L)
    (hAvoid₂ : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K₂ k₂ N₂).L)
    (original₁ : Fin M₁ → Fin (finiteNumericH K₁ k₁ N₁).size)
    (original₂ : Fin M₂ → Fin (finiteNumericH K₂ k₂ N₂).size)
    (Z₁ Z₂ : Set (AdmissibleKptNode family))
    (hPool₁ : ∀ z, z ∈ Z₁ →
      ∃ v : Fin M₁,
        z ≤ (finiteNumericH K₁ k₁ N₁).kptOriginal family hAvoid₁ (original₁ v))
    (hPool₂ : ∀ z, z ∈ Z₂ →
      ∃ v : Fin M₂,
        z ≤ (finiteNumericH K₂ k₂ N₂).kptOriginal family hAvoid₂ (original₂ v))
    (cut : Nat)
    (hNoI1₁ : ¬ KptI1AtCut family Z₁ cut)
    (hNoI2₁ : ¬ KptI2MeetAtCut family Z₁ cut)
    (hTerminal : KptI1AtCut family Z₁ cut ↔
      KptI1AtCut family Z₂ cut)
    (hPhysical :
      FullPhysicalClosureCrossing family Z₁ cut =
        FullPhysicalClosureCrossing family Z₂ cut) :
    (¬ KptI1AtCut family Z₂ cut ∧
      ¬ KptI2MeetAtCut family Z₂ cut) ∧
    (let F : PrescribedBoringData cut db du dd :=
      closureSelectedBoringData family
        (finiteNumericH K₁ k₁ N₁) hAvoid₁ original₁ Z₁ cut
     let G : PrescribedBoringData cut db du dd :=
      closureSelectedBoringData family
        (finiteNumericH K₂ k₂ N₂) hAvoid₂ original₂ Z₂ cut
     F.source = G.source ∧
      (∀ T, T ∈ F.source → F.target T = G.target T) ∧
      (F.CorrectedB3 family ↔ G.CorrectedB3 family)) := by
  have hNoStruct₂ :=
    kpt_no_structural_event_transfers_of_local_profile
      family Z₁ Z₂ cut hNoI1₁ hNoI2₁ hTerminal hPhysical
  have hB3 :=
    two_numericH_closures_B3_of_equal_full_crossing_relation
      family K₁ K₂ k₁ N₁ k₂ N₂
      hAvoid₁ hAvoid₂ original₁ original₂ Z₁ Z₂
      hPool₁ hPool₂ cut hNoI2₁ hNoStruct₂.2 hPhysical
  exact ⟨hNoStruct₂,hB3⟩

end Kk
