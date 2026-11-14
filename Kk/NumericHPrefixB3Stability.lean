import Kk.NumericHPrefixLPlusCoherence
import Kk.CrossClosurePhysicalComparison
import Mathlib.Tactic

/-!
# Track C: growing the genuine finite numerical H+ prefix preserves full B3

English-first proof and sixteen hostile checks (COMMITTED BEFORE Lean):
  docs/track_c_numeric_prefix_B3_stability_english_audit.md

For fixed K,k, actual Kpt seeds X and selected-level set I,
the COMPLETE Kpt meet/parameter closure Z does NOT change when
the finite numerical-H+ original carrier grows from N to M.

The previous Track C physical old-prefix theorem transports
every old original's exact auxiliary E, free cut, Kpt full
dependent L+ type and seed prefix pool into the larger model.

Thus under actual no-(I2) at the tested cut the two full
closure-selected prescribed crossing maps over the COMPLETE
Fin N and Fin M source-name universes have the SAME source,
the SAME assigned upper complete L+ type on source, and the
SAME corrected B3 verdict, despite new available original names.

This does not assert source equality between different diary
occurrences, add E to any separate L-only B3 age witness, or
construct new reserved original backward columns.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- An OLD named original belongs to the actual closure-selected
source at cut p precisely when the SAME physical original name
(after Fin.castLE) belongs in the larger numerical H+ prefix.

This is true even at a competing I2 cut, because the predicate
means the existence of a true Kpt node crossing that cut and
below the old original's exact dependent L+ type. No choice
of an assigned next-type representative occurs in this predicate.
-/
theorem finiteNumericH_prefix_old_named_source_iff
    {db du dd P : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N M : Nat) (hNM : N ≤ M)
    (hAvoidN : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hAvoidM : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k M).L)
    (original : Fin P → Fin N)
    (Z : Set (AdmissibleKptNode family))
    (cut : Nat) (v : Fin P) :
    closureSelectedOriginal family (finiteNumericH K k N)
      hAvoidN original Z cut v ↔
    closureSelectedOriginal family (finiteNumericH K k M)
      hAvoidM (fun w : Fin P => Fin.castLE hNM (original w))
      Z cut v := by
  have hOrig := finiteNumericH_prefix_old_KptOriginal_eq
    family K k N M hNM hAvoidN hAvoidM (original v)
  constructor
  · rintro ⟨z,hz,hCut,hBelow⟩
    refine ⟨z,hz,hCut,?_⟩
    rw [← hOrig]
    exact hBelow
  · rintro ⟨z,hz,hCut,hBelow⟩
    refine ⟨z,hz,hCut,?_⟩
    rw [hOrig]
    exact hBelow

/-- For one FIXED genuine finite numerical-H+ Kpt seed family X
and the SAME selected level set I, growing the physical carrier
N<=M leaves the canonical FULL source graph and its corrected B3
verdict unchanged at any no-(I2) cut.

The original-name universe is the entire physical Fin N / Fin M
in each model; neither side is the selected-front shadow.

The resulting comparison is exactly on the genuine source and
COMPLETE assigned upper L+ records, never dummy total F.target
values outside source. This does NOT imply a resolved schedule
with freshly inserted selected seeds preserves the same closure.
-/
theorem finiteNumericH_prefix_full_source_and_B3_stable
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N M : Nat) (hNM : N ≤ M)
    (hAvoidN : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hAvoidM : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k M).L)
    (U : Set (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hSeeds : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoidN U)
    (I : Set Nat) (cut : Nat)
    (hNoMeet : ¬ ∃ a : AdmissibleKptNode family,
      a ∈ SMTree.Envelope.closure (admissibleKptSTree family) I X ∧
      ∃ b : AdmissibleKptNode family,
        b ∈ SMTree.Envelope.closure (admissibleKptSTree family) I X ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :
    let Z : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family) I X
    let F_N : PrescribedBoringData cut db du dd :=
      closureSelectedBoringData family
        (finiteNumericH K k N) hAvoidN
        (fun v : Fin N => v) Z cut
    let F_M : PrescribedBoringData cut db du dd :=
      closureSelectedBoringData family
        (finiteNumericH K k M) hAvoidM
        (fun v : Fin M => v) Z cut
    F_N.source = F_M.source ∧
    (∀ T, T ∈ F_N.source → F_N.target T = F_M.target T) ∧
    (F_N.CorrectedB3 family ↔ F_M.CorrectedB3 family) := by
  classical
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  let B : EnumeratedPartialStructure db du dd := finiteNumericH K k M
  let Z : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family) I X
  have hPoolN : ∀ z, z ∈ Z →
      ∃ v : Fin N,
        z ≤ A.kptOriginal family hAvoidN v := by
    intro z hz
    obtain ⟨o, ⟨v,_hv,rfl⟩,hBelow⟩ :=
      (admissibleKpt_stage_closure_subset_pool
        family A hAvoidN U I X hSeeds) hz
    exact ⟨v,hBelow⟩
  have hSeedsM :
      X ⊆ ambientPrefixPool family B hAvoidM
        ((Fin.castLE hNM) '' U) :=
    finiteNumericH_prefix_seed_pool_lifts
      family K k N M hNM hAvoidN hAvoidM U X hSeeds
  have hPoolM : ∀ z, z ∈ Z →
      ∃ v : Fin M,
        z ≤ B.kptOriginal family hAvoidM v := by
    intro z hz
    obtain ⟨o, ⟨v,_hv,rfl⟩,hBelow⟩ :=
      (admissibleKpt_stage_closure_subset_pool
        family B hAvoidM ((Fin.castLE hNM) '' U) I X
        hSeedsM) hz
    exact ⟨v,hBelow⟩
  exact two_numericH_closures_B3_of_equal_full_crossing_relation
    family K K k N k M hAvoidN hAvoidM
    (fun v : Fin N => v) (fun v : Fin M => v)
    Z Z hPoolN hPoolM cut hNoMeet hNoMeet rfl

#print axioms Kk.finiteNumericH_prefix_old_named_source_iff
#print axioms Kk.finiteNumericH_prefix_full_source_and_B3_stable

end Kk
