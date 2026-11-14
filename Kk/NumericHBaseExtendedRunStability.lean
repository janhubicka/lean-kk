import Kk.NumericHBaseExtensionCoherence
import Kk.CrossClosurePhysicalComparison
import SuccessorTree.EnvelopeRun
import Mathlib.Tactic

/-!
# Track C: actual full source/B3 under NEW ORIGINAL Henson columns

English-first proof and 17 adversarial checks:
  docs/track_c_base_extended_run_stability_english_audit.md

We compare TWO different base age models K,L, not merely truncations
of the same base K. They agree exactly on all original
binary/unary/diagonal atoms below b; their newly added columns
at/above b can differ.

When the OLD physical numerical carrier N lies below the new
base-original block frontier hPosition k b 0, the already-checked
Track C base-extension lemma identifies every old admissible Kpt
original and carries the entire old parameter closure into the
new physical numerical-H+ model.

The actual full closure-selected source and its assigned upper L+
types are therefore stable at any true no-I2 cut. Two independent
AlgorithmRuns on the SAME true Kpt seeds have identical selected
level sets by the verified successor-tree theorem, so the real
run-cut comparison follows without a stipulated comparison of I.

This is NOT an equality of full source orbits for different diary
seed sets, not a construction of all new original columns, and not
a global big Ramsey degree characterization.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The exact OLD Kpt original selection predicate is preserved
under physical base-graph extension K→L, including new columns
outside old original blocks. This needs NO no-(I2) hypothesis:
there is no chosen next-upper type in the statement. -/
theorem finiteNumericH_baseExtension_old_named_source_iff
    {db du dd P : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K L : AgeTestModel db du dd)
    (k b N M : Nat) (hNM : N ≤ M)
    (hBlock : N ≤ hPosition k b 0)
    (hBin : ∀ i j : Nat, i < b → j < b →
      ∀ r : Fin db, K.binary i j r = L.binary i j r)
    (hUn : ∀ i : Nat, i < b → ∀ r : Fin du,
      K.unary i r = L.unary i r)
    (hDiag : ∀ i : Nat, i < b → ∀ r : Fin dd,
      K.diagonal i r = L.diagonal i r)
    (hAvoidK : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hAvoidL : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (original : Fin P → Fin N)
    (Z : Set (AdmissibleKptNode family))
    (cut : Nat) (v : Fin P) :
    closureSelectedOriginal family (finiteNumericH K k N)
      hAvoidK original Z cut v ↔
    closureSelectedOriginal family (finiteNumericH L k M)
      hAvoidL (fun t : Fin P => Fin.castLE hNM (original t))
      Z cut v := by
  have hOrig := finiteNumericH_baseExtension_old_KptOriginal_eq
    family K L k b N M hNM hBlock hBin hUn hDiag
    hAvoidK hAvoidL (original v)
  constructor
  · rintro ⟨z,hz,hCross,hBelow⟩
    refine ⟨z,hz,hCross,?_⟩
    rw [← hOrig]
    exact hBelow
  · rintro ⟨z,hz,hCross,hBelow⟩
    refine ⟨z,hz,hCross,?_⟩
    rw [hOrig]
    exact hBelow

/-- The canonical full closure-selected source graph is preserved
when the BASE numerical-H+ original model changes from K to L
outside the old base block prefix, in addition to N→M carrier
growth. The identical TRUE Kpt closure Z is exhaustively
represented in BOTH physical numerical models.

At a genuine full no-I2 cut, the complete old/upper L+ source
graph and ordinary-L corrected-B3 verdict are exactly equal,
not only selected-front graph-age spectra. -/
theorem finiteNumericH_baseExtension_same_closure_full_source_B3_stable
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K L : AgeTestModel db du dd)
    (k b N M : Nat) (hNM : N ≤ M)
    (hBlock : N ≤ hPosition k b 0)
    (hBin : ∀ i j : Nat, i < b → j < b →
      ∀ r : Fin db, K.binary i j r = L.binary i j r)
    (hUn : ∀ i : Nat, i < b → ∀ r : Fin du,
      K.unary i r = L.unary i r)
    (hDiag : ∀ i : Nat, i < b → ∀ r : Fin dd,
      K.diagonal i r = L.diagonal i r)
    (hAvoidK : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hAvoidL : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (U : Set (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hSeeds : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoidK U)
    (I : Set Nat) (cut : Nat)
    (hNoMeet : ¬ ∃ a : AdmissibleKptNode family,
      a ∈ SMTree.Envelope.closure (admissibleKptSTree family) I X ∧
      ∃ b : AdmissibleKptNode family,
        b ∈ SMTree.Envelope.closure (admissibleKptSTree family) I X ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :
    let Z : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family) I X
    let F_K : PrescribedBoringData cut db du dd :=
      closureSelectedBoringData family
        (finiteNumericH K k N) hAvoidK (fun v : Fin N => v) Z cut
    let F_L : PrescribedBoringData cut db du dd :=
      closureSelectedBoringData family
        (finiteNumericH L k M) hAvoidL (fun v : Fin M => v) Z cut
    F_K.source = F_L.source ∧
      (∀ T, T ∈ F_K.source → F_K.target T = F_L.target T) ∧
      (F_K.CorrectedB3 family ↔ F_L.CorrectedB3 family) := by
  classical
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  let B : EnumeratedPartialStructure db du dd := finiteNumericH L k M
  let Z : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family) I X
  have hPoolK : ∀ z, z ∈ Z →
      ∃ v : Fin N,
        z ≤ A.kptOriginal family hAvoidK v := by
    intro z hz
    obtain ⟨o,⟨v,_hv,rfl⟩,hBelow⟩ :=
      (admissibleKpt_stage_closure_subset_pool
        family A hAvoidK U I X hSeeds) hz
    exact ⟨v,hBelow⟩
  have hSeedsL : X ⊆ ambientPrefixPool family B hAvoidL
      ((Fin.castLE hNM) '' U) :=
    finiteNumericH_baseExtension_old_seedPool_lifts
      family K L k b N M hNM hBlock hBin hUn hDiag
        hAvoidK hAvoidL U X hSeeds
  have hPoolL : ∀ z, z ∈ Z →
      ∃ v : Fin M,
        z ≤ B.kptOriginal family hAvoidL v := by
    intro z hz
    obtain ⟨o,⟨v,_hv,rfl⟩,hBelow⟩ :=
      (admissibleKpt_stage_closure_subset_pool
        family B hAvoidL ((Fin.castLE hNM) '' U) I X
          hSeedsL) hz
    exact ⟨v,hBelow⟩
  exact two_numericH_closures_B3_of_equal_full_crossing_relation
    family K L k N k M hAvoidK hAvoidL
      (fun v : Fin N => v) (fun v : Fin M => v)
      Z Z hPoolK hPoolL cut hNoMeet hNoMeet rfl

/-- TWO genuine AlgorithmRuns on the SAME actual full Kpt seed X
over TWO physical numerical-H+ structures K,N and L,M whose
base-original graphs agree below the old block frontier must
select the same levels regardless of their one-step map choices.

At EACH actual pre-cut with no full competing I2 meet, the
canonical full L+ old/upper assigned source graph and corrected
B3 verdict coincide, including every auxiliary parameter/meet
source and all negative relation atoms.

This is a valid SAME-SEED physical model-extension theorem, NOT
a comparison of different resolved diary occurrences. -/
theorem numericH_two_actual_runs_baseExtension_full_source_B3_stable
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K L : AgeTestModel db du dd)
    (k b N M : Nat) (hNM : N ≤ M)
    (hBlock : N ≤ hPosition k b 0)
    (hBin : ∀ i j : Nat, i < b → j < b →
      ∀ r : Fin db, K.binary i j r = L.binary i j r)
    (hUn : ∀ i : Nat, i < b → ∀ r : Fin du,
      K.unary i r = L.unary i r)
    (hDiag : ∀ i : Nat, i < b → ∀ r : Fin dd,
      K.diagonal i r = L.diagonal i r)
    (hAvoidK : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hAvoidL : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (U : Set (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hSeeds : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoidK U)
    (top : Nat)
    (R S : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top) :
    (∀ i : Nat, i ≤ top → R.I i = S.I i) ∧
      (∀ cut : Nat, cut < top →
        (¬ ∃ a : AdmissibleKptNode family,
          a ∈ SMTree.Envelope.closure
            (admissibleKptSTree family) (R.I (cut+1)) X ∧
          ∃ b : AdmissibleKptNode family,
            b ∈ SMTree.Envelope.closure
              (admissibleKptSTree family) (R.I (cut+1)) X ∧
            SMTree.Envelope.SameComponent a b ∧
            LevelTree.lev (LevelTree.meet a b) = cut) →
        let Z_R : Set (AdmissibleKptNode family) :=
          SMTree.Envelope.closure
            (admissibleKptSTree family) (R.I (cut+1)) X
        let Z_S : Set (AdmissibleKptNode family) :=
          SMTree.Envelope.closure
            (admissibleKptSTree family) (S.I (cut+1)) X
        let F_K : PrescribedBoringData cut db du dd :=
          closureSelectedBoringData family
            (finiteNumericH K k N) hAvoidK
            (fun v : Fin N => v) Z_R cut
        let F_L : PrescribedBoringData cut db du dd :=
          closureSelectedBoringData family
            (finiteNumericH L k M) hAvoidL
            (fun v : Fin M => v) Z_S cut
        F_K.source = F_L.source ∧
          (∀ T, T ∈ F_K.source → F_K.target T = F_L.target T) ∧
          (F_K.CorrectedB3 family ↔ F_L.CorrectedB3 family)) := by
  have hLevels : ∀ i : Nat, i ≤ top → R.I i = S.I i :=
    R.I_eq S
  refine ⟨hLevels, ?_⟩
  intro cut hCut hNoMeet
  have hTail : R.I (cut+1) = S.I (cut+1) :=
    hLevels (cut+1) (by omega)
  change
    (closureSelectedBoringData family
      (finiteNumericH K k N) hAvoidK
      (fun v : Fin N => v)
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X) cut).source =
    (closureSelectedBoringData family
      (finiteNumericH L k M) hAvoidL
      (fun v : Fin M => v)
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (S.I (cut+1)) X) cut).source ∧
    (∀ T,
      T ∈ (closureSelectedBoringData family
        (finiteNumericH K k N) hAvoidK
        (fun v : Fin N => v)
        (SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) X) cut).source →
      (closureSelectedBoringData family
        (finiteNumericH K k N) hAvoidK
        (fun v : Fin N => v)
        (SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) X) cut).target T =
      (closureSelectedBoringData family
        (finiteNumericH L k M) hAvoidL
        (fun v : Fin M => v)
        (SMTree.Envelope.closure
          (admissibleKptSTree family) (S.I (cut+1)) X) cut).target T) ∧
    ((closureSelectedBoringData family
      (finiteNumericH K k N) hAvoidK
      (fun v : Fin N => v)
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X) cut).CorrectedB3 family ↔
     (closureSelectedBoringData family
      (finiteNumericH L k M) hAvoidL
      (fun v : Fin M => v)
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (S.I (cut+1)) X) cut).CorrectedB3 family)
  rw [← hTail]
  exact finiteNumericH_baseExtension_same_closure_full_source_B3_stable
    family K L k b N M hNM hBlock hBin hUn hDiag
      hAvoidK hAvoidL U X hSeeds (R.I (cut+1)) cut hNoMeet

#print axioms Kk.finiteNumericH_baseExtension_old_named_source_iff
#print axioms Kk.finiteNumericH_baseExtension_same_closure_full_source_B3_stable
#print axioms Kk.numericH_two_actual_runs_baseExtension_full_source_B3_stable

end Kk
