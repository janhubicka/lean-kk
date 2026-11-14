import Kk.B3FullSourceCertification
import Kk.IndexedPhysicalCrossing
import Mathlib.Tactic

/-!
# Track B: finite indexed physical cut-star records from TRUE Kpt sources

English-first mathematical proof and 18 adversarial checks:
  docs/track_b_indexed_physical_cutstar_english_audit.md

The complete physical Kpt crossing relation is already indexed by
Track E's finite TRUE final closure-node universe and exact
per-cut active Boolean mask. Here we take ONLY the intrinsic
positive-cut complete upper ordinary-L projection relevant to B3.

Unlike the stronger Track E pair-matching criterion, this forgets
irrelevant off-cut old/upper sources and auxiliary E after the
physical source has been correctly identified. No-(I2) is NOT
required for the physical relation/projection itself; it is
required later for a corrected-B3 partial function.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- An actual FINITE Kpt-node index with a per-cut live mask
represents a complete positive-cut ordinary-L upper type R iff
SOME live node has a COMPLETE OLD/UPPER L+ ancestor pair and
the physical next upper L-reduct equals R and is L-adjacent
to the tested coordinate.

The source-index j in IndexedPhysicalCrossing supplies BOTH
old and upper values; no fictitious E on age-test continuations. -/
def IndexedPhysicalCutStarUpperL
    (family : List (NormalizedForbidden 1 0 1))
    {Params : Type}
    (node : Params → AdmissibleKptNode family)
    (presentAt : Nat → Params → Bool)
    (cut : Nat)
    (R : RelationalPrefixType (cut+1) 1 0 1) : Prop :=
  ∃ T : PartialTypeWithE cut 1 0 1,
    ∃ U : PartialTypeWithE (cut+1) 1 0 1,
      (T,U) ∈ IndexedPhysicalCrossing family node presentAt cut ∧
      U.lReduct = R ∧
      R.binary
        (some (⟨cut,Nat.lt_succ_self cut⟩ : Fin (cut+1)))
        none (0 : Fin 1) = true

/-- Every finite indexed physical cut-star type is carried by
ONE GENUINELY LIVE, CUT-CROSSING Kpt node and its complete
actual old/upper dependent-L+ ancestor records. -/
theorem indexedCutStar_has_live_physical_node
    (family : List (NormalizedForbidden 1 0 1))
    {Params : Type}
    (node : Params → AdmissibleKptNode family)
    (presentAt : Nat → Params → Bool)
    (cut : Nat)
    (R : RelationalPrefixType (cut+1) 1 0 1)
    (hR : IndexedPhysicalCutStarUpperL family node presentAt cut R) :
    ∃ j : Params, presentAt cut j = true ∧
      ∃ T : PartialTypeWithE cut 1 0 1,
        ∃ U : PartialTypeWithE (cut+1) 1 0 1,
          kptFullOldAtCut (node j) cut =
            some (⟨cut,T⟩ : RawPartialTypeNode 1 0 1) ∧
          kptFullUpperAtCut (node j) cut =
            some (⟨cut+1,U⟩ : RawPartialTypeNode 1 0 1) ∧
          U.lReduct = R ∧
          R.binary
            (some (⟨cut,Nat.lt_succ_self cut⟩ : Fin (cut+1)))
            none (0 : Fin 1) = true := by
  obtain ⟨T,U,⟨j,hLive,hOld,hUpper⟩,hRed,hBit⟩ := hR
  exact ⟨j,hLive,T,U,hOld,hUpper,hRed,hBit⟩

/-- Exact live-index coverage of the REAL Kpt source makes the
finite indexed cut-star upper-L spectrum literally equivalent
to the intrinsic, original-name-INDEPENDENT physical cut-star
projection of the full actual L+ crossing relation.

No no-(I2) hypothesis is required for this relation-level equality. -/
theorem indexedCutStar_iff_physical_of_exact
    (family : List (NormalizedForbidden 1 0 1))
    {Params : Type}
    (node : Params → AdmissibleKptNode family)
    (presentAt : Nat → Params → Bool)
    (Z : Set (AdmissibleKptNode family))
    (cut : Nat)
    (hExact : ∀ z : AdmissibleKptNode family,
      z ∈ Z ↔ ∃ j : Params,
        node j = z ∧ presentAt cut j = true)
    (R : RelationalPrefixType (cut+1) 1 0 1) :
    IndexedPhysicalCutStarUpperL family node presentAt cut R ↔
      PhysicalCutStarUpperL family Z cut R := by
  have hPhysical :=
    indexed_physical_crossing_eq_full_closure_relation
      family node presentAt Z cut hExact
  change (∃ T U,
      (T,U) ∈ IndexedPhysicalCrossing family node presentAt cut ∧
      U.lReduct = R ∧
      R.binary
        (some (⟨cut,Nat.lt_succ_self cut⟩ : Fin (cut+1)))
        none (0 : Fin 1) = true) ↔
    (∃ T U,
      (T,U) ∈ FullPhysicalClosureCrossing family Z cut ∧
      U.lReduct = R ∧
      R.binary
        (some (⟨cut,Nat.lt_succ_self cut⟩ : Fin (cut+1)))
        none (0 : Fin 1) = true)
  rw [hPhysical]

/-- An actual finite numerical-H AlgorithmRun has ONE finite
true Kpt-node universe and a Boolean active mask that computes
the intrinsic physical cut-star complete upper-L spectrum at
EVERY cut in the scan. This is independent of all original-name
pools and does not assume absence of I2.

The final closure can contain meets and positive parameters
as well as seed originals; all are actually indexed. -/
theorem numericH_actual_run_all_cuts_indexed_cutStar
    (family : List (NormalizedForbidden 1 0 1))
    (K : AgeTestModel 1 0 1) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Set (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid U)
    (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top) :
    ∃ params : Finset (AdmissibleKptNode family),
      ∃ presentAt : Nat → Fin params.card → Bool,
        (∀ z : AdmissibleKptNode family,
          z ∈ params ↔
            z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
              (Run.I 0) X) ∧
        (∀ cut, cut < top →
          ∀ R : RelationalPrefixType (cut+1) 1 0 1,
            IndexedPhysicalCutStarUpperL family
              (fun j : Fin params.card => (params.equivFin.symm j).val)
              presentAt cut R ↔
            PhysicalCutStarUpperL family
              (SMTree.Envelope.closure (admissibleKptSTree family)
                (Run.I (cut+1)) X) cut R) := by
  classical
  obtain ⟨params,presentAt,hParams,hCuts⟩ :=
    numericH_actual_run_all_cuts_indexed_physical_crossing
      family K k N hAvoid U X hX top Run
  refine ⟨params,presentAt,hParams,?_⟩
  intro cut hCut R
  have hCross := hCuts cut hCut
  change IndexedPhysicalCrossing family
      (fun j : Fin params.card => (params.equivFin.symm j).val)
        presentAt cut =
      FullPhysicalClosureCrossing family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (Run.I (cut+1)) X) cut at hCross
  change (∃ T U,
      (T,U) ∈ IndexedPhysicalCrossing family
        (fun j : Fin params.card => (params.equivFin.symm j).val)
        presentAt cut ∧
      U.lReduct = R ∧
      R.binary
        (some (⟨cut,Nat.lt_succ_self cut⟩ : Fin (cut+1)))
        none (0 : Fin 1) = true) ↔
    (∃ T U,
      (T,U) ∈ FullPhysicalClosureCrossing family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (Run.I (cut+1)) X) cut ∧
      U.lReduct = R ∧
      R.binary
        (some (⟨cut,Nat.lt_succ_self cut⟩ : Fin (cut+1)))
        none (0 : Fin 1) = true)
  rw [hCross]

/-- Matching ONLY the finite indexed POSITIVE-CUT next-L spectra
in TWO exact active source indexes implies that the canonical
physical closure cut-star spectra coincide. Unlike Track E's
complete old/upper L+ PAIR matching, this does not require
matching off-cut source types, fake E columns or multiplicities.

The source coordinate and exact active-node coverage are still
genuine hypotheses, not consequences of a selected macrodiary. -/
theorem two_closures_physical_cutStar_eq_of_indexed_projection
    (family : List (NormalizedForbidden 1 0 1))
    {Params₁ Params₂ : Type}
    (node₁ : Params₁ → AdmissibleKptNode family)
    (node₂ : Params₂ → AdmissibleKptNode family)
    (live₁ : Nat → Params₁ → Bool)
    (live₂ : Nat → Params₂ → Bool)
    (Z₁ Z₂ : Set (AdmissibleKptNode family))
    (cut : Nat)
    (hExact₁ : ∀ z : AdmissibleKptNode family,
      z ∈ Z₁ ↔ ∃ j : Params₁,
        node₁ j = z ∧ live₁ cut j = true)
    (hExact₂ : ∀ z : AdmissibleKptNode family,
      z ∈ Z₂ ↔ ∃ j : Params₂,
        node₂ j = z ∧ live₂ cut j = true)
    (hProjected : ∀ R : RelationalPrefixType (cut+1) 1 0 1,
      IndexedPhysicalCutStarUpperL family node₁ live₁ cut R ↔
      IndexedPhysicalCutStarUpperL family node₂ live₂ cut R) :
    ∀ R : RelationalPrefixType (cut+1) 1 0 1,
      PhysicalCutStarUpperL family Z₁ cut R ↔
      PhysicalCutStarUpperL family Z₂ cut R := by
  intro R
  exact (indexedCutStar_iff_physical_of_exact
    family node₁ live₁ Z₁ cut hExact₁ R).symm.trans
      ((hProjected R).trans
        (indexedCutStar_iff_physical_of_exact
          family node₂ live₂ Z₂ cut hExact₂ R))

#print axioms indexedCutStar_has_live_physical_node
#print axioms indexedCutStar_iff_physical_of_exact
#print axioms numericH_actual_run_all_cuts_indexed_cutStar
#print axioms two_closures_physical_cutStar_eq_of_indexed_projection

end Kk
