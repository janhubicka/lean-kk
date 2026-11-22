import Kk.TrackECandidateSourceFiniteIndex
import Kk.TrackAOddIndexedStructuralBudget
import Mathlib.Tactic

/-!
# Track A/G: automatically indexed actual odd Kpt Bad-cut budget

English proof and hostile audit written FIRST:
docs/track_a_odd_bad_automatic_candidate_index_english_audit_20261122.md

Combines already verified Track E E70 candidate full-Kpt closure
index on ONE OLD AlgorithmRun with verified Track A/G odd Bad source
structural-level count. No new Y-run is assumed or constructed.
Finite Q depends on numeric H carrier; no uniform BRD claim.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

/-- Any represented candidate Y, compared along an ACTUAL OLD run
R on X, has a constructed exhaustive finite full dependent Kpt index.
For that very index, the exact old-factor Bad ODD cut set has size at
most Q+Q² plus actual cuts lacking an old complete lower Kpt socle.
The existence of the candidate source index is a CONCLUSION, not
an additional hypothesis. -/
theorem finiteNumericH_odd_bad_budget_exists_exact_candidate_index
    (family : List (NormalizedForbidden 1 0 1))
    (K : AgeTestModel 1 0 1) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hSym : ∀ i j : Nat,
      (finiteNumericH K k N).L.binary i j (0 : Fin 1) =
        (finiteNumericH K k N).L.binary j i (0 : Fin 1))
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid (U : Set (Fin N)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top) :
    ∃ params : Finset (AdmissibleKptNode family),
      ∃ live : Nat → Fin params.card → Bool,
        (∀ cut : Nat, cut < top →
          ∀ z : AdmissibleKptNode family,
            z ∈ SMTree.Envelope.closure
              (admissibleKptSTree family) (R.I (cut+1)) Y ↔
            ∃ i : Fin params.card,
              (params.equivFin.symm i).val = z ∧
              live cut i = true) ∧
        (kptOddExactBadCuts family X top R
          (fun i : Fin params.card => (params.equivFin.symm i).val)
          live).card ≤
          params.card + params.card*params.card +
          (kptOddMissingOldSocleCuts family X top R
            (fun i : Fin params.card => (params.equivFin.symm i).val)
            live).card := by
  classical
  obtain ⟨params,live,_hFinal,_hInjective,_hPresent,hExact⟩ :=
    finiteNumericH_oldRun_candidate_uniform_exhaustive_source_index
      family K k N hAvoid (U : Set (Fin N)) X Y hY top R
  refine ⟨params,live,hExact,?_⟩
  exact finiteNumericH_odd_bad_card_le_structural_plus_missing
    family K k N params.card hAvoid hSym U X Y hXY hY
    top R (fun i : Fin params.card => (params.equivFin.symm i).val)
    live hExact

/-- If EVERY actual ODD candidate crossing has a matching complete
OLD Kpt lower ancestor in the old pre-cut closure, an exact finite
candidate index EXISTS and all old-factor Bad odd cuts are among at
most Q+Q² terminal/meet source levels. No Y-run is assumed. -/
theorem finiteNumericH_odd_bad_budget_exists_of_full_old_socle
    (family : List (NormalizedForbidden 1 0 1))
    (K : AgeTestModel 1 0 1) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hSym : ∀ i j : Nat,
      (finiteNumericH K k N).L.binary i j (0 : Fin 1) =
        (finiteNumericH K k N).L.binary j i (0 : Fin 1))
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid (U : Set (Fin N)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (hSocle : ∀ cut : Nat, cut < top → cut % 2 = 1 →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) Y →
        ∀ (hCross : cut < LevelTree.lev z),
          ∃ w : AdmissibleKptNode family,
            w ∈ SMTree.Envelope.closure
              (admissibleKptSTree family) (R.I (cut+1)) X ∧
            ∃ (hWCross : cut < LevelTree.lev w),
              LevelTree.ancestor z cut (Nat.le_of_lt hCross) =
                LevelTree.ancestor w cut (Nat.le_of_lt hWCross)) :
    ∃ params : Finset (AdmissibleKptNode family),
      ∃ live : Nat → Fin params.card → Bool,
        (∀ cut : Nat, cut < top →
          ∀ z : AdmissibleKptNode family,
            z ∈ SMTree.Envelope.closure
              (admissibleKptSTree family) (R.I (cut+1)) Y ↔
            ∃ i : Fin params.card,
              (params.equivFin.symm i).val = z ∧
              live cut i = true) ∧
        (kptOddExactBadCuts family X top R
          (fun i : Fin params.card => (params.equivFin.symm i).val)
          live).card ≤
          params.card + params.card*params.card := by
  classical
  obtain ⟨params,live,_hFinal,_hInjective,hPresent,hExact⟩ :=
    finiteNumericH_oldRun_candidate_uniform_exhaustive_source_index
      family K k N hAvoid (U : Set (Fin N)) X Y hY top R
  let node : Fin params.card → AdmissibleKptNode family :=
    fun i => (params.equivFin.symm i).val
  have hNoMissing :
      kptOddMissingOldSocleCuts family X top R node live = ∅ := by
    ext cut
    constructor
    · intro hc
      exfalso
      have hFilter : cut ∈
        (Finset.range top).filter
          (fun cut => cut % 2 = 1 ∧
            kptMissingOldSocleAt family X top R node live cut) := hc
      obtain ⟨hRange,hOdd,hMissing⟩ := Finset.mem_filter.mp hFilter
      obtain ⟨i,hLive,hCross,hNoOld⟩ := hMissing
      have hz : node i ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y :=
      (hPresent cut i).mp hLive
      exact hNoOld
        (hSocle cut (Finset.mem_range.mp hRange) hOdd
          (node i) hz hCross)
    · simp
  refine ⟨params,live,hExact,?_⟩
  have hBound :=
    finiteNumericH_odd_bad_card_le_of_no_missing_old_socle
      family K k N params.card hAvoid hSym U X Y hXY hY
      top R node live hExact hNoMissing
  exact hBound

#print axioms Kk.finiteNumericH_odd_bad_budget_exists_exact_candidate_index
#print axioms Kk.finiteNumericH_odd_bad_budget_exists_of_full_old_socle

end Kk
