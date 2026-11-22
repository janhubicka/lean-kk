import Kk.TrackAOddOldSocleFrontier
import Kk.TrackACandidateDescendantRawSocle
import Kk.TrackECandidateSourceFiniteIndex
import Mathlib.Tactic

/-!
# Track A/C/G: concrete RAW type matching at one maximal odd cut per candidate

English proof and hostile audit first:
 docs/track_a_odd_bad_raw_max_seed_match_english_audit_20261122.md

Based on three verified ingredients: E70 constructs the true
candidate source index on ONE OLD run; Track A/G #503 reduces
complete OLD lower-socle coverage to ONE maximal odd old-boring
live crossing cut per candidate; Track A/C #509 certifies that
lower ancestor by a complete physical RAW old-seed type equality,
even for a non-original candidate node below a physical original.

No candidate Y-run, no uniform bound on Q, no diary raw matching
existence theorem, and no global BRD conclusion.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

/-- A finite actual physical numerical-H+ model and ONE old Kpt
AlgorithmRun construct an exhaustive candidate index and reduce
the genuine old-factor Bad odd-cut count to Q+Q², conditional
only on ONE COMPLETE numerical RAW old-seed match per candidate
at its highest ODD OLD-BORING LIVE CROSSING cut.

The input is a concrete `KptRawOldSeedMatchAt` on physical
originals O_u and O_v with candidate source node below O_v;
the output is independent of any presumed new Y-run. -/
theorem finiteNumericH_odd_bad_budget_exists_of_raw_max_candidate_seed_matches
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
      ((∀ i : Fin params.card,
        ∀ hNonempty : (kptOddOldBoringCandidateCrossingCuts
          family X top R
          (fun j : Fin params.card => (params.equivFin.symm j).val)
          live i).Nonempty,
        ∃ v : Fin N,
          (params.equivFin.symm i).val ≤
            (finiteNumericH K k N).kptOriginal family hAvoid v ∧
          KptRawOldSeedMatchAt family K k N hAvoid X v
            ((kptOddOldBoringCandidateCrossingCuts
              family X top R
              (fun j : Fin params.card =>
                (params.equivFin.symm j).val) live i).max' hNonempty)) →
      (kptOddExactBadCuts family X top R
        (fun j : Fin params.card => (params.equivFin.symm j).val)
        live).card ≤ params.card + params.card*params.card) := by
  classical
  obtain ⟨params,live,_hFinal,_hInjective,_hPresent,hExact⟩ :=
    finiteNumericH_oldRun_candidate_uniform_exhaustive_source_index
      family K k N hAvoid (U : Set (Fin N)) X Y hY top R
  let node : Fin params.card → AdmissibleKptNode family :=
    fun j => (params.equivFin.symm j).val
  refine ⟨params,live,hExact,?_⟩
  intro hRawMax
  have hMaxSocle : ∀ i : Fin params.card,
      ∀ hNonempty : (kptOddOldBoringCandidateCrossingCuts
        family X top R node live i).Nonempty,
      KptActualOldSocleCoveredAt family X top R (node i)
        ((kptOddOldBoringCandidateCrossingCuts
          family X top R node live i).max' hNonempty) := by
    intro i hNonempty
    let C := kptOddOldBoringCandidateCrossingCuts
      family X top R node live i
    obtain ⟨v,hBelow,hSeedMatch⟩ := hRawMax i hNonempty
    have hMaxMember : C.max' hNonempty ∈ C :=
      Finset.max'_mem C hNonempty
    have hCross : C.max' hNonempty < LevelTree.lev (node i) :=
      (Finset.mem_filter.mp hMaxMember).2.2.2.2
    exact finiteNumericH_candidate_below_original_old_socle_of_raw_seed_match
      family K k N hAvoid X top R v (node i)
      hBelow (C.max' hNonempty) hCross hSeedMatch
  exact finiteNumericH_odd_bad_card_le_of_max_lower_socles
    family K k N params.card hAvoid hSym U X Y hXY hY
      top R node live hExact hMaxSocle

#print axioms Kk.finiteNumericH_odd_bad_budget_exists_of_raw_max_candidate_seed_matches

end Kk
