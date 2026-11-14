import Kk.B3ActualRunMissingLiveNode
import Kk.B3FullSourceCertification
import Kk.B3IndexedPhysicalCutStar
import Kk.B3LiveCutStarCoverExact
import Mathlib.Tactic

/-!
# Track B — compare TWO genuine finite Henson runs with DIFFERENT E and k

English-first adversarial audit:
  docs/track_b_different_base_actual_runs_english_audit.md

The previous two-real-run B3 theorems shared the literal base
Henson graph E and numerical generation parameter k. Here each
actual run has its OWN physical E and k, own finite truncation N,
seed pool, Kpt closure and exhaustive Kpt-node index.

The only OLD L-prefix comparison premise is the explicit
SameInitialL of their actual finite numerical-H ambients at a
COMMON SOURCE cut. There is no manufactured identification from
a selected-front graph-age F or mere K_ell-freeness.

Real original-prefix seed representation and actual AlgorithmRun
automatically discharge source completeness on BOTH sides.
The complete POSITIVE-CUT next ordinary-L spectrum is obtained
from true indexed Kpt nodes; matching these smaller spectra
suffices for the local full corrected B3 verdict.

A failed/passing discrepancy yields a genuinely LIVE physical
cut-crossing Kpt node in the failing run with NO matching complete
next ordinary-L type on the passing side. No common labelled
inverse-source orbit or global Ramsey bound is inferred.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- One completely physical finite Henson AlgorithmRun at one
source-coordinate cut. Unlike HensonRunCutData, E and k are
FIELDS, so two occurrences can have DIFFERENT base graphs
and different generation parameters.

All the source evidence is physical: actual Kpt prefix seeds,
a genuine AlgorithmRun, cut and scan bounds, and no competing
I2 at its TRUE pre-cut meet-and-parameter closure.
-/
structure HensonPhysicalRunCutData
    (ell : Nat) (hell : 2 ≤ ell) (cut : Nat) where
  k : Nat
  hK : ell ≤ k+1
  E : Nat → Nat → Bool
  hLoops : ∀ i, E i i = false
  hSym : ∀ x y, E x y = E y x
  hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
    (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true)
  N : Nat
  U : Finset (Fin N)
  hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
    bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L
  X : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell))
  hX : X ⊆ ambientPrefixPool
    (hensonForbiddenFamily ell hell)
    (finiteNumericH (normalizedGraphModel E) k N)
    hAvoid (U : Set (Fin N))
  top : Nat
  run : SMTree.Envelope.AlgorithmRun
    (normalizedKptSMTree (hensonForbiddenFamily ell hell)) X top
  hCut : cut < N
  hBelow : cut < top
  hNoI2 : ¬ ∃ a : AdmissibleKptNode (hensonForbiddenFamily ell hell),
    a ∈ SMTree.Envelope.closure
      (admissibleKptSTree (hensonForbiddenFamily ell hell))
      (run.I (cut+1)) X ∧
    ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      b ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (run.I (cut+1)) X ∧
      SMTree.Envelope.SameComponent a b ∧
      LevelTree.lev (LevelTree.meet a b) = cut

namespace HensonPhysicalRunCutData

variable {ell cut : Nat} {hell : 2 ≤ ell}

/-- A true finite AlgorithmRun supplies the EXACT full selected
original-name pool, rather than an arbitrary one-sided represented
subpool. Every actual pre-cut Kpt node is covered by a maintained
original from the final finite source, including generated parameters
and meets. -/
noncomputable abbrev occurrence
    (P : HensonPhysicalRunCutData ell hell cut) :
    HensonCutOccurrence ell cut hell :=
  actualHensonRunCutOccurrence
    ell hell P.k P.hK P.E P.hLoops P.hSym P.hClique
    P.N P.U P.hAvoid P.X P.top P.run cut P.hCut P.hNoI2

/-- Both actual original-source completeness certificates are
DERIVED for ONE physical AlgorithmRun, with its OWN base E,k.
Neither equality of another run's base nor a separately assumed
full-source selector occurs. -/
theorem occurrence_full_source_exhaustive
    (P : HensonPhysicalRunCutData ell hell cut) :
    (∀ v : Fin P.occurrence.M,
      P.occurrence.Full v ↔
        closureSelectedOriginal (hensonForbiddenFamily ell hell)
          P.occurrence.ambient P.occurrence.hAvoid
          P.occurrence.original P.occurrence.Z cut v) ∧
    (∀ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      z ∈ P.occurrence.Z →
        ∃ v : Fin P.occurrence.M,
          z ≤ P.occurrence.ambient.kptOriginal
            (hensonForbiddenFamily ell hell)
            P.occurrence.hAvoid (P.occurrence.original v)) := by
  constructor
  · exact actualHensonRunCutOccurrence_fullExact
      ell hell P.k P.hK P.E P.hLoops P.hSym P.hClique
      P.N P.U P.hAvoid P.X P.top P.run cut P.hCut P.hNoI2
  · exact actualHensonRunCutOccurrence_poolExhaustive
      ell hell P.k P.hK P.E P.hLoops P.hSym P.hClique
      P.N P.U P.hAvoid P.X P.hX P.top P.run
      cut P.hCut P.hBelow P.hNoI2

/-- Two true finite Henson AlgorithmRuns over DIFFERENT physical
base graphs, numerical generation parameters and actual Kpt sources
have equivalent complete corrected B3 tests if
  (i) their OLD ordinary-L prefixes are aligned at the same cut, and
  (ii) their intrinsic complete positive-cut upper ordinary-L
       physical spectra agree.

The exact Full source selectors and exhaustive Kpt original pools
are DERIVED from the physical AlgorithmRuns, not assumed. -/
theorem two_runs_full_B3_iff_of_old_socle_and_physical_cutStar
    (P Q : HensonPhysicalRunCutData ell hell cut)
    (hOld : SameInitialL
      P.occurrence.ambient.L Q.occurrence.ambient.L cut)
    (hPhysical : ∀ R : RelationalPrefixType (cut+1) 1 0 1,
      PhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
        P.occurrence.Z cut R ↔
      PhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
        Q.occurrence.Z cut R) :
    P.occurrence.fullProfile.CorrectedB3
      (hensonForbiddenFamily ell hell) ↔
    Q.occurrence.fullProfile.CorrectedB3
      (hensonForbiddenFamily ell hell) := by
  obtain ⟨hFullP,hPoolP⟩ := occurrence_full_source_exhaustive P
  obtain ⟨hFullQ,hPoolQ⟩ := occurrence_full_source_exhaustive Q
  exact HensonCutOccurrence.full_B3_crossAmbient_iff_of_intrinsic_physical_cutStar
    P.occurrence Q.occurrence
    hFullP hPoolP hFullQ hPoolQ hOld hPhysical

/-- A TRUE finite numerical Henson AlgorithmRun has a genuine
exhaustive finite Kpt source-node index (including all parameters
and meets) and actual per-cut live mask. Its positive-cut
complete upper ordinary-L profile is EXACTLY the intrinsic
physical profile of this run.

This uses the run's OWN E,k and original-prefix seed invariant. -/
private theorem actual_index
    (P : HensonPhysicalRunCutData ell hell cut) :
    ∃ params : Finset (AdmissibleKptNode (hensonForbiddenFamily ell hell)),
      ∃ live : Nat → Fin params.card → Bool,
        (∀ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
          z ∈ params ↔ z ∈ SMTree.Envelope.closure
            (admissibleKptSTree (hensonForbiddenFamily ell hell))
            (P.run.I 0) P.X) ∧
        (∀ R : RelationalPrefixType (cut+1) 1 0 1,
          IndexedPhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
            (fun j : Fin params.card => (params.equivFin.symm j).val)
            live cut R ↔
          PhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
            P.occurrence.Z cut R) := by
  classical
  obtain ⟨params,live,hParams,hCuts⟩ :=
    numericH_actual_run_all_cuts_indexed_cutStar
      (hensonForbiddenFamily ell hell)
      (normalizedGraphModel P.E) P.k P.N P.hAvoid
      (P.U : Set (Fin P.N)) P.X P.hX P.top P.run
  exact ⟨params,live,hParams,
    fun R => hCuts cut P.hBelow R⟩

/-- For TWO actual finite runs with distinct physical base graphs,
if their ordinary-L old socles align at one common source cut,
then a two-sided match of the TRUE LIVE cut-crossing Kpt nodes'
COMPLETE NEXT ordinary-L types suffices for full corrected B3.

The old dependent L+ node values, auxiliary E, off-cut types,
physical graph E, k and index cardinalities need NOT match.

The two genuine finite Kpt-node index sets and masks are
CONSTRUCTED; equality of positive-cut live spectra is the only
additional crossing-profile input. This does not manufacture
old-prefix alignment or a refined diary transport. -/
theorem two_runs_finite_live_cutStar_cover_controls_full_B3
    (P Q : HensonPhysicalRunCutData ell hell cut)
    (hOld : SameInitialL
      P.occurrence.ambient.L Q.occurrence.ambient.L cut) :
    ∃ paramsP : Finset (AdmissibleKptNode (hensonForbiddenFamily ell hell)),
      ∃ liveP : Nat → Fin paramsP.card → Bool,
      ∃ paramsQ : Finset (AdmissibleKptNode (hensonForbiddenFamily ell hell)),
      ∃ liveQ : Nat → Fin paramsQ.card → Bool,
        (∀ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
          z ∈ paramsP ↔ z ∈ SMTree.Envelope.closure
            (admissibleKptSTree (hensonForbiddenFamily ell hell))
            (P.run.I 0) P.X) ∧
        (∀ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
          z ∈ paramsQ ↔ z ∈ SMTree.Envelope.closure
            (admissibleKptSTree (hensonForbiddenFamily ell hell))
            (Q.run.I 0) Q.X) ∧
        (∀ R : RelationalPrefixType (cut+1) 1 0 1,
          IndexedPhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
            (fun j : Fin paramsP.card => (paramsP.equivFin.symm j).val)
            liveP cut R ↔
          PhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
            P.occurrence.Z cut R) ∧
        (∀ R : RelationalPrefixType (cut+1) 1 0 1,
          IndexedPhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
            (fun j : Fin paramsQ.card => (paramsQ.equivFin.symm j).val)
            liveQ cut R ↔
          PhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
            Q.occurrence.Z cut R) ∧
        ((IndexedCutStarLiveCover (hensonForbiddenFamily ell hell)
            (fun j : Fin paramsP.card => (paramsP.equivFin.symm j).val)
            liveP
            (fun j : Fin paramsQ.card => (paramsQ.equivFin.symm j).val)
            liveQ cut ∧
          IndexedCutStarLiveCover (hensonForbiddenFamily ell hell)
            (fun j : Fin paramsQ.card => (paramsQ.equivFin.symm j).val)
            liveQ
            (fun j : Fin paramsP.card => (paramsP.equivFin.symm j).val)
            liveP cut) →
          (P.occurrence.fullProfile.CorrectedB3
             (hensonForbiddenFamily ell hell) ↔
           Q.occurrence.fullProfile.CorrectedB3
             (hensonForbiddenFamily ell hell))) := by
  classical
  obtain ⟨paramsP,liveP,hParamsP,hProjP⟩ := actual_index P
  obtain ⟨paramsQ,liveQ,hParamsQ,hProjQ⟩ := actual_index Q
  refine ⟨paramsP,liveP,paramsQ,liveQ,
    hParamsP,hParamsQ,hProjP,hProjQ,?_⟩
  intro hCover
  have hProjected := indexed_cutStar_iff_of_bilateral_live_cover
    (hensonForbiddenFamily ell hell)
    (fun j : Fin paramsP.card => (paramsP.equivFin.symm j).val)
    liveP
    (fun j : Fin paramsQ.card => (paramsQ.equivFin.symm j).val)
    liveQ cut hCover.1 hCover.2
  apply two_runs_full_B3_iff_of_old_socle_and_physical_cutStar
    P Q hOld
  intro R
  exact (hProjP R).symm.trans
    ((hProjected R).trans (hProjQ R))

/-- If one true finite Henson AlgorithmRun fails corrected B3 and
another (possibly based on DIFFERENT E and k) passes, with aligned
OLD ordinary L-socles at a common source cut, then the failing
run has an ACTUAL LIVE Kpt source node crossing that cut, with
both full OLD/UPPER dependent L+ records and a POSITIVE physical
ordinary-L cut edge, whose COMPLETE upper ordinary-L type is
attained by NO live cut-crossing Kpt node of the passing run.

Both finite Kpt-node source indexes are CONSTRUCTED from true
AlgorithmRuns with exhaustive original-prefix representation.
No common inverse source orbit is asserted. -/
theorem two_runs_bad_good_has_finite_unmatched_live_Kpt_node
    (P Q : HensonPhysicalRunCutData ell hell cut)
    (hOld : SameInitialL
      P.occurrence.ambient.L Q.occurrence.ambient.L cut)
    (hBad : ¬ P.occurrence.fullProfile.CorrectedB3
      (hensonForbiddenFamily ell hell))
    (hGood : Q.occurrence.fullProfile.CorrectedB3
      (hensonForbiddenFamily ell hell)) :
    ∃ paramsP : Finset (AdmissibleKptNode (hensonForbiddenFamily ell hell)),
      ∃ liveP : Nat → Fin paramsP.card → Bool,
      ∃ paramsQ : Finset (AdmissibleKptNode (hensonForbiddenFamily ell hell)),
      ∃ liveQ : Nat → Fin paramsQ.card → Bool,
        (∀ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
          z ∈ paramsP ↔ z ∈ SMTree.Envelope.closure
            (admissibleKptSTree (hensonForbiddenFamily ell hell))
            (P.run.I 0) P.X) ∧
        (∀ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
          z ∈ paramsQ ↔ z ∈ SMTree.Envelope.closure
            (admissibleKptSTree (hensonForbiddenFamily ell hell))
            (Q.run.I 0) Q.X) ∧
        UnmatchedLiveCutStarNode (hensonForbiddenFamily ell hell)
          (fun j : Fin paramsP.card => (paramsP.equivFin.symm j).val)
          liveP
          (fun j : Fin paramsQ.card => (paramsQ.equivFin.symm j).val)
          liveQ cut := by
  classical
  obtain ⟨paramsP,liveP,hParamsP,hProjP⟩ := actual_index P
  obtain ⟨paramsQ,liveQ,hParamsQ,hProjQ⟩ := actual_index Q
  refine ⟨paramsP,liveP,paramsQ,liveQ,
    hParamsP,hParamsQ,?_⟩
  obtain ⟨v,hFull,hEdge,_hFree,hMissing⟩ :=
    HensonCutOccurrence.failing_full_B3_has_unmatched_cutStar_original
      P.occurrence Q.occurrence hOld hBad hGood
  let R : RelationalPrefixType (cut+1) 1 0 1 :=
    (P.occurrence.ambient.partialTypeAt
      (cut+1) (P.occurrence.original v).val).lReduct
  have hStarP : P.occurrence.starNames v := ⟨hFull,hEdge⟩
  have hAllowedP : P.occurrence.starProfile.PrescribedUpperLType R :=
    HensonCutOccurrence.star_name_complete_upperL_permitted
      P.occurrence v hStarP
  obtain ⟨hFullP,hPoolP⟩ := occurrence_full_source_exhaustive P
  obtain ⟨hFullQ,hPoolQ⟩ := occurrence_full_source_exhaustive Q
  have hPhysicalP :
      PhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
        P.occurrence.Z cut R :=
    (HensonCutOccurrence.starProfile_upperL_iff_physical_of_exhaustive
      P.occurrence hFullP hPoolP R).mp hAllowedP
  have hIndexedP :
      IndexedPhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
        (fun j : Fin paramsP.card => (paramsP.equivFin.symm j).val)
        liveP cut R := (hProjP R).mpr hPhysicalP
  have hNotIndexedQ :
      ¬ IndexedPhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
        (fun j : Fin paramsQ.card => (paramsQ.equivFin.symm j).val)
        liveQ cut R := by
    intro hIndexedQ
    have hPhysicalQ := (hProjQ R).mp hIndexedQ
    have hAllowedQ :=
      (HensonCutOccurrence.starProfile_upperL_iff_physical_of_exhaustive
        Q.occurrence hFullQ hPoolQ R).mpr hPhysicalQ
    exact hMissing hAllowedQ
  obtain ⟨j,hLive,T,U,hOldKpt,hUpperKpt,hReduct,hBit⟩ :=
    indexedCutStar_has_live_physical_node
      (hensonForbiddenFamily ell hell)
      (fun t : Fin paramsP.card => (paramsP.equivFin.symm t).val)
      liveP cut R hIndexedP
  refine ⟨j,T,U,hLive,hOldKpt,hUpperKpt,?_,?_⟩
  · rw [hReduct]
    exact hBit
  · rintro ⟨i,S,V,hLiveQ,hOldQ,hUpperQ,hEq⟩
    have hInQ :
        IndexedPhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
          (fun t : Fin paramsQ.card => (paramsQ.equivFin.symm t).val)
          liveQ cut R :=
      ⟨S,V,⟨i,hLiveQ,hOldQ,hUpperQ⟩,hEq.trans hReduct,hBit⟩
    exact hNotIndexedQ hInQ

end HensonPhysicalRunCutData

#print axioms Kk.HensonPhysicalRunCutData.occurrence_full_source_exhaustive
#print axioms Kk.HensonPhysicalRunCutData.two_runs_full_B3_iff_of_old_socle_and_physical_cutStar
#print axioms Kk.HensonPhysicalRunCutData.two_runs_finite_live_cutStar_cover_controls_full_B3
#print axioms Kk.HensonPhysicalRunCutData.two_runs_bad_good_has_finite_unmatched_live_Kpt_node

end Kk
