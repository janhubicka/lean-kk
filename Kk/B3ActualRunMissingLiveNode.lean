import Kk.B3TwoActualRuns
import Kk.B3TwoRunLiveCutStarCover
import Kk.B3LiveCutStarCoverExact
import Mathlib.Tactic

/-!
# Track B: failed FULL B3 at a true run has an UNMATCHABLE live Kpt node

English-first mathematical proof and sixteen hostile checks:
  docs/track_b_actual_run_missing_live_node_english_audit.md

A full corrected-(B3) discrepancy between TWO genuine finite Henson
AlgorithmRuns on the SAME literal base E/k and source-coordinate cut
requires a concrete ACTIVE, CUT-CROSSING Kpt node in the failing
run, with a positive PHYSICAL ordinary-L edge to the tested cut,
whose COMPLETE upper ordinary-L next type is absent from the
passing run's actual active cut-star Kpt nodes.

The runs have true original-prefix seed pools and ALL generated
meet/parameter closure nodes. There is no artificial Full subset,
chosen dummy upper type, or copied E on ordinary-L age witnesses.

This does not construct the refined diary's common labelled
inverse-source orbit, relative continuation B3-loss bridge,
or unbounded big Ramsey upper/lower bounds.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A REAL live Kpt cut-crossing source on the first side whose
complete next ordinary-L reduct is POSITIVELY adjacent to cut
but is not attained by ANY truly live Kpt cut-crossing node on
the second side.

Both old and upper records are actual complete dependent L+ raw
ancestor values from ONE Kpt source index on EACH side. Equality
of the upper ordinary L reduct (not old E records) defines a match. -/
def UnmatchedLiveCutStarNode
    (family : List (NormalizedForbidden 1 0 1))
    {ParamsP ParamsQ : Type}
    (nodeP : ParamsP → AdmissibleKptNode family)
    (liveP : Nat → ParamsP → Bool)
    (nodeQ : ParamsQ → AdmissibleKptNode family)
    (liveQ : Nat → ParamsQ → Bool)
    (cut : Nat) : Prop :=
  ∃ (j : ParamsP)
    (T : PartialTypeWithE cut 1 0 1)
    (U : PartialTypeWithE (cut+1) 1 0 1),
      liveP cut j = true ∧
      kptFullOldAtCut (nodeP j) cut =
        some (⟨cut,T⟩ : RawPartialTypeNode 1 0 1) ∧
      kptFullUpperAtCut (nodeP j) cut =
        some (⟨cut+1,U⟩ : RawPartialTypeNode 1 0 1) ∧
      U.lReduct.binary
        (some (⟨cut,Nat.lt_succ_self cut⟩ : Fin (cut+1)))
        none (0 : Fin 1) = true ∧
      ¬ ∃ (i : ParamsQ)
        (S : PartialTypeWithE cut 1 0 1)
        (V : PartialTypeWithE (cut+1) 1 0 1),
          liveQ cut i = true ∧
          kptFullOldAtCut (nodeQ i) cut =
            some (⟨cut,S⟩ : RawPartialTypeNode 1 0 1) ∧
          kptFullUpperAtCut (nodeQ i) cut =
            some (⟨cut+1,V⟩ : RawPartialTypeNode 1 0 1) ∧
          V.lReduct = U.lReduct

namespace HensonRunCutData

variable
    {ell : Nat} {hell : 2 ≤ ell}
    {k : Nat} {hK : ell ≤ k+1}
    {E : Nat → Nat → Bool}
    {hLoops : ∀ i, E i i = false}
    {hSym : ∀ x y, E x y = E y x}
    {hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true)}
    {cut : Nat}

/-- Failure of the TRUE full corrected B3 test in run P and
passage in run Q forces an actual complete upper ordinary-L
type in P's indexed physical cut-star ABSENT from Q's index,
and hence forbids even a ONE-SIDED live Kpt cut-star cover P→Q.

The full-source exhaustiveness, common old L socle and intrinsic
physical cut-star projection are DERIVED from the real run data.
Only exactness of the displayed active Kpt indexes is assumed here;
the final theorem below constructs those indexes too. -/
theorem bad_good_has_missing_indexed_cutStar_type
    (P Q : HensonRunCutData ell hell k hK E hLoops hSym hClique cut)
    {ParamsP ParamsQ : Type}
    (nodeP : ParamsP → AdmissibleKptNode (hensonForbiddenFamily ell hell))
    (liveP : Nat → ParamsP → Bool)
    (nodeQ : ParamsQ → AdmissibleKptNode (hensonForbiddenFamily ell hell))
    (liveQ : Nat → ParamsQ → Bool)
    (hProjP : ∀ R : RelationalPrefixType (cut+1) 1 0 1,
      IndexedPhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
        nodeP liveP cut R ↔
      PhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
        P.occurrence.Z cut R)
    (hProjQ : ∀ R : RelationalPrefixType (cut+1) 1 0 1,
      IndexedPhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
        nodeQ liveQ cut R ↔
      PhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
        Q.occurrence.Z cut R)
    (hBad : ¬ P.occurrence.fullProfile.CorrectedB3
      (hensonForbiddenFamily ell hell))
    (hGood : Q.occurrence.fullProfile.CorrectedB3
      (hensonForbiddenFamily ell hell)) :
    ∃ R : RelationalPrefixType (cut+1) 1 0 1,
      IndexedPhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
        nodeP liveP cut R ∧
      ¬ IndexedPhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
        nodeQ liveQ cut R ∧
      ¬ IndexedCutStarLiveCover (hensonForbiddenFamily ell hell)
        nodeP liveP nodeQ liveQ cut := by
  classical
  have hOld : SameInitialL
      P.occurrence.ambient.L Q.occurrence.ambient.L cut :=
    HensonCutOccurrence.same_base_old_socle
      P.occurrence Q.occurrence rfl rfl
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
        nodeP liveP cut R := (hProjP R).mpr hPhysicalP
  have hNotIndexedQ :
      ¬ IndexedPhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
        nodeQ liveQ cut R := by
    intro hIndexedQ
    have hPhysicalQ := (hProjQ R).mp hIndexedQ
    have hAllowedQ :=
      (HensonCutOccurrence.starProfile_upperL_iff_physical_of_exhaustive
        Q.occurrence hFullQ hPoolQ R).mpr hPhysicalQ
    exact hMissing hAllowedQ
  have hNotCover :
      ¬ IndexedCutStarLiveCover (hensonForbiddenFamily ell hell)
        nodeP liveP nodeQ liveQ cut := by
    intro hCover
    have hIncluded :=
      indexed_cutStar_upperL_of_live_cover
        (hensonForbiddenFamily ell hell)
        nodeP liveP nodeQ liveQ cut hCover R hIndexedP
    exact hNotIndexedQ hIncluded
  exact ⟨R,hIndexedP,hNotIndexedQ,hNotCover⟩

/-- A TRUE FULL B3 discrepancy yields a GENUINELY LIVE Kpt node
j in the failing run's exact indexed source. It crosses cut,
has both complete dependent old and upper L+ ancestor records
from the SAME source node, and is physically L-adjacent to cut.
No live source node on the passing side has this COMPLETE upper
ordinary-L reduct, even if its old dependent E type differs. -/
theorem bad_good_has_unmatched_live_Kpt_node
    (P Q : HensonRunCutData ell hell k hK E hLoops hSym hClique cut)
    {ParamsP ParamsQ : Type}
    (nodeP : ParamsP → AdmissibleKptNode (hensonForbiddenFamily ell hell))
    (liveP : Nat → ParamsP → Bool)
    (nodeQ : ParamsQ → AdmissibleKptNode (hensonForbiddenFamily ell hell))
    (liveQ : Nat → ParamsQ → Bool)
    (hProjP : ∀ R : RelationalPrefixType (cut+1) 1 0 1,
      IndexedPhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
        nodeP liveP cut R ↔
      PhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
        P.occurrence.Z cut R)
    (hProjQ : ∀ R : RelationalPrefixType (cut+1) 1 0 1,
      IndexedPhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
        nodeQ liveQ cut R ↔
      PhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
        Q.occurrence.Z cut R)
    (hBad : ¬ P.occurrence.fullProfile.CorrectedB3
      (hensonForbiddenFamily ell hell))
    (hGood : Q.occurrence.fullProfile.CorrectedB3
      (hensonForbiddenFamily ell hell)) :
    UnmatchedLiveCutStarNode (hensonForbiddenFamily ell hell)
      nodeP liveP nodeQ liveQ cut := by
  classical
  obtain ⟨R,hInP,hNotInQ,_hNoCover⟩ :=
    bad_good_has_missing_indexed_cutStar_type
      P Q nodeP liveP nodeQ liveQ hProjP hProjQ hBad hGood
  obtain ⟨j,hLive,T,U,hOld,hUpper,hReduct,hBit⟩ :=
    indexedCutStar_has_live_physical_node
      (hensonForbiddenFamily ell hell) nodeP liveP cut R hInP
  refine ⟨j,T,U,hLive,hOld,hUpper,?_,?_⟩
  · rw [hReduct]
    exact hBit
  · rintro ⟨i,S,V,hLiveQ,hOldQ,hUpperQ,hSame⟩
    have hInQ :
        IndexedPhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
          nodeQ liveQ cut R :=
      ⟨S,V,⟨i,hLiveQ,hOldQ,hUpperQ⟩,hSame.trans hReduct,hBit⟩
    exact hNotInQ hInQ

/-- For TWO ACTUAL finite numerical-Henson AlgorithmRuns whose
FULL corrected B3 verdicts differ (first fails, second passes),
construct two ACTUAL exhaustive finite Kpt-node index universes
with exact per-cut live masks AND an unmatchable TRUE cut-adjacent
active Kpt node j in the FAILING source.

No separately postulated name pool/exhaustiveness, old-L-socle
alignment, source-index sizes or physical projection certificates:
they all follow from each genuine AlgorithmRun plus shared E,k,cut.
The remaining missing datum is a refined diary producing a
cross-occurrence matching relation (which this theorem disproves
when their B3 verdicts differ). -/
theorem two_runs_bad_good_has_finite_unmatched_live_Kpt_node
    (P Q : HensonRunCutData ell hell k hK E hLoops hSym hClique cut)
    (hBad : ¬ P.occurrence.fullProfile.CorrectedB3
      (hensonForbiddenFamily ell hell))
    (hGood : Q.occurrence.fullProfile.CorrectedB3
      (hensonForbiddenFamily ell hell)) :
    ∃ paramsP : Finset (AdmissibleKptNode (hensonForbiddenFamily ell hell)),
      ∃ liveP : Nat → Fin paramsP.card → Bool,
      ∃ paramsQ : Finset (AdmissibleKptNode (hensonForbiddenFamily ell hell)),
      ∃ liveQ : Nat → Fin paramsQ.card → Bool,
        (∀ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
          z ∈ paramsP ↔
            z ∈ SMTree.Envelope.closure
              (admissibleKptSTree (hensonForbiddenFamily ell hell))
              (P.run.I 0) P.X) ∧
        (∀ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
          z ∈ paramsQ ↔
            z ∈ SMTree.Envelope.closure
              (admissibleKptSTree (hensonForbiddenFamily ell hell))
              (Q.run.I 0) Q.X) ∧
        UnmatchedLiveCutStarNode (hensonForbiddenFamily ell hell)
          (fun j : Fin paramsP.card => (paramsP.equivFin.symm j).val)
          liveP
          (fun j : Fin paramsQ.card => (paramsQ.equivFin.symm j).val)
          liveQ cut := by
  classical
  obtain ⟨paramsP,liveP,paramsQ,liveQ,hParamsP,hParamsQ,
    hProjP,hProjQ,_hConditional⟩ :=
    two_runs_finite_indexed_cutStar_controls_full_B3 P Q
  refine ⟨paramsP,liveP,paramsQ,liveQ,hParamsP,hParamsQ,?_⟩
  exact bad_good_has_unmatched_live_Kpt_node P Q
    (fun j : Fin paramsP.card => (paramsP.equivFin.symm j).val) liveP
    (fun j : Fin paramsQ.card => (paramsQ.equivFin.symm j).val) liveQ
    hProjP hProjQ hBad hGood

end HensonRunCutData

#print axioms Kk.HensonRunCutData.bad_good_has_missing_indexed_cutStar_type
#print axioms Kk.HensonRunCutData.bad_good_has_unmatched_live_Kpt_node
#print axioms Kk.HensonRunCutData.two_runs_bad_good_has_finite_unmatched_live_Kpt_node

end Kk
