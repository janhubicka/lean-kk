import Kk.B3RelevantBaseOldSocle
import Kk.B3DifferentBaseActualRuns
import Mathlib.Tactic

/-!
# Track B — TWO real Henson runs, FINITE old base-pair and live cut-star tests

English-first mathematical proof and 15 hostile checks:
  docs/track_b_two_runs_relevant_base_live_transfer_english_audit.md

The earlier true two-run physical comparison with DIFFERENT base E
and generation k requires an explicit old ordinary-L prefix
SameInitialL. This module DISCHARGES that premise when the two
runs use the SAME generation k and their (possibly different)
base graphs agree only on the FINITELY many real generation
pairs whose numeric H copy positions lie at or before cut.

Each run's full Kpt source exactness and original-prefix
exhaustiveness are independently DERIVED from its true physical
AlgorithmRun. Equality of the intrinsic positive-cut COMPLETE
next ordinary-L spectra (equivalently bilateral LIVE Kpt cut-star
name coverage with true indexed source masks) then suffices for
FULL corrected B3 agreement. This is NOT an unbounded diary theorem.
-/

namespace Kk
namespace HensonPhysicalRunCutData

open SuccessorTree
open SuccessorTree.V10

variable {ell cut : Nat} {hell : 2 ≤ ell}

/-- Two ACTUAL finite Henson AlgorithmRuns with different physical
base E can have the SAME complete old ordinary-L socle through
cut even when their entire base graphs are NOT equal.

It suffices that they share generation k and the two directed
base edge atoms agree on only finitely many RelevantBasePairs
whose allowed real H copies lie at/below this literal cut.
The base loops agree automatically by physical Henson irreflexivity.
-/
theorem old_socle_of_relevant_base_pairs
    (P Q : HensonPhysicalRunCutData ell hell cut)
    (hk : P.k = Q.k)
    (hBase : ∀ i j,
      HensonRelevantBasePair P.k cut i j →
      P.E i j = Q.E i j ∧ P.E j i = Q.E j i) :
    SameInitialL P.occurrence.ambient.L Q.occurrence.ambient.L cut := by
  exact HensonCutOccurrence.old_socle_of_relevant_base_pair_agreement
    P.occurrence Q.occurrence hk hBase

/-- At two genuine physically exhaustive Henson AlgorithmRuns
over different base graphs but a common numerical generation k
and source cut, matching only the finite OLD relevant directed
base edge pairs plus the intrinsic positive-cut COMPLETE next
ordinary-L spectra suffices for equivalence of FULL corrected B3.

The old-L prefix alignment and source-exhaustiveness are DERIVED
from these actual physical data rather than independently assumed.
Equality of positive-cut upper profiles remains a real hypothesis
not proved by an unrefined selected macrodiary. -/
theorem full_B3_iff_of_relevant_base_and_intrinsic_cutStar
    (P Q : HensonPhysicalRunCutData ell hell cut)
    (hk : P.k = Q.k)
    (hBase : ∀ i j,
      HensonRelevantBasePair P.k cut i j →
      P.E i j = Q.E i j ∧ P.E j i = Q.E j i)
    (hPhysical : ∀ R : RelationalPrefixType (cut+1) 1 0 1,
      PhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
        P.occurrence.Z cut R ↔
      PhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
        Q.occurrence.Z cut R) :
    P.occurrence.fullProfile.CorrectedB3
      (hensonForbiddenFamily ell hell) ↔
    Q.occurrence.fullProfile.CorrectedB3
      (hensonForbiddenFamily ell hell) := by
  exact two_runs_full_B3_iff_of_old_socle_and_physical_cutStar
    P Q (old_socle_of_relevant_base_pairs P Q hk hBase) hPhysical

/-- Application-facing LIVE finite Kpt index version: the old-L
prefix is aligned by the FINITE real-base-pair edge agreement,
and the physically exact indexed source spectra agree if their
true live cut-crossing Kpt nodes match in both directions by
COMPLETE NEXT ordinary-L type at a positive physical cut edge.

There is no requirement for old dependent E/source L+ equality,
equal finite Kpt index cardinalities, common source-name labels,
or equality of entire physical base graphs. The exact index
projection hypotheses can be CONSTRUCTED from each actual run
by the previously verified all-cuts true-Kpt-index theorem. -/
theorem full_B3_iff_of_relevant_base_and_live_cover
    (P Q : HensonPhysicalRunCutData ell hell cut)
    (hk : P.k = Q.k)
    (hBase : ∀ i j,
      HensonRelevantBasePair P.k cut i j →
      P.E i j = Q.E i j ∧ P.E j i = Q.E j i)
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
    (hAB : IndexedCutStarLiveCover (hensonForbiddenFamily ell hell)
      nodeP liveP nodeQ liveQ cut)
    (hBA : IndexedCutStarLiveCover (hensonForbiddenFamily ell hell)
      nodeQ liveQ nodeP liveP cut) :
    P.occurrence.fullProfile.CorrectedB3
      (hensonForbiddenFamily ell hell) ↔
    Q.occurrence.fullProfile.CorrectedB3
      (hensonForbiddenFamily ell hell) := by
  apply full_B3_iff_of_relevant_base_and_intrinsic_cutStar
    P Q hk hBase
  intro R
  have hIndexed :=
    indexed_cutStar_iff_of_bilateral_live_cover
      (hensonForbiddenFamily ell hell)
      nodeP liveP nodeQ liveQ cut hAB hBA R
  exact (hProjP R).symm.trans
    (hIndexed.trans (hProjQ R))

/-- With the literal finite-base OLD socle alignment, a full
corrected-B3 discrepancy between two actual Henson AlgorithmRuns
of different physical base E forces a COMPLETE positive-cut
ordinary-L type in the FAILING run's true physical Kpt closure
which is ABSENT from the passing run's intrinsic cut-star.

This witness is source-exact: no hypothetical all-eligible
original or selected graph-age F is substituted for the true
Kpt meet/parameter-closed source. -/
theorem bad_good_has_missing_intrinsic_cutStar_type_of_relevant_base
    (P Q : HensonPhysicalRunCutData ell hell cut)
    (hk : P.k = Q.k)
    (hBase : ∀ i j,
      HensonRelevantBasePair P.k cut i j →
      P.E i j = Q.E i j ∧ P.E j i = Q.E j i)
    (hBad : ¬ P.occurrence.fullProfile.CorrectedB3
      (hensonForbiddenFamily ell hell))
    (hGood : Q.occurrence.fullProfile.CorrectedB3
      (hensonForbiddenFamily ell hell)) :
    ∃ R : RelationalPrefixType (cut+1) 1 0 1,
      PhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
        P.occurrence.Z cut R ∧
      ¬ PhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
        Q.occurrence.Z cut R := by
  classical
  have hOld := old_socle_of_relevant_base_pairs
    P Q hk hBase
  obtain ⟨v,hFull,hEdge,_hEligible,hMissing⟩ :=
    HensonCutOccurrence.failing_full_B3_has_unmatched_cutStar_original
      P.occurrence Q.occurrence hOld hBad hGood
  let R : RelationalPrefixType (cut+1) 1 0 1 :=
    (P.occurrence.ambient.partialTypeAt
      (cut+1) (P.occurrence.original v).val).lReduct
  have hStar : P.occurrence.starNames v := ⟨hFull,hEdge⟩
  have hAllowedP : P.occurrence.starProfile.PrescribedUpperLType R :=
    HensonCutOccurrence.star_name_complete_upperL_permitted
      P.occurrence v hStar
  obtain ⟨hFullP,hPoolP⟩ := occurrence_full_source_exhaustive P
  obtain ⟨hFullQ,hPoolQ⟩ := occurrence_full_source_exhaustive Q
  have hPhysicalP :
      PhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
        P.occurrence.Z cut R :=
    (HensonCutOccurrence.starProfile_upperL_iff_physical_of_exhaustive
      P.occurrence hFullP hPoolP R).mp hAllowedP
  have hNotPhysicalQ :
      ¬ PhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
        Q.occurrence.Z cut R := by
    intro hPhysicalQ
    have hAllowedQ :=
      (HensonCutOccurrence.starProfile_upperL_iff_physical_of_exhaustive
        Q.occurrence hFullQ hPoolQ R).mpr hPhysicalQ
    exact hMissing hAllowedQ
  exact ⟨R,hPhysicalP,hNotPhysicalQ⟩

end HensonPhysicalRunCutData

#print axioms Kk.HensonPhysicalRunCutData.old_socle_of_relevant_base_pairs
#print axioms Kk.HensonPhysicalRunCutData.full_B3_iff_of_relevant_base_and_intrinsic_cutStar
#print axioms Kk.HensonPhysicalRunCutData.full_B3_iff_of_relevant_base_and_live_cover
#print axioms Kk.HensonPhysicalRunCutData.bad_good_has_missing_intrinsic_cutStar_type_of_relevant_base

end Kk
