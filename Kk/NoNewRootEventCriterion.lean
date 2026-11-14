import Kk.NewRootIndexedNovelty
import Kk.ActualRunLevelProfileSync
import Mathlib.Tactic

/-!
# Track E: one-sided NO-NOVELTY criterion for genuine new-root runs

Actual closure and IsInterestingAt are monotone under X⊆Y. Hence
the old pre-cut source/crossing data is automatically contained in
the new source/crossing data; to obtain exact selected-level equality
it is enough to rule out NEW terminal and full old/upper L+ pairs.

This is a more economical source-growth criterion than comparing
two full records in both directions without using monotonicity.

A finite-index version tests actual live COMPLETE Kpt nodes of the
new run, using BOTH old and upper dependent type values of the
SAME live index. It retains I2 branches and auxiliary E.

English-first proof and hostile audit:
  docs/track_e_monotone_seed_growth_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- One-sided NEW-source inertness at a source cut. It says:
  (i) no genuinely NEW terminal I1 *existence* event;
  (ii) no genuinely NEW complete old/upper dependent L+ pair.

For seed growth the reverse implications follow automatically
from actual closure monotonicity; no isomorphism or bidirectional
source matching is postulated. -/
def NewRootNoNoveltyAtCut
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldSource newSource : Set (AdmissibleKptNode family))
    (cut : Nat) : Prop :=
  (KptI1AtCut family newSource cut →
    KptI1AtCut family oldSource cut) ∧
  FullPhysicalClosureCrossing family newSource cut ⊆
    FullPhysicalClosureCrossing family oldSource cut

/-- If the actual NEW complete pre-cut closure creates neither
a new terminal existence nor a new old/upper L+ crossing pair
at ANY scanned cut, two genuine same-top runs on seed sets
X⊆Y have exactly the SAME selected levels at EVERY stage.

The OLD⇒NEW profile direction is **DERIVED** from real
seed/level-set monotonicity; one only checks NEW⇒OLD.
The semantic I3 transfer is the REAL monoid-level result, not
a B3 converse or selected-shadow approximation. -/
theorem two_actual_Kpt_runs_levels_eq_of_one_sided_no_novelty
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y) (top : Nat)
    (RunX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (RunY : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y top)
    (hNoNovelty : ∀ cut : Nat, cut < top →
      NewRootNoNoveltyAtCut family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RunX.I (cut+1)) X)
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RunY.I (cut+1)) Y) cut) :
    ∀ i : Nat, i ≤ top → RunX.I i = RunY.I i := by
  have hSelectedSub :=
    actual_AlgorithmRun_selected_levels_mono_of_seed_growth
      (normalizedKptSMTree family) X Y hXY top RunX RunY
  apply two_actual_Kpt_runs_level_sets_eq_of_stagewise_full_profiles
    family X Y top RunX RunY
  intro cut hCut _hHigher
  let ZX : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (RunX.I (cut+1)) X
  let ZY : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (RunY.I (cut+1)) Y
  have hSub : ZX ⊆ ZY :=
    envelope_closure_mono_both
      (RunX.I (cut+1)) (RunY.I (cut+1)) X Y
      (hSelectedSub (cut+1) (by omega)) hXY
  obtain ⟨hNewTerm,hNewCross⟩ := hNoNovelty cut hCut
  have hTerminal :
      KptI1AtCut family ZX cut ↔
      KptI1AtCut family ZY cut := by
    constructor
    · rintro ⟨z,hz,hLevel⟩
      exact ⟨z,hSub hz,hLevel⟩
    · exact hNewTerm
  have hCrossSub :
      FullPhysicalClosureCrossing family ZX cut ⊆
      FullPhysicalClosureCrossing family ZY cut :=
    full_physical_crossing_mono_of_source_subset
      family ZX ZY hSub cut
  exact ⟨hTerminal,Set.Subset.antisymm hCrossSub hNewCross⟩

/-- Application-facing FINITE source check at all cuts of TWO true
Kpt runs with X⊆Y. The P-indexed source is exact for each
pre-cut closure of the larger run; it need not be identified with
the old source index.

To prove equal selected levels, check only (1) each LIVE,
cut-TERMINAL new node's level already has an old terminal
witness and (2) each LIVE, cut-CROSSING node's complete
old/upper L+ pair is already realized by the old full Kpt
closure at that cut.

This uses exactly one physical name j for BOTH full types;
fake E and negative L atoms remain in the raw Kpt records.
No-(I2), no graph-age surrogate and no common labelled orbit
are assumed. -/
theorem two_actual_Kpt_runs_levels_eq_of_finite_indexed_quiet_source
    {db du dd P : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y) (top : Nat)
    (RunX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (RunY : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y top)
    (node : Fin P → AdmissibleKptNode family)
    (live : Nat → Fin P → Bool)
    (hExact : ∀ cut : Nat, cut < top →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (RunY.I (cut+1)) Y ↔
        ∃ j : Fin P, node j = z ∧ live cut j = true)
    (hTerminal : ∀ cut : Nat, cut < top →
      ∀ j : Fin P, live cut j = true →
        LevelTree.lev (node j) = cut →
          KptI1AtCut family
            (SMTree.Envelope.closure (admissibleKptSTree family)
              (RunX.I (cut+1)) X) cut)
    (hCrossing : ∀ cut : Nat, cut < top →
      ∀ j : Fin P, live cut j = true →
        ∀ T : PartialTypeWithE cut db du dd,
          ∀ U : PartialTypeWithE (cut+1) db du dd,
            kptFullOldAtCut (node j) cut =
              some (⟨cut,T⟩ : RawPartialTypeNode db du dd) →
            kptFullUpperAtCut (node j) cut =
              some (⟨cut+1,U⟩ : RawPartialTypeNode db du dd) →
            (T,U) ∈ FullPhysicalClosureCrossing family
              (SMTree.Envelope.closure (admissibleKptSTree family)
                (RunX.I (cut+1)) X) cut) :
    ∀ i : Nat, i ≤ top → RunX.I i = RunY.I i := by
  apply two_actual_Kpt_runs_levels_eq_of_one_sided_no_novelty
    family X Y hXY top RunX RunY
  intro cut hCut
  let ZX : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (RunX.I (cut+1)) X
  let ZY : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (RunY.I (cut+1)) Y
  constructor
  · rintro ⟨z,hZ,hLevel⟩
    obtain ⟨j,hNode,hLive⟩ := (hExact cut hCut z).mp hZ
    exact hTerminal cut hCut j hLive (by simpa only [hNode] using hLevel)
  · intro p hp
    have hIndexed :
        p ∈ IndexedPhysicalCrossing family node live cut := by
      rw [indexed_physical_crossing_eq_full_closure_relation
        family node live ZY cut (hExact cut hCut)]
      exact hp
    obtain ⟨j,hLive,hOldRaw,hUpperRaw⟩ := hIndexed
    exact hCrossing cut hCut j hLive p.1 p.2 hOldRaw hUpperRaw

end Kk
