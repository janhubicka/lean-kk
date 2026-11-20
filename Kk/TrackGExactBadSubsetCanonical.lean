import Kk.TrackGIntrinsicExactFactorBad
import Kk.TrackECanonicalBadCutSupport
import Kk.TrackGBoringOnlyNoNoveltyRunTransfer
import Kk.TrackGFullEventProfileTransport
import Mathlib.Tactic

/-!
# Track G: exact old-factor Bad support is contained in E54's no-novelty Bad support

English proof and 16 adversarial checks committed FIRST:
docs/track_g_exact_bad_subset_canonical_english_audit_20261120.md

For one genuine old RX on X and literal nested true Kpt seeds X ⊆ Y
with independently exhaustive full physical Kpt pre-cut indices,
G406's new EXACT total-factor Bad cuts form a SUBSET of the older
E54 canonical physical no-novelty Bad cuts.

At an old-boring cut, E54 indexed quietness implies equality of
the complete terminal and same-node paired old/upper L+/E crossing
profiles. Hence no new terminal or genuine I2 meet occurs, and the
unique old skip factor (G309) obeys every new crossing (G347).
The actual old-boring cut is off-plan by I_mem_bounds.

Thus ALL existing bounds on E54 physical Bad support also bound
the sharper genuine factor-obstruction support by cardinal
monotonicity. No diary-uniform such bound, new-only source matching,
cut reindexing or global Kk-free big Ramsey degree is proved here.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

/-- A genuine old-total-factor incompatible Kpt cut is necessarily
an E54 physical no-novelty Bad cut, for TWO independently exact
complete physical Kpt pre-cut source indices and literal X⊆Y.

The converse need not hold: an extra new physical crossing pair
can be compatible with the unique old skip map even if not present
in the old paired crossing profile. No strict containment example
for a genuine numerical H+ stage is claimed. -/
theorem kpt_exact_factor_BadCuts_subset_canonical_noNovelty
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool)
    (hExactOld : ∀ cut : Nat, cut < top →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (RX.I (cut+1)) X ↔
        ∃ i : Fin P, oldNode i = z ∧ oldLive cut i = true)
    (hExactNew : ∀ cut : Nat, cut < top →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (RX.I (cut+1)) Y ↔
        ∃ j : Fin Q, newNode j = z ∧ newLive cut j = true) :
    kptExactOldFactorBadCuts family X top RX
      newNode newLive ⊆
    kptCanonicalOffPlanBadCuts family RX.I top
      oldNode newNode oldLive newLive := by
  intro cut hBad
  obtain ⟨hCut,hOldBoring,hNotCompatible⟩ :=
    (mem_kptExactOldFactorBadCuts
      family X top RX newNode newLive cut).mp hBad
  have hOldUnselected : cut ∉ RX.I cut := by
    intro hSelected
    obtain ⟨_E,_hSkip,_hOldCross,hOldI,_hOldF⟩ :=
      RX.noninteresting_step cut hCut hOldBoring
    have hMemNext : cut ∈ RX.I (cut+1) := by
      rw [hOldI] at hSelected
      exact hSelected
    have hTooHigh : cut+1 ≤ cut :=
      (RX.I_mem_bounds (cut+1) (by omega) cut hMemNext).1
    omega
  apply (mem_kptCanonicalOffPlanBadCuts
    family RX.I top oldNode newNode oldLive newLive cut).mpr
  refine ⟨hCut,hOldUnselected,?_⟩
  intro hQuiet
  let CX : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (RX.I (cut+1)) X
  let CY : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (RX.I (cut+1)) Y
  have hPhysical : NewRootNoNoveltyAtCut family CX CY cut :=
    (kptIndexedQuietAtCut_iff_physical
      family CX CY oldNode newNode oldLive newLive cut
      (hExactOld cut hCut) (hExactNew cut hCut)).mp hQuiet
  have hIncl : CX ⊆ CY :=
    envelope_closure_mono_seeds_and_levels
      (admissibleKptSTree family)
      (RX.I (cut+1)) (RX.I (cut+1)) X Y
      (by intro i hi; exact hi) hXY
  have hProfiles :=
    (kpt_noNovelty_iff_full_profile_eq_of_source_subset
      family CX CY cut hIncl).mp hPhysical
  have hDecision :=
    kpt_IsInterestingAt_iff_of_terminal_and_full_crossing_eq
      family CX CY cut hProfiles.1 hProfiles.2
  have hBoringNew :
      ¬ SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family) CY cut := by
    intro hNewInteresting
    exact hOldBoring (hDecision.mpr hNewInteresting)
  apply hNotCompatible
  refine ⟨?_,?_,?_⟩
  · intro j hLive hLevel
    have hj : newNode j ∈ CY :=
      (hExactNew cut hCut (newNode j)).mpr
        ⟨j,rfl,hLive⟩
    exact hBoringNew (Or.inl ⟨newNode j,hj,hLevel⟩)
  · intro j k hjLive hkLive hMeetData
    have hj : newNode j ∈ CY :=
      (hExactNew cut hCut (newNode j)).mpr
        ⟨j,rfl,hjLive⟩
    have hk : newNode k ∈ CY :=
      (hExactNew cut hCut (newNode k)).mpr
        ⟨k,rfl,hkLive⟩
    exact hBoringNew (Or.inr (Or.inl
      ⟨newNode j,hj,newNode k,hk,hMeetData.1,hMeetData.2⟩))
  · intro D hFactorD j hLive hCrossJ
    obtain ⟨E,hSkipE,hOldCrossE,_hOldI,hFactorE⟩ :=
      RX.noninteresting_step cut hCut hOldBoring
    have hDE : D = E :=
      kpt_MMap_comp_left_cancel
        (normalizedKptSMTree family)
        (RX.F (cut+1)) D E
        (hFactorD.symm.trans hFactorE)
    have hNewCrossE :=
      (kpt_actual_skipLaw_iff_of_full_crossing_eq
        family CX CY cut hProfiles.2 E).mp hOldCrossE
    have hj : newNode j ∈ CY :=
      (hExactNew cut hCut (newNode j)).mpr
        ⟨j,rfl,hLive⟩
    have hAt := hNewCrossE hj hCrossJ
    simpa only [hDE] using hAt

/-- Every physical cardinal upper bound established for E54's
canonical no-novelty Bad support also bounds the sharper
EXACT total-factor Bad support, with no further counting.

This is not a new diary-uniform bound: it is a finite
comparison under exact physical Kpt source indexing. -/
theorem kpt_exact_factor_BadCuts_card_le_canonical_noNovelty
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool)
    (hExactOld : ∀ cut : Nat, cut < top →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (RX.I (cut+1)) X ↔
        ∃ i : Fin P, oldNode i = z ∧ oldLive cut i = true)
    (hExactNew : ∀ cut : Nat, cut < top →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (RX.I (cut+1)) Y ↔
        ∃ j : Fin Q, newNode j = z ∧ newLive cut j = true) :
    (kptExactOldFactorBadCuts family X top RX
      newNode newLive).card ≤
    (kptCanonicalOffPlanBadCuts family RX.I top
      oldNode newNode oldLive newLive).card := by
  exact Finset.card_le_card
    (kpt_exact_factor_BadCuts_subset_canonical_noNovelty
      family X Y hXY top RX oldNode newNode oldLive newLive
      hExactOld hExactNew)

end Kk
