import Kk.TrackENumericCoherentSourceIndex
import Kk.TrackGOldBoringNoTerminal
import Mathlib.Tactic

/-!
# Track E E64: exact residual live-source obstruction at old-boring cuts

The coherent physical old->new name injection from E62/E63 makes
old-LIVE images automatically covered, with literal same-node full
dependent L+ old/upper raw type records. Consequently the entire
reverse NEW->OLD off-plan no-novelty test can be restricted to
*residual* new-live indices not in that old-LIVE image.

A residual index may still denote an OLD FINAL source node which
only became active earlier in the new run. Never confuse residual
with outside the image of the old FINAL index map.

English-first proof and 20 hostile cases:
  docs/track_e_residual_novelty_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The image of an OLD LIVE physical name under one coherent
old-to-new Fin-index map at the specific literal Kpt source cut. -/
def KptOldLiveImageAt
    {P Q : Nat} (φ : Fin P → Fin Q)
    (oldLive : Nat → Fin P → Bool)
    (cut : Nat) (j : Fin Q) : Prop :=
  ∃ i : Fin P, oldLive cut i = true ∧ φ i = j

/-- A new-live index is residual precisely when it is not the
image of ANY old-live index at the present source cut. This
includes both newly created final Kpt nodes and OLD final
nodes which are newly active in the new pre-cut closure. -/
def KptResidualQuietAtBoringCut
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool)
    (φ : Fin P → Fin Q) (cut : Nat) : Prop :=
  (∀ j : Fin Q, newLive cut j = true →
    ¬ KptOldLiveImageAt φ oldLive cut j →
    LevelTree.lev (newNode j) ≠ cut) ∧
  (∀ j : Fin Q, newLive cut j = true →
    ¬ KptOldLiveImageAt φ oldLive cut j →
    ∀ T : PartialTypeWithE cut db du dd,
    ∀ U : PartialTypeWithE (cut+1) db du dd,
      kptFullOldAtCut (newNode j) cut =
        some (⟨cut,T⟩ : RawPartialTypeNode db du dd) →
      kptFullUpperAtCut (newNode j) cut =
        some (⟨cut+1,U⟩ : RawPartialTypeNode db du dd) →
      (T,U) ∈ IndexedPhysicalCrossing family oldNode oldLive cut)

/-- Any NEW complete physical same-node old/upper L+ crossing pair
which is absent from the OLD indexed crossing relation must
have a RESIDUAL new-live witness, not an old-live name image.
This requires only actual source-node identity under φ. -/
theorem kpt_novel_full_crossing_has_residual_new_witness
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool)
    (φ : Fin P → Fin Q)
    (hNodes : ∀ i : Fin P, newNode (φ i) = oldNode i)
    (cut : Nat)
    (p : PartialTypeWithE cut db du dd ×
      PartialTypeWithE (cut+1) db du dd)
    (hNew : p ∈ IndexedPhysicalCrossing
      family newNode newLive cut)
    (hNotOld : p ∉ IndexedPhysicalCrossing
      family oldNode oldLive cut) :
    ∃ j : Fin Q, newLive cut j = true ∧
      kptFullOldAtCut (newNode j) cut =
        some (⟨cut,p.1⟩ : RawPartialTypeNode db du dd) ∧
      kptFullUpperAtCut (newNode j) cut =
        some (⟨cut+1,p.2⟩ : RawPartialTypeNode db du dd) ∧
      ¬ KptOldLiveImageAt φ oldLive cut j := by
  obtain ⟨j,hLive,hOld,hUpper⟩ := hNew
  refine ⟨j,hLive,hOld,hUpper,?_⟩
  rintro ⟨i,hOldLive,hφ⟩
  apply hNotOld
  refine ⟨i,hOldLive,?_,?_⟩
  · rw [← hNodes i, hφ]
    exact hOld
  · rw [← hNodes i, hφ]
    exact hUpper

/-- If no OLD LIVE Kpt node is a cut-level terminal,
every new cut-level terminal is necessarily residual.
A REAL old-boring AlgorithmRun gives this hypothesis
from its full physical pre-cut closure. -/
theorem kpt_new_terminal_at_old_boring_cut_is_residual
    {db du dd P Q : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (φ : Fin P → Fin Q)
    (hNodes : ∀ i : Fin P, newNode (φ i) = oldNode i)
    (cut : Nat)
    (hNoOldTerminal : ∀ i : Fin P,
      oldLive cut i = true →
      LevelTree.lev (oldNode i) ≠ cut)
    (j : Fin Q)
    (hTerminal : LevelTree.lev (newNode j) = cut) :
    ¬ KptOldLiveImageAt φ oldLive cut j := by
  rintro ⟨i,hOldLive,hφ⟩
  apply hNoOldTerminal i hOldLive
  calc
    LevelTree.lev (oldNode i) =
        LevelTree.lev (newNode (φ i)) :=
      congrArg LevelTree.lev (hNodes i).symm
    _ = LevelTree.lev (newNode j) := by rw [hφ]
    _ = cut := hTerminal

/-- At an OLD terminal-free cut, the full two-index quietness
test is EQUIVALENT to checking only RESIDUAL new-live names.
All old-live image crossings are automatically transferred
by literal identity of actual Kpt nodes, including E and
negative ordinary L; at (I2) no functionality is assumed.

This is a REDUCTION of the missing reverse physical source
geometry, not a proof that the residual tests hold. -/
theorem kpt_indexed_quiet_iff_residual_quiet_at_boring_cut
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool)
    (φ : Fin P → Fin Q)
    (hNodes : ∀ i : Fin P, newNode (φ i) = oldNode i)
    (cut : Nat)
    (hNoOldTerminal : ∀ i : Fin P,
      oldLive cut i = true →
      LevelTree.lev (oldNode i) ≠ cut) :
    KptIndexedQuietAtCut family
      oldNode newNode oldLive newLive cut ↔
    KptResidualQuietAtBoringCut family
      oldNode newNode oldLive newLive φ cut := by
  constructor
  · rintro ⟨hTerminal,hPairs⟩
    constructor
    · intro j hLive _hResidual hLevel
      obtain ⟨i,hOldLive,hOldLevel⟩ :=
        hTerminal j hLive hLevel
      exact hNoOldTerminal i hOldLive hOldLevel
    · intro j hLive _hResidual T U hOld hUpper
      exact hPairs ⟨j,hLive,hOld,hUpper⟩
  · rintro ⟨hResidualTerminal,hResidualPairs⟩
    constructor
    · intro j hLive hLevel
      have hRes : ¬ KptOldLiveImageAt φ oldLive cut j :=
        kpt_new_terminal_at_old_boring_cut_is_residual
          oldNode newNode oldLive φ hNodes cut
          hNoOldTerminal j hLevel
      exact False.elim ((hResidualTerminal j hLive hRes) hLevel)
    · intro p hp
      obtain ⟨j,hLive,hOld,hUpper⟩ := hp
      by_cases hImage : KptOldLiveImageAt φ oldLive cut j
      · obtain ⟨i,hOldLive,hφ⟩ := hImage
        refine ⟨i,hOldLive,?_,?_⟩
        · rw [← hNodes i, hφ]
          exact hOld
        · rw [← hNodes i, hφ]
          exact hUpper
      · exact hResidualPairs j hLive hImage p.1 p.2 hOld hUpper

/-- At a GENUINE old AlgorithmRun's boring cut, exact finite
indexing of the complete physical pre-cut source yields NO
old-live cut-level terminal. It does not follow from selected
graph-age shadows or from an arbitrary old selected-set function. -/
theorem actual_Kpt_boring_run_exact_index_has_no_old_live_terminal
    {db du dd P : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (RunOld : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (oldNode : Fin P → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (hExactOld : ∀ cut : Nat, cut < top →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (RunOld.I (cut+1)) X ↔
        ∃ i : Fin P, oldNode i = z ∧ oldLive cut i = true)
    (cut : Nat) (hCut : cut < top)
    (hBoring : cut ∉ RunOld.I cut) :
    ∀ i : Fin P, oldLive cut i = true →
      LevelTree.lev (oldNode i) ≠ cut := by
  intro i hLive hLevel
  have hNoPhysical :
      ¬ KptI1AtCut family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RunOld.I (cut+1)) X) cut :=
    actual_Kpt_old_boring_cut_no_terminal
      family X top RunOld cut hCut hBoring
  apply hNoPhysical
  exact ⟨oldNode i,
    (hExactOld cut hCut (oldNode i)).mpr ⟨i,rfl,hLive⟩,
    hLevel⟩

/-- The ENTIRE source-exact off-plan finite certificate for one
genuine old Kpt AlgorithmRun reduces to terminal/pair tests
on just the RESIDUAL new-live indices, outside the old-LIVE
image of one coherent old->new node map.

The theorem does NOT show the residual tests are true in the
proposed resolved numerical-H+ diary. The K4 q2 and E cuts
remain compulsory physical application cases. -/
theorem actual_Kpt_twoIndex_offplan_iff_residual_live_quiet
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (RunOld : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (Allowed : Set Nat)
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool)
    (φ : Fin P → Fin Q)
    (hNodes : ∀ i : Fin P, newNode (φ i) = oldNode i)
    (hExactOld : ∀ cut : Nat, cut < top →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (RunOld.I (cut+1)) X ↔
        ∃ i : Fin P, oldNode i = z ∧ oldLive cut i = true) :
    KptTwoIndexOffPlanNoNovelty family RunOld.I
      top Allowed oldNode newNode oldLive newLive ↔
    ∀ cut : Nat, cut < top →
      cut ∉ RunOld.I cut → cut ∉ Allowed →
      KptResidualQuietAtBoringCut family
        oldNode newNode oldLive newLive φ cut := by
  rw [kptTwoIndexOffPlanNoNovelty_iff_quiet
    family RunOld.I top Allowed oldNode newNode oldLive newLive]
  constructor
  · intro hQuiet cut hCut hBoring hOffPlan
    apply (kpt_indexed_quiet_iff_residual_quiet_at_boring_cut
      family oldNode newNode oldLive newLive φ hNodes cut
      (actual_Kpt_boring_run_exact_index_has_no_old_live_terminal
        family X top RunOld oldNode oldLive hExactOld
        cut hCut hBoring)).mp
    exact hQuiet cut hCut hBoring hOffPlan
  · intro hRes cut hCut hBoring hOffPlan
    apply (kpt_indexed_quiet_iff_residual_quiet_at_boring_cut
      family oldNode newNode oldLive newLive φ hNodes cut
      (actual_Kpt_boring_run_exact_index_has_no_old_live_terminal
        family X top RunOld oldNode oldLive hExactOld
        cut hCut hBoring)).mpr
    exact hRes cut hCut hBoring hOffPlan

end Kk
