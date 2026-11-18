import Kk.TrackGBoringOnlyNoNoveltyRunTransfer
import Kk.TrackECanonicalBadCutSupport
import Mathlib.Tactic

/-!
# Track G: original E53 finite quietness and empty E54 canonical Bad support

English proof and 16 hostile checks committed FIRST:
docs/track_g_empty_canonical_badcuts_run_transfer_english_audit_20261118.md

Exact complete Kpt indices on the original AlgorithmRun's I tails,
E53 no-offplan with Allowed empty, and the genuine old-boring
criterion suffice for constructing a new Y-run with the original
I and TOTAL monoid-valued F. No target run or source bijection.
A second theorem states the equivalent sufficient test as
emptiness of E54's canonical finite bad-cut set. Neither theorem
proves a uniform event budget or common labelled source orbit.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

/-- An E53 no-offplan certificate (Allowed empty) on independent
EXACT full Kpt source indices yields one actual Y-run with I/F
identical to the given X-run. Physical quietness need only
be checked at genuinely old-boring cuts. -/
theorem kpt_wholeRun_transport_of_twoIndex_noOffPlan
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family)) (hXY : X ⊆ Y)
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
        ∃ j : Fin Q, newNode j = z ∧ newLive cut j = true)
    (hFinite : KptTwoIndexOffPlanNoNovelty family RX.I top
        (∅ : Set Nat) oldNode newNode oldLive newLive) :
    ∃ RY : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family) Y top,
      RY.I = RX.I ∧ RY.F = RX.F := by
  have hQuiet :
      ∀ cut : Nat, cut < top →
        cut ∉ RX.I cut → cut ∉ (∅ : Set Nat) →
        KptIndexedQuietAtCut family
          oldNode newNode oldLive newLive cut :=
    (kptTwoIndexOffPlanNoNovelty_iff_quiet
      family RX.I top (∅ : Set Nat)
      oldNode newNode oldLive newLive).mp hFinite
  apply kpt_transport_actualRun_of_boring_only_indexed_quiet
    family X Y hXY top RX
    oldNode newNode oldLive newLive hExactOld hExactNew
  intro cut hCut hBoring
  have hNotSelected : cut ∉ RX.I cut := by
    intro hMem
    obtain ⟨_D,_hSkip,_hCross,hI,_hF⟩ :=
      RX.noninteresting_step cut hCut hBoring
    have hMemNext : cut ∈ RX.I (cut+1) := by
      rw [hI] at hMem
      exact hMem
    have hImpossible : cut+1 ≤ cut :=
      (RX.I_mem_bounds (cut+1) (by omega) cut hMemNext).1
    omega
  exact hQuiet cut hCut hNotSelected (by simp)

/-- The EMPTY minimal old-boring physical Bad Finset of E54 is
an exact finite certificate for E53 with Allowed empty, hence
suffices to transport one genuine run's I and total F.

This is a SUFFICIENT criterion, not a necessary one: extra
new-source crossings might still happen to respect the old
skipping monoid map. No uniform Bad bound is asserted. -/
theorem kpt_wholeRun_transport_of_empty_canonical_BadCuts
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family)) (hXY : X ⊆ Y)
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
        ∃ j : Fin Q, newNode j = z ∧ newLive cut j = true)
    (hBadEmpty :
      kptCanonicalOffPlanBadCuts family RX.I top
        oldNode newNode oldLive newLive = ∅) :
    ∃ RY : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family) Y top,
      RY.I = RX.I ∧ RY.F = RX.F := by
  have hFinite : KptTwoIndexOffPlanNoNovelty family RX.I top
      (∅ : Set Nat) oldNode newNode oldLive newLive := by
    apply (kptTwoIndexOffPlanNoNovelty_iff_badCuts_subset
      family RX.I top (∅ : Set Nat)
      oldNode newNode oldLive newLive).mpr
    intro cut hBad
    rw [hBadEmpty] at hBad
    simp at hBad
  exact kpt_wholeRun_transport_of_twoIndex_noOffPlan
    family X Y hXY top RX oldNode newNode oldLive newLive
    hExactOld hExactNew hFinite

end Kk
