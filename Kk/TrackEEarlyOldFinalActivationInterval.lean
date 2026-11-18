import Kk.TrackENumericResidualTwoClass
import Kk.TrackGCrossingFrontier
import Mathlib.Tactic

/-!
# Track E E66: early activation of old-final physical Kpt names is an interval

E65's OLD-FINAL-but-OLD-INACTIVE class does NOT require the name to
be currently new-live. Adding the true new-live condition gives the
actual residual activation window. For two downward-monotone live
masks, a fixed name's early-activation cuts form an order-convex set.

Actual Kpt AlgorithmRuns have this monotonicity via their complete
physical pre-cut closures (G294), provided per-index membership is
EXACT. One such window may nevertheless contain arbitrarily many
cuts in the bare Boolean abstraction: this is not a diary budget.

English-first proof and 18 hostile tests:
docs/track_e_early_activation_window_english_audit_20261118.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The correct early OLD-FINAL residual activity condition:
new LIVE at cut while some old FINAL index naming this same new
index is OLD INACTIVE at that cut. The physical node identity
of the map phi is an additional application requirement. -/
def KptEarlyOldFinalLiveAt
    {P Q : Nat} (φ : Fin P → Fin Q)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool)
    (cut : Nat) (j : Fin Q) : Prop :=
  newLive cut j = true ∧
    KptEarlyOldFinalName φ oldLive cut j

/-- Order-convexity requires even LESS than two early-live endpoints:
early at LOW and new-live at HIGH force early at every intermediate
source cut, if both masks are genuinely downward-monotone.
No injectivity of phi or old->new liveness is needed for this
Boolean interval lemma. -/
theorem kpt_earlyOldFinalLive_mid_of_low_early_high_new
    {P Q : Nat}
    (φ : Fin P → Fin Q)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool)
    (top : Nat)
    (hOldDown : ∀ (low high : Nat) (i : Fin P),
      low ≤ high → high < top →
      oldLive high i = true → oldLive low i = true)
    (hNewDown : ∀ (low high : Nat) (j : Fin Q),
      low ≤ high → high < top →
      newLive high j = true → newLive low j = true)
    (low mid high : Nat)
    (hLowMid : low ≤ mid)
    (hMidHigh : mid ≤ high)
    (hHighTop : high < top)
    (j : Fin Q)
    (hLowEarly : KptEarlyOldFinalLiveAt φ oldLive newLive low j)
    (hHighNew : newLive high j = true) :
    KptEarlyOldFinalLiveAt φ oldLive newLive mid j := by
  change newLive low j = true ∧
    KptEarlyOldFinalName φ oldLive low j at hLowEarly
  obtain ⟨_hNewLow, ⟨i,hφ,hOldLowFalse⟩⟩ := hLowEarly
  have hNewMid : newLive mid j = true :=
    hNewDown mid high j hMidHigh hHighTop hHighNew
  have hOldMidFalse : oldLive mid i = false := by
    cases hOldMid : oldLive mid i with
    | false => rfl
    | true =>
      have hOldLowTrue : oldLive low i = true :=
        hOldDown low mid i hLowMid
          (lt_of_le_of_lt hMidHigh hHighTop) hOldMid
      rw [hOldLowFalse] at hOldLowTrue
      cases hOldLowTrue
  exact ⟨hNewMid, ⟨i,hφ,hOldMidFalse⟩⟩

/-- Consequently each fixed name's early old-final NEW-LIVE window
is an interval in literal source cut coordinates. Empty and
arbitrarily long windows are NOT ruled out. -/
theorem kpt_earlyOldFinalLive_orderConvex_of_monotone_masks
    {P Q : Nat}
    (φ : Fin P → Fin Q)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool)
    (top : Nat)
    (hOldDown : ∀ (low high : Nat) (i : Fin P),
      low ≤ high → high < top →
      oldLive high i = true → oldLive low i = true)
    (hNewDown : ∀ (low high : Nat) (j : Fin Q),
      low ≤ high → high < top →
      newLive high j = true → newLive low j = true)
    (low mid high : Nat)
    (hLowMid : low ≤ mid)
    (hMidHigh : mid ≤ high)
    (hHighTop : high < top)
    (j : Fin Q)
    (hLow : KptEarlyOldFinalLiveAt φ oldLive newLive low j)
    (hHigh : KptEarlyOldFinalLiveAt φ oldLive newLive high j) :
    KptEarlyOldFinalLiveAt φ oldLive newLive mid j := by
  exact kpt_earlyOldFinalLive_mid_of_low_early_high_new
    φ oldLive newLive top hOldDown hNewDown
    low mid high hLowMid hMidHigh hHighTop
    j hLow hHigh.1

/-- PHYSICAL version. Exact per-index masks of TWO genuine
AlgorithmRuns in the SAME normalized Kpt tree grow monotonically
as their source cut decreases. Hence old-final newly active names,
when interpreted through a fixed physical map phi, have
order-convex early-live windows.

Literal nested seeds and a real old-top seed are NOT logically
needed here; they are needed in E62/E63 to CONSTRUCT phi as
a true node-preserving coherent physical source map. -/
theorem kpt_actual_runs_earlyOldFinalLive_orderConvex
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (oldTop newTop : Nat) (hTopLe : oldTop ≤ newTop)
    (RunOld : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (RunNew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y newTop)
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool)
    (hOldExact : ∀ cut : Nat, cut < oldTop →
      ∀ i : Fin P, oldLive cut i = true ↔
        oldNode i ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (RunOld.I (cut+1)) X)
    (hNewExact : ∀ cut : Nat, cut < oldTop →
      ∀ j : Fin Q, newLive cut j = true ↔
        newNode j ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (RunNew.I (cut+1)) Y)
    (φ : Fin P → Fin Q)
    (low mid high : Nat)
    (hLowMid : low ≤ mid)
    (hMidHigh : mid ≤ high)
    (hHigh : high < oldTop)
    (j : Fin Q)
    (hLowEarly : KptEarlyOldFinalLiveAt φ oldLive newLive low j)
    (hHighEarly : KptEarlyOldFinalLiveAt φ oldLive newLive high j) :
    KptEarlyOldFinalLiveAt φ oldLive newLive mid j := by
  have hOldDown : ∀ (a b : Nat) (i : Fin P),
      a ≤ b → b < oldTop →
      oldLive b i = true → oldLive a i = true := by
    intro a b i hab hb hLive
    apply (hOldExact a (lt_of_le_of_lt hab hb) i).2
    apply (kpt_actual_run_preCut_source_mono_down
      family X oldTop a b RunOld hab hb)
    exact (hOldExact b hb i).1 hLive
  have hNewDown : ∀ (a b : Nat) (j : Fin Q),
      a ≤ b → b < oldTop →
      newLive b j = true → newLive a j = true := by
    intro a b j hab hb hLive
    apply (hNewExact a (lt_of_le_of_lt hab hb) j).2
    apply (kpt_actual_run_preCut_source_mono_down
      family Y newTop a b RunNew hab
      (lt_of_lt_of_le hb hTopLe))
    exact (hNewExact b hb j).1 hLive
  exact kpt_earlyOldFinalLive_orderConvex_of_monotone_masks
    φ oldLive newLive oldTop hOldDown hNewDown
    low mid high hLowMid hMidHigh hHigh j
    hLowEarly hHighEarly

/-- ABSTRACT negative regression, not a realized Kpt diary:
a SINGLE old-final name can be old-inactive but new-live on
ARBITRARILY MANY source cuts while both masks are downward
monotone. Thus order-convexity does not bound its length. -/
theorem kpt_abstract_earlyOldFinalLive_arbitrarily_long
    (n : Nat) :
    ∃ oldLive newLive : Nat → Fin 1 → Bool,
      (∀ cut : Nat, cut < n →
        KptEarlyOldFinalLiveAt
          (fun i : Fin 1 => i) oldLive newLive cut (0 : Fin 1)) ∧
      (∀ (low high : Nat) (i : Fin 1),
        low ≤ high → oldLive high i = true → oldLive low i = true) ∧
      (∀ (low high : Nat) (j : Fin 1),
        low ≤ high → newLive high j = true → newLive low j = true) := by
  refine ⟨(fun _ _ => false), (fun _ _ => true), ?_, ?_, ?_⟩
  · intro cut _hCut
    exact ⟨rfl, ⟨0,rfl,rfl⟩⟩
  · intro low high i _hLe hLive
    cases hLive
  · intro low high j _hLe _hLive
    rfl

end Kk
