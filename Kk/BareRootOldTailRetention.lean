import Kk.AlgorithmRunCrossHeightMonotonicity
import Kk.PhysicalBareNewRootRun
import Mathlib.Tactic

/-!
# Track C: retain only the old selected TAIL under a true bare-root insertion

English-first adversarial proof:
  docs/track_c_bare_old_tail_english_audit.md

The former all-old-levels-above-cut closure-absorption interface can be
vacuous when 0 belongs to the old selected set. The result here is
nonvacuous: it preserves precisely old selected levels strictly above
the tested cut even if lower levels, including 0, were selected.

Crucial limitation: no equality of old/full Kpt closure, full L+/E
crossing, corrected B3, common diary orbit or BRD theorem follows.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

universe u v

/-- For two TRUE AlgorithmRuns on X⊆Y at possibly different scan tops,
with a real old top seed, every old selected level STRICTLY above a
tested old cut remains selected at the NEW pre-cut stage.

Unlike the previously used all-above-cut hypothesis, this is useful
even when old I0 contains 0 or other selected levels below the cut.

This only compares the selected-level tails; it does NOT absorb
dependent parameters generated at old levels ≤ cut. -/
theorem envelope_algorithmRun_retains_old_selected_tail
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    {S : STree T Label}
    (H : SMTree S)
    (X Y : Set T)
    (hXY : X ⊆ Y)
    (oldTop newTop : Nat)
    (hTopLe : oldTop ≤ newTop)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = oldTop)
    (R : SMTree.Envelope.AlgorithmRun H X oldTop)
    (Q : SMTree.Envelope.AlgorithmRun H Y newTop)
    (cut : Nat) (hCut : cut < oldTop) :
    ∀ q : Nat, q ∈ R.I 0 → cut < q → q ∈ Q.I (cut+1) := by
  have hStage : R.I (cut+1) ⊆ Q.I (cut+1) :=
    envelope_algorithmRun_selected_levels_mono_seed_height
      H X Y hXY oldTop newTop hTopLe hTopSeed R Q
      (cut+1) (by omega)
  intro q hOld hAbove
  apply hStage
  rw [R.I_eq_final_tail_of_run (cut+1) (by omega)]
  exact ⟨hOld, Nat.succ_le_iff.mpr hAbove⟩

/-- Track C physical specialization to the genuinely BARE new-root seed
family X ∪ {one actual numerical-H admissible Kpt ORIGINAL}.
It never preinserts the new original's ancestors or the inherited
parameter closure as initial seeds. Both runs operate in the SAME
normalized admissible Kpt successor tree; they may have different tops.

The actual new H+ base's forbidden-family avoidance is an explicit
hypothesis needed to define the genuine physical Kpt original.

Old selected levels q>cut survive in the new pre-cut tail, but
q≤cut is NOT claimed and no full closure equality is asserted. -/
theorem finiteNumericH_bareTopRoot_retains_old_selected_tail
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M j : Nat)
    (hAvoidL : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (hTarget : hPosition k j k < M)
    (X : Set (AdmissibleKptNode family))
    (oldTop newTop : Nat)
    (hTopLe : oldTop ≤ newTop)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = oldTop)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (Rnew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
        (finiteNumericH_bareTopRootSeeds
          family L k M j hAvoidL hTarget X) newTop)
    (cut : Nat) (hCut : cut < oldTop) :
    ∀ q : Nat, q ∈ Rold.I 0 → cut < q →
      q ∈ Rnew.I (cut+1) := by
  have hSeeds :
      X ⊆ finiteNumericH_bareTopRootSeeds
        family L k M j hAvoidL hTarget X := by
    intro z hz
    exact Or.inl hz
  exact envelope_algorithmRun_retains_old_selected_tail
    (normalizedKptSMTree family)
    X (finiteNumericH_bareTopRootSeeds
      family L k M j hAvoidL hTarget X)
    hSeeds oldTop newTop hTopLe hTopSeed
    Rold Rnew cut hCut

end Kk
