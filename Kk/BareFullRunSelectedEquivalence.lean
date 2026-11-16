import Kk.CutVisibleClosureAbsorption
import Mathlib.Tactic

/-!
# Track C: bare and inherited-full true Kpt AlgorithmRuns choose SAME levels

English-first proof and hostile cases:
  docs/track_c_bare_full_run_selections_english_audit.md

The older full-closure absorption needed all old selected levels above
each cut, which can be vacuous. The graded cut-visible theorem proves
a new result: preinserting inherited old parameter closure cannot
change ANY selected level of the new true AlgorithmRun, provided
both new runs use the SAME scan top and the old run has a REAL top seed.

This does NOT identify the two choices of MMap F_i, two different
base source models, any common labelled inverse orbit, or BRDs.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

universe u v

private theorem bareFull_induction_down
    {top : Nat} {P : Nat → Prop}
    (htop : P top)
    (hstep : ∀ i, i < top → P (i + 1) → P i) :
    ∀ i, i ≤ top → P i := by
  have main : ∀ d : Nat, ∀ i, top - i = d → i ≤ top → P i := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro i hdi hit
        by_cases heq : i = top
        · simpa [heq] using htop
        · have hlt : i < top := lt_of_le_of_ne hit heq
          apply hstep i hlt
          apply ih (top - (i + 1)) (by omega)
            (i + 1) rfl (by omega)
  intro i hi
  exact main (top - i) i rfl hi

/-- The true new-run selected interesting levels are IDENTICAL
whether its initial seeds are the genuinely BARE old X∪O or the
preinserted inherited-FULL old closure_(Rold.I0)(X)∪O.

The two NEW runs have the SAME top newTop; oldTop≤newTop and
one REAL old seed has level oldTop. This uses neither E1 nor
equality of chosen shape maps F_i: the genuine IsInterestingAt
predicate depends only on cut-visible closure sources.

The theorem is general for any STree/SMTree satisfying the
strict parameter-level axiom; no Kk diary is a hypothesis. -/
theorem envelope_bare_full_new_runs_same_selected_levels
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    {S : STree T Label}
    (H : SMTree S)
    (X O : Set T)
    (oldTop newTop : Nat)
    (hTopLe : oldTop ≤ newTop)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = oldTop)
    (Rold : SMTree.Envelope.AlgorithmRun H X oldTop)
    (Rbare : SMTree.Envelope.AlgorithmRun H (X ∪ O) newTop)
    (Rfull : SMTree.Envelope.AlgorithmRun H
      (SMTree.Envelope.closure S (Rold.I 0) X ∪ O) newTop) :
    ∀ i : Nat, i ≤ newTop → Rbare.I i = Rfull.I i := by
  have hBareSeeds : X ⊆ X ∪ O := by
    intro x hx
    exact Or.inl hx
  have hTail :
      ∀ cut : Nat, cut < newTop →
        ∀ q : Nat, q ∈ Rold.I 0 → cut < q →
          q ∈ Rbare.I (cut+1) := by
    intro cut hCut q hOld hAbove
    by_cases hBefore : cut < oldTop
    · exact envelope_algorithmRun_retains_old_selected_tail
        H X (X ∪ O) hBareSeeds oldTop newTop hTopLe
        hTopSeed Rold Rbare cut hBefore q hOld hAbove
    · have hBound := Rold.I_mem_bounds 0 (Nat.zero_le oldTop) q hOld
      omega
  apply bareFull_induction_down
  · rw [Rbare.topI, Rfull.topI]
  · intro cut hCut hNext
    have hTailCut :
        ∀ q : Nat, q ∈ Rold.I 0 → cut < q →
          q ∈ Rbare.I (cut+1) :=
      hTail cut hCut
    have hVisible :
        ∀ z : T, cut ≤ LevelTree.lev z →
          (z ∈ SMTree.Envelope.closure S
            (Rbare.I (cut+1)) (X ∪ O) ↔
           z ∈ SMTree.Envelope.closure S
            (Rfull.I (cut+1))
              (SMTree.Envelope.closure S (Rold.I 0) X ∪ O)) := by
      intro z hz
      have hSource :=
        envelope_closure_high_absorbs_old_closure
          S (Rold.I 0) (Rbare.I (cut+1)) X O cut
          hTailCut z hz
      rw [← hNext]
      exact hSource.symm
    have hInteresting :
        SMTree.Envelope.IsInterestingAt H
            (SMTree.Envelope.closure S
              (Rbare.I (cut+1)) (X ∪ O)) cut ↔
        SMTree.Envelope.IsInterestingAt H
            (SMTree.Envelope.closure S
              (Rfull.I (cut+1))
                (SMTree.Envelope.closure S (Rold.I 0) X ∪ O)) cut :=
      envelope_IsInterestingAt_iff_of_cut_visible H
        (SMTree.Envelope.closure S (Rbare.I (cut+1)) (X ∪ O))
        (SMTree.Envelope.closure S (Rfull.I (cut+1))
          (SMTree.Envelope.closure S (Rold.I 0) X ∪ O))
        cut hVisible
    by_cases hBare :
        SMTree.Envelope.IsInterestingAt H
          (SMTree.Envelope.closure S
            (Rbare.I (cut+1)) (X ∪ O)) cut
    · have hFull := hInteresting.mp hBare
      have hBI := (Rbare.interesting_step cut hCut hBare).1
      have hFI := (Rfull.interesting_step cut hCut hFull).1
      rw [hBI, hFI, hNext]
    · have hFull :
          ¬ SMTree.Envelope.IsInterestingAt H
            (SMTree.Envelope.closure S
              (Rfull.I (cut+1))
                (SMTree.Envelope.closure S (Rold.I 0) X ∪ O)) cut := by
        intro h
        exact hBare (hInteresting.mpr h)
      obtain ⟨_,_,_,hBI,_⟩ :=
        Rbare.noninteresting_step cut hCut hBare
      obtain ⟨_,_,_,hFI,_⟩ :=
        Rfull.noninteresting_step cut hCut hFull
      rw [hBI, hFI, hNext]

/-- Exact numerical H+ specialization with genuine NEW admissible Kpt
originals, including the auxiliary E/free-cut data. The new initial
seed O is the image of original nodes at actual finite coordinates W,
NEVER their entire ancestor-prefix pool.

Both runs are true Kpt AlgorithmRuns on the SAME finite physical
normalized successor tree at the same new top. The old top seed and
newTop≥oldTop are substantive physical hypotheses.

The result compares the I-sets, NOT F_i maps or labelled orbit. -/
theorem finiteNumericH_bare_and_full_new_runs_same_selected_levels
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd)
    (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (X : Set (AdmissibleKptNode family))
    (W : Set (Fin M))
    (oldTop newTop : Nat)
    (hTopLe : oldTop ≤ newTop)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = oldTop)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (Rbare : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
      (X ∪ ((fun w : Fin M =>
        (finiteNumericH L k M).kptOriginal family hAvoid w) '' W))
      newTop)
    (Rfull : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (Rold.I 0) X ∪
        ((fun w : Fin M =>
          (finiteNumericH L k M).kptOriginal family hAvoid w) '' W))
      newTop) :
    ∀ i : Nat, i ≤ newTop → Rbare.I i = Rfull.I i := by
  exact envelope_bare_full_new_runs_same_selected_levels
    (normalizedKptSMTree family)
    X ((fun w : Fin M =>
      (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)
    oldTop newTop hTopLe hTopSeed Rold Rbare Rfull

end Kk
