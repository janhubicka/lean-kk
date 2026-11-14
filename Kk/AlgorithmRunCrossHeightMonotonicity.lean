import Kk.AlgorithmRunSeedMonotonicity
import Mathlib.Tactic

/-!
# Track C: true AlgorithmRun selected-level retention across INCREASING heights

English-first proof and twenty hostile checks:
  docs/track_c_crossheight_run_retention_english_audit.md

The previous Track C theorem compared two true AlgorithmRuns at the SAME
scan top. Resolved constructions genuinely add newer, higher original
Kpt free cuts, so the scan top changes.

For an old true run on X at top=t and a new true run on Y⊇X
at top=T≥t, a REAL old seed x∈X of level t forces I1 when the
new run scans t. Thus the old top t remains selected in the new
run, and the verified seed/selected-level closure monotonicity plus
the exact I1/I2/I3 interestingness monotonicity descends to every
earlier level. We derive I_old⊆I_new even when t<T.

The top-seed condition is NECESSARY: a formal AlgorithmRun can be
started at a top with no seed at that level, and the new run might
then skip that old artificial top.

For the corrected physical original-ONLY new-root seed family, this
discharges the retained-old-level hypothesis of the prior exact
full Kpt pre-cut closure absorption theorem, at tested cuts below
the old selected levels.

No common source orbit, all-cut minimal diary or unconditional BRD.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

universe u v

/-- Descending natural-number induction, explicitly reproduced because
the upstream successor-tree induction helper is private. -/
private theorem crossheight_induction_down
    {ell : Nat} {P : Nat → Prop}
    (htop : P ell)
    (hstep : ∀ i, i < ell → P (i + 1) → P i) :
    ∀ i, i ≤ ell → P i := by
  have main : ∀ d : Nat, ∀ i, ell - i = d → i ≤ ell → P i := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro i hdi hiell
        by_cases hieq : i = ell
        · simpa [hieq] using htop
        · have hilt : i < ell := lt_of_le_of_ne hiell hieq
          apply hstep i hilt
          apply ih (ell - (i + 1)) (by omega) (i + 1) rfl (by omega)
  intro i hiell
  exact main (ell - i) i rfl hiell

/-- TWO genuine successor-tree AlgorithmRuns with different scan
tops and X⊆Y have MONOTONE selected level sets through the entire
old scan, provided the SMALL run has a GENUINE seed at its top.

The new run's level t is forced interesting by this old top node,
and the rest follows by downward induction on true I1/I2/I3
interestingness and genuine meet/parameter closure.

This comparison permits arbitrarily many ADDITIONAL selected levels
in the larger new-root run. -/
theorem envelope_algorithmRun_selected_levels_mono_seed_height
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
    (Q : SMTree.Envelope.AlgorithmRun H Y newTop) :
    ∀ i : Nat, i ≤ oldTop → R.I i ⊆ Q.I i := by
  have hBase : R.I oldTop ⊆ Q.I oldTop := by
    rw [R.topI]
    intro q hq
    have hqEq : q = oldTop := by
      simpa only [Set.mem_singleton_iff] using hq
    subst q
    by_cases hEq : oldTop = newTop
    · subst newTop
      rw [Q.topI]
      simp
    · have hLt : oldTop < newTop := by omega
      obtain ⟨x,hx,hLev⟩ := hTopSeed
      have hSeed :
          x ∈ SMTree.Envelope.closure S (Q.I (oldTop+1)) Y :=
        (SMTree.Envelope.subset_closure
          S (Q.I (oldTop+1)) Y) (hXY hx)
      have hInteresting :
          SMTree.Envelope.IsInterestingAt H
            (SMTree.Envelope.closure S
              (Q.I (oldTop+1)) Y) oldTop :=
        Or.inl ⟨x,hSeed,hLev⟩
      have hStep := (Q.interesting_step oldTop hLt hInteresting).1
      rw [hStep]
      simp
  apply crossheight_induction_down
  · exact hBase
  · intro i hi hNext
    have hClosure :
        SMTree.Envelope.closure S (R.I (i+1)) X ⊆
          SMTree.Envelope.closure S (Q.I (i+1)) Y :=
      envelope_closure_mono_seeds_and_levels
        S (R.I (i+1)) (Q.I (i+1)) X Y hNext hXY
    by_cases hInteresting :
        SMTree.Envelope.IsInterestingAt H
          (SMTree.Envelope.closure S (R.I (i+1)) X) i
    · have hInterestingQ :
          SMTree.Envelope.IsInterestingAt H
            (SMTree.Envelope.closure S (Q.I (i+1)) Y) i :=
        envelope_IsInterestingAt_mono_nodes H
          (SMTree.Envelope.closure S (R.I (i+1)) X)
          (SMTree.Envelope.closure S (Q.I (i+1)) Y)
          hClosure i hInteresting
      have hRI := (R.interesting_step i hi hInteresting).1
      have hQI := (Q.interesting_step i (by omega) hInterestingQ).1
      rw [hRI, hQI]
      intro z hz
      rcases Set.mem_insert_iff.mp hz with hEq | hOld
      · exact Set.mem_insert_iff.mpr (Or.inl hEq)
      · exact Set.mem_insert_iff.mpr (Or.inr (hNext hOld))
    · obtain ⟨_,_,_,hRI,_⟩ :=
        R.noninteresting_step i hi hInteresting
      have hQNext : Q.I (i+1) ⊆ Q.I i := by
        rcases Q.level_step i (by omega) with hQI | hQI
        · rw [hQI]
        · rw [hQI]
          intro z hz
          exact Set.mem_insert_iff.mpr (Or.inr hz)
      rw [hRI]
      exact hNext.trans hQNext

/-- Adding corrected genuine new Kpt ORIGINAL seeds at a strictly
larger scan height CANNOT DELETE any selected old level, provided
the actual old stage has a genuine top-level seed.

No assumed retention of I_old is left in the conclusion. The two
runs have different seed sets and possibly different top heights,
but operate in the SAME complete admissible Kpt successor tree. -/
theorem finiteNumericH_newRoot_run_retains_old_levels_larger_top
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (X : Set (AdmissibleKptNode family))
    (W : Set (Fin M))
    (oldTop newTop : Nat)
    (hTopLe : oldTop ≤ newTop)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = oldTop)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (Rnew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
        (finiteNumericH_physicalExtendedSeeds
          family L k M hAvoid (Rold.I 0) X W) newTop) :
    Rold.I 0 ⊆ Rnew.I 0 := by
  have hSeeds :
      X ⊆ finiteNumericH_physicalExtendedSeeds
        family L k M hAvoid (Rold.I 0) X W := by
    intro z hz
    exact Or.inl
      ((SMTree.Envelope.subset_closure
        (admissibleKptSTree family) (Rold.I 0) X) hz)
  exact envelope_algorithmRun_selected_levels_mono_seed_height
    (normalizedKptSMTree family)
    X (finiteNumericH_physicalExtendedSeeds
      family L k M hAvoid (Rold.I 0) X W)
    hSeeds oldTop newTop hTopLe hTopSeed
    Rold Rnew 0 (Nat.zero_le oldTop)

/-- At an actual NEW root's higher-top AlgorithmRun pre-cut STRICTLY
below every selected old level, the entire inherited old closure
is ABSORBED: the complete pre-cut Kpt meet/parameter node set is
identical to that generated from bare old X and NEW original Kpt
nodes alone.

Here OLD selected-level retention is a theorem from increasing-top
seed monotonicity, NOT an assumed diary hypothesis. Therefore all
actual I1/I2 and full physical old/upper L+ crossing records agree
at such a cut. No claim of all-cut or different-occurrence orbit. -/
theorem finiteNumericH_newRoot_preCut_absorbs_old_run_larger_top
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (X : Set (AdmissibleKptNode family))
    (W : Set (Fin M))
    (oldTop newTop : Nat)
    (hTopLe : oldTop ≤ newTop)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = oldTop)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (Rnew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
        (finiteNumericH_physicalExtendedSeeds
          family L k M hAvoid (Rold.I 0) X W) newTop)
    (cut : Nat) (hCut : cut < newTop)
    (hAbove : ∀ q : Nat, q ∈ Rold.I 0 → cut < q) :
    let O : Set (AdmissibleKptNode family) :=
      ((fun w : Fin M =>
        (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)
    SMTree.Envelope.closure (admissibleKptSTree family)
      (Rnew.I (cut+1))
      (finiteNumericH_physicalExtendedSeeds family L k M
        hAvoid (Rold.I 0) X W) =
    SMTree.Envelope.closure (admissibleKptSTree family)
      (Rnew.I (cut+1)) (X ∪ O) := by
  have hRetained : Rold.I 0 ⊆ Rnew.I 0 :=
    finiteNumericH_newRoot_run_retains_old_levels_larger_top
      family L k M hAvoid X W oldTop newTop
      hTopLe hTopSeed Rold Rnew
  exact finiteNumericH_newRoot_run_preCut_absorbs_of_retained_above
    family L k M hAvoid (Rold.I 0) X W newTop
    Rnew cut hCut hRetained hAbove

#print axioms Kk.envelope_algorithmRun_selected_levels_mono_seed_height
#print axioms Kk.finiteNumericH_newRoot_run_retains_old_levels_larger_top
#print axioms Kk.finiteNumericH_newRoot_preCut_absorbs_old_run_larger_top

end Kk
