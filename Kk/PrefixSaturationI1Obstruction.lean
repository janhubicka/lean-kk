import Kk.NumericHBaseExtensionCoherence
import SuccessorTree.EnvelopeRun
import Mathlib.Tactic

/-!
# Track C: full root-PREFIX seed saturation FORCES every level I1

English-first adversarial proof and fourteen hostile checks:
  docs/track_c_prefix_saturation_I1_english_audit.md

This is a negative mathematical audit of the ORIGINAL (now superseded)
PR #165 seed formula. A physical original of Kpt level top has
actual admissible predecessors at EVERY lower level. If one inserts
the ENTIRE ambient original-prefix pool as initial seeds, each of
these predecessors is already an I1 witness in the genuine pre-cut
closure of Algorithm 5.4. Therefore EVERY level 0,...,top is selected.

This proves why an ambientPrefixPool is a physical SOURCE COVER,
not a valid small seed set for a BOUNDED resolved-copy envelope.
The corrected constructive PR #165 seeds only the new ORIGINAL
Kpt node(s), not all their proper prefixes.

No graph-age proxy, extra E on an L-only age witness or B3
assumption is involved. This is a genuine Kpt LevelTree result.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- If the true Kpt seed set contains EVERY predecessor of one
node x of level top, then EVERY numerical level p≤top is
selected by EVERY genuine AlgorithmRun on these seeds.

The witnesses are genuine admissible Kpt ancestors and already
belong to the actual seed set, hence to every pre-cut closure.
They force I1 before any I2/B3 decision is considered. -/
theorem kpt_full_prefix_seeds_force_all_levels
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Y : Set (AdmissibleKptNode family))
    (x : AdmissibleKptNode family)
    (top : Nat)
    (hTop : LevelTree.lev x = top)
    (hAll : ∀ z : AdmissibleKptNode family, z ≤ x → z ∈ Y)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y top) :
    ∀ p : Nat, p ≤ top → p ∈ R.I 0 := by
  intro p hp
  have hpx : p ≤ LevelTree.lev x := by omega
  let a : AdmissibleKptNode family :=
    LevelTree.ancestor x p hpx
  have haY : a ∈ Y :=
    hAll a (LevelTree.ancestor_le x p hpx)
  have haZ :
      a ∈ SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (p+1)) Y :=
    SMTree.Envelope.subset_closure
      (admissibleKptSTree family) (R.I (p+1)) Y haY
  have hLev : LevelTree.lev a = p :=
    LevelTree.level_ancestor x p hpx
  have hSelected : p ∈ R.I p := by
    by_cases heq : p = top
    · subst p
      rw [R.topI]
      simp
    · have hlt : p < top := by omega
      have hI1 : SMTree.Envelope.IsInterestingAt
          (normalizedKptSMTree family)
          (SMTree.Envelope.closure
            (admissibleKptSTree family) (R.I (p+1)) Y) p :=
        Or.inl ⟨a,haZ,hLev⟩
      have hStep := (R.interesting_step p hlt hI1).1
      rw [hStep]
      simp
  have hTail : R.I p = {q | q ∈ R.I 0 ∧ p ≤ q} :=
    R.I_eq_final_tail_of_run p hp
  rw [hTail] at hSelected
  exact hSelected.1

/-- Stronger exact description: for prefix-saturated actual Kpt
seeds, the AlgorithmRun's FINAL selected set is ALL levels
0,...,top, not merely some interesting auxiliary levels.

The reverse containment uses the independently verified
AlgorithmRun selected-level upper bound. -/
theorem kpt_full_prefix_seeds_final_levels_all
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Y : Set (AdmissibleKptNode family))
    (x : AdmissibleKptNode family)
    (top : Nat)
    (hTop : LevelTree.lev x = top)
    (hAll : ∀ z : AdmissibleKptNode family, z ≤ x → z ∈ Y)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y top) :
    R.I 0 = {p : Nat | p ≤ top} := by
  ext p
  constructor
  · intro hp
    exact (R.I_mem_bounds 0 (Nat.zero_le top) p hp).2
  · intro hp
    exact kpt_full_prefix_seeds_force_all_levels
      family Y x top hTop hAll R p hp

/-- Actual PHYSICAL original-prefix pools are indeed saturated:
if the initial seeds contain ambientPrefixPool W and W contains
one genuine original w of free level top, every level is forced I1.

This is a regression theorem for the overlarge (superseded)
next-seed definition. It uses the real admissible Kpt original,
its E free level and literal old prefix relation. -/
theorem kpt_physical_full_prefix_pool_forces_all_levels
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (W : Set (Fin A.size))
    (w : Fin A.size) (hw : w ∈ W)
    (Y : Set (AdmissibleKptNode family))
    (hPrefixSeeds :
      ambientPrefixPool family A hAvoid W ⊆ Y)
    (top : Nat) (hFree : A.freeLevel w.val = top)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y top) :
    R.I 0 = {p : Nat | p ≤ top} := by
  let x : AdmissibleKptNode family :=
    A.kptOriginal family hAvoid w
  have hTop : LevelTree.lev x = top := hFree
  have hAll : ∀ z : AdmissibleKptNode family,
      z ≤ x → z ∈ Y := by
    intro z hz
    apply hPrefixSeeds
    exact ⟨x, ⟨w,hw,rfl⟩,hz⟩
  exact kpt_full_prefix_seeds_final_levels_all
    family Y x top hTop hAll R

#print axioms Kk.kpt_full_prefix_seeds_force_all_levels
#print axioms Kk.kpt_full_prefix_seeds_final_levels_all
#print axioms Kk.kpt_physical_full_prefix_pool_forces_all_levels

end Kk
