import Kk.NumericHPhysicalNewRootRun
import Mathlib.Tactic

/-!
# Track C: the tight chronological H+ old cutoff enables a bounded new-root run

English proof and fifteen hostile checks committed BEFORE Lean:
  docs/track_c_chronological_top_cut_english_audit.md

A common error is to use the start of the next base-original block
as the OLD numerical carrier N. The new root in that first new block
then has E free cut N-1, so the bounded-envelope precondition N<=top
FAILS by one.

The correct physical old cutoff ends immediately after the last
REAL TOP-generation coordinate of the preceding original block:
  N := hPosition k (b-1) k + 1  (b>0).
This includes EVERY real generation-q copy of all earlier original
blocks i<b, and satisfies BOTH the old-base coherence frontier and
the NEW root's exact free-level height, for j>=b.

Using the mathematically REPAIRED PR #165 root-only seed definition,
the exact physical selected top root and complete inherited old
Kpt closure yield a CONSTRUCTED bounded actual AlgorithmRun and
an exhaustive finite source index without a manually asserted N<=top.

No claim about canonical resolved-diary microevent economy or
unbounded labelled monoid orbits is made.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Every physical REAL generation copy from an OLD block i<b
belongs to the tight numeric prefix ending just after the final
old TOP-generation real position.

No trailing fake target coordinate need be added to represent
these genuine originals and their actual E free cuts. -/
theorem hPosition_old_real_below_previous_top_cut
    (k b i q : Nat)
    (hb : 0 < b) (hi : i < b) (hq : q ≤ k) :
    hPosition k i q < hPosition k (b-1) k+1 := by
  have hiLast : i ≤ b-1 := by omega
  rcases lt_or_eq_of_le hiLast with hStrict | hEq
  · have hBefore :=
      hPosition_lt_of_block_lt k i (b-1) q k hq hStrict
    omega
  · rw [hEq]
    unfold hPosition
    omega

/-- The chronological OLD numerical carrier chosen just after
the previous real top original satisfies ALL THREE necessary
inequalities for a new real top root in block j>=b>0:
  * old N is before the new base original block b;
  * old N is at/below the new root's ACTUAL E-free level;
  * old N is physically inside the enlarged finite carrier M.

The commonly used alternative N=hPosition k b 0 is ONE LARGER
than the first new root's free cut and is not a valid substitute.
-/
theorem hPosition_previous_top_chronological_bounds
    (k b j M : Nat)
    (hb : 0 < b) (hjb : b ≤ j)
    (hTarget : hPosition k j k < M) :
    let N : Nat := hPosition k (b-1) k+1
    N ≤ hPosition k b 0 ∧
    N ≤ hPosition k (j-1) k+1 ∧
    N ≤ M := by
  have hPrevBlock : b-1 < b := by omega
  have hBeforeNewBlock :=
    hPosition_lt_of_block_lt k (b-1) b k 0
      (Nat.le_refl k) hPrevBlock
  have hPrevJ : b-1 < j := by omega
  have hBeforeTarget :=
    hPosition_lt_of_block_lt k (b-1) j k k
      (Nat.le_refl k) hPrevJ
  have hOrigOrder : b-1 ≤ j-1 := by omega
  have hScaled :
      2*(k+1)*(b-1) ≤ 2*(k+1)*(j-1) :=
    Nat.mul_le_mul_left (2*(k+1)) hOrigOrder
  have hBeforeCut :
      hPosition k (b-1) k ≤ hPosition k (j-1) k := by
    unfold hPosition
    omega
  dsimp
  omega

/-- For a genuine top root j≥b>0, the natural tight OLD numerical
prefix contains ALL old original real generations, and the actual
root E-free cut automatically bounds every inherited old Kpt seed,
meet and selected parameter node.

This is the corrected original-ONLY new-root construction: the new
root's entire predecessor chain is a source COVER, not the seed set.
The actual AlgorithmRun, top seed and full finite index are
constructed via the verified base-extension theorem, without an
extra user-supplied N<=top precondition. -/
theorem finiteNumericH_chronological_top_root_bounded_run
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K L : AgeTestModel db du dd)
    (k b j M : Nat)
    (hk : 0 < k) (hb : 0 < b) (hjb : b ≤ j)
    (hTarget : hPosition k j k < M)
    (hBin : ∀ i j : Nat, i < b → j < b →
      ∀ r : Fin db, K.binary i j r = L.binary i j r)
    (hUn : ∀ i : Nat, i < b → ∀ r : Fin du,
      K.unary i r = L.unary i r)
    (hDiag : ∀ i : Nat, i < b → ∀ r : Fin dd,
      K.diagonal i r = L.diagonal i r)
    (hAvoidK : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k (hPosition k (b-1) k+1)).L)
    (hAvoidL : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (U : Set (Fin (hPosition k (b-1) k+1)))
    (X : Set (AdmissibleKptNode family))
    (hSeeds : X ⊆ ambientPrefixPool family
      (finiteNumericH K k (hPosition k (b-1) k+1))
      hAvoidK U)
    (I : Set Nat) :
    let w : Fin M := ⟨hPosition k j k,hTarget⟩
    let Y := finiteNumericH_physicalExtendedSeeds family
      L k M hAvoidL I X ({w} : Set (Fin M))
    HasPhysicalExhaustiveKptRun family Y
      (hPosition k (j-1) k+1) ∧
    Y ⊆ SMTree.Envelope.levelLe
      (T := AdmissibleKptNode family)
      (hPosition k (j-1) k+1) := by
  obtain ⟨hBlock,hNTop,hNM⟩ :=
    hPosition_previous_top_chronological_bounds
      k b j M hb hjb hTarget
  have hj : 0 < j := by omega
  exact finiteNumericH_baseExtension_actual_top_root_run_bounded
    family K L k b (hPosition k (b-1) k+1) M j
    hNM hBlock hk hj hTarget hNTop
    hBin hUn hDiag hAvoidK hAvoidL U X hSeeds I

#print axioms Kk.hPosition_old_real_below_previous_top_cut
#print axioms Kk.hPosition_previous_top_chronological_bounds
#print axioms Kk.finiteNumericH_chronological_top_root_bounded_run

end Kk
