import Kk.HensonTopI3
import SuccessorTree.V10.I3AlgorithmInterestingBridge
import Mathlib.Tactic

/-!
# Actual Algorithm 5.4 I3 cannot be interesting at top H generation

The checked successor library already identifies an actual positive
Algorithm 5.4 I3 level (one with neither an I1 node nor an I2 meet)
with failure of corrected B3 for the CANONICAL SELECTED crossing
on its full parameter-closed set Z.

The Henson-specific numeric theorem proves corrected B3 at the top
generation for EVERY selected-original pool, at any generation height
k >= ell-1.

Combining these, no positive top-generation level of a genuine
numerical-H parameter-closed envelope can be I3-interesting provided
every closure node lies below an original of ONE fixed finite pool.
No manual comparison of f_ell with an all-eligible pool, no
unproved witness projection, and no extra age axiom is introduced.

The hypothesis that the closure is represented by such a finite
original pool remains visible and must be obtained for the
specially resolved Henson copy before applying the theorem there.
The conclusion concerns top-generation I3 only; arbitrary earlier
generation (B3) failures and diary orbit comparison remain open.
-/

namespace Kk

open SuccessorTree.V10

/-- Genuine normalized Henson finite numerical-H base: a top H
generation cannot be a positive I3-interesting level of the actual
Algorithm 5.4 closure, as soon as I1/I2 are absent and the
complete closure is represented by a fixed original-name pool. -/
theorem henson_algorithm_top_generation_no_I3
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N cut M idx : Nat)
    (hCut : cut < N) (hPos : 0 < cut)
    (hTop : cut = hPosition k idx k)
    (hAvoidH :
      ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
        bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (original : Fin M → Fin N)
    (Z : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (hPool : ∀ z, z ∈ Z →
      ∃ v : Fin M,
        z ≤ (finiteNumericH (normalizedGraphModel E) k N).kptOriginal
          (hensonForbiddenFamily ell hell) hAvoidH (original v))
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      z ∈ Z ∧ LevelTree.lev z = cut)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      a ∈ Z ∧ ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        b ∈ Z ∧ SuccessorTree.SMTree.Envelope.SameComponent a b ∧
          LevelTree.lev (LevelTree.meet a b) = cut) :
    ¬ SuccessorTree.SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree (hensonForbiddenFamily ell hell)) Z cut := by
  intro hInteresting
  have hFailure :=
    algorithmI3_failsCorrectedB3
      (hensonForbiddenFamily ell hell)
      (finiteNumericH (normalizedGraphModel E) k N)
      hAvoidH original Z hPool cut hPos hNoI1 hNoI2 hInteresting
  have hB3 :=
    henson_selected_top_generation_B3
      ell hell k hK E hLoops hSym hClique
      N cut M idx hCut hTop original
      (closureSelectedOriginal
        (hensonForbiddenFamily ell hell)
        (finiteNumericH (normalizedGraphModel E) k N)
        hAvoidH original Z cut)
  exact hFailure hB3

end Kk
