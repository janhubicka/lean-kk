import Kk.B3CutStarNormalForm
import Kk.NumericPrefixGapZero
import Mathlib.Tactic

/-!
# Track D: genuine odd numerical H cuts cannot fail full corrected (B3)

English-first proof and hostile checks:
docs/audits/2026-11-15-track-d-odd-cut-full-b3-english.md

The REAL numerical-H ordinary L relation has no edges incident with
an odd dummy coordinate. Failed Henson corrected B3 always produces
one actual eligible selected physical L cut-neighbour. Hence corrected
B3 passes at ALL odd physical cuts for any original-name pool.

This does NOT exclude structural I1/I2, whose auxiliary E records
may force odd free cuts to be retained.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- EVERY genuine odd physical cut of any finite numerical-H Henson
model passes the full corrected B3 test on any selected original pool.

No full-source nonemptiness, no (I1)/(I2) assumption and no diary
selected-shadow fidelity is needed. This is only the L-only
corrected-B3 component of the boringness test. -/
theorem henson_numericH_odd_cut_correctedB3
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N a M : Nat) (hCut : 2*a+1 < N)
    (original : Fin M → Fin N)
    (Full : Fin M → Prop) :
    (selectedStagePoolPrescribedData
      (finiteNumericH (normalizedGraphModel E) k N)
      (2*a+1) original Full).CorrectedB3
        (hensonForbiddenFamily ell hell) := by
  classical
  by_contra hFailure
  obtain ⟨v,_hFull,_hFree,hEdge⟩ :=
    henson_failedSelectedB3_has_eligible_cut_neighbour
      ell hell k hK E hLoops hSym hClique
      N (2*a+1) M hCut original Full hFailure
  have hZero :
      (finiteNumericHL (normalizedGraphModel E) k N).binary
        (2*a+1) (original v).val (0 : Fin 1) = false := by
    change hNumericBinary (normalizedGraphModel E).binary k
      (2*a+1) (original v).val (0 : Fin 1) = false
    exact hNumericBinary_odd_left_false
      (normalizedGraphModel E).binary k a (original v).val (0 : Fin 1)
  rw [hZero] at hEdge
  cases hEdge

#print axioms henson_numericH_odd_cut_correctedB3

end Kk
