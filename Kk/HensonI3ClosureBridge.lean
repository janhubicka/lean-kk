import Kk.HensonTopI3
import SuccessorTree.V10.I3ActualGraphRepresentation
import Mathlib.Tactic

/-!
# From the actual Algorithm 5.4 I3 source to Henson selected-pool B3

The author does not use the all-originals ambient pool at an I3 stage.
The real source is the set of closure types crossing the tested cut,
with the prescribed COMPLETE next-level type of each source type.

The pinned successor library proves that such a finite full crossing
has exactly the B3 age test of a selected-original pool if every
source/target pair is represented by one of the fixed real originals.
No artificially large all-eligible original pool is substituted.

Composing that generic equality with the verified Henson
top-generation selected-pool result gives a concrete conditional
theorem about the ACTUAL prescribed source function at top generation.

One application-specific hypothesis remains: every source type of
the actual parameter-closed Algorithm 5.4 I3 crossing must be traced
to a fixed original preserving both complete old and next L+ types.
The theorem does NOT claim that the macro-diary state (D,F) alone
supplies this representation, nor that lower-generation auxiliary
B3 failures project to selected graph-age events.
-/

namespace Kk

open SuccessorTree.V10

/-- The full corrected finite L-only B3 age test of a prescribed
crossing F is automatically satisfied at top numerical H generation
k once the *actual source and next type graph* of F is represented
by a fixed pool of numerical H originals.

This holds at k=ell as in the manuscript, and at every k with
ell<=k+1. The source-to-original hypothesis is displayed explicitly
and is the remaining Algorithm 5.4 closure identification to prove.
-/
theorem henson_represented_top_I3_correctedB3
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N cut M idx : Nat)
    (hCut : cut < N)
    (hTop : cut = hPosition k idx k)
    (original : Fin M → Fin N)
    (F : PrescribedBoringData cut 1 0 1)
    (hRepresented : ∀ T, T ∈ F.source →
      ∃ v : Fin M,
        cut+1 ≤
          (finiteNumericH (normalizedGraphModel E) k N).freeLevel
            (original v).val ∧
        T = (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
            cut (original v).val ∧
        F.target T =
          (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
            (cut+1) (original v).val) :
    F.CorrectedB3 (hensonForbiddenFamily ell hell) := by
  let A : EnumeratedPartialStructure 1 0 1 :=
    finiteNumericH (normalizedGraphModel E) k N
  have hPool :
      F.CorrectedB3 (hensonForbiddenFamily ell hell) ↔
      (selectedStagePoolPrescribedData A cut original
        (selectedFromActualGraph A cut original F)).CorrectedB3
          (hensonForbiddenFamily ell hell) :=
    correctedB3_iff_selectedFromActualGraph
      (hensonForbiddenFamily ell hell)
      A cut original F hRepresented
  apply hPool.mpr
  exact henson_selected_top_generation_B3 ell hell k hK
    E hLoops hSym hClique N cut M idx hCut hTop
    original (selectedFromActualGraph A cut original F)

end Kk
