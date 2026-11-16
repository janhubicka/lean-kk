import Kk.B3CutVisibleNoNonempty
import Kk.PhysicalLowerRealCutNeighbour
import Mathlib.Tactic

/-!
# Track D: a physical base-block certificate for FULL corrected-B3

English-first proof and 15 hostile checks were committed before Lean:
docs/audits/2026-11-16-track-d-lower-real-base-coverage-b3-english.md

For an actual finite Henson numerical-H lower REAL cut,
every eligible physical positive cut neighbour must be
at a strictly later original base and higher generation.

If the genuinely represented Marked source includes ALL Full
names satisfying that exact BASE-graph physical criterion,
and no-(I2) holds in the SAME full Kpt closure Z, the
chosen complete next-cut ordinary L-type transfer proves
Full corrected-B3 from Marked corrected-B3.

The Marked B3 test and base-block coverage remain explicit
hypotheses: no selected-graph-age projection or global
small-independent source orbit is asserted.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- At an actual non-top real numerical-H cut, a BASE-GRAPH
coverage certificate for ALL genuinely selected higher-generation
Full originals is sufficient to transfer marked corrected B3 to
full corrected B3, assuming genuine Marked representation in Z
and no competing I2 meet at that SAME full closure cut.

No independent Marked nonemptiness hypothesis is needed.
The coverage condition includes auxiliary parameter originals;
a selected diary shadow does NOT automatically satisfy it.
-/
theorem henson_fullB3_of_lower_real_base_covered_marked_source
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N idx g M : Nat) (hg : g < k)
    (hCut : hPosition k idx g < N)
    (original : Fin M → Fin N)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (Z : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (Full Marked : Fin M → Prop)
    (hMarkedRepresented : ∀ v : Fin M, Marked v →
      closureSelectedOriginal
        (hensonForbiddenFamily ell hell)
        (finiteNumericH (normalizedGraphModel E) k N)
        hAvoid original Z (hPosition k idx g) v)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      a ∈ Z ∧ ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        b ∈ Z ∧ SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = hPosition k idx g)
    (hBaseCovered : ∀ v : Fin M, Full v →
      ∀ j m : Nat, idx < j → g < m → m ≤ k →
        (original v).val = hPosition k j m →
        E idx j = true → Marked v)
    (hMarkedB3 :
      (selectedStagePoolPrescribedData
        (finiteNumericH (normalizedGraphModel E) k N)
        (hPosition k idx g) original Marked).CorrectedB3
          (hensonForbiddenFamily ell hell)) :
    (selectedStagePoolPrescribedData
      (finiteNumericH (normalizedGraphModel E) k N)
      (hPosition k idx g) original Full).CorrectedB3
        (hensonForbiddenFamily ell hell) := by
  classical
  have hAllCutNeighboursMarked : ∀ v : Fin M, Full v →
      hPosition k idx g+1 ≤
        (finiteNumericH (normalizedGraphModel E) k N).freeLevel
          (original v).val →
      (finiteNumericHL (normalizedGraphModel E) k N).binary
        (hPosition k idx g) (original v).val (0 : Fin 1) = true →
      Marked v := by
    intro v hFull hFree hEdge
    obtain ⟨j,m,hij,hgm,hm,hAddress,hBase⟩ :=
      finiteNumericH_eligible_lower_cut_neighbour_is_higher
        E k N idx g hg hCut (original v) hFree hEdge
    exact hBaseCovered v hFull j m hij hgm hm hAddress hBase
  exact henson_fullB3_of_no_i2_marked_closure_cut_neighbours_no_nonempty
    ell hell k hK E hLoops hSym hClique
    N (hPosition k idx g) M hCut original hAvoid Z Full Marked
    hMarkedRepresented hNoI2 hAllCutNeighboursMarked hMarkedB3

#print axioms henson_fullB3_of_lower_real_base_covered_marked_source

end Kk
