import Kk.B3CutVisibleTransfer
import Kk.B3CutStarNormalForm
import Kk.B3PhysicalBadCoreIff
import Mathlib.Tactic

/-!
# Track D: full B3 transfer without an independent marked-source nonemptiness hypothesis

English-first hostile proof audit:
docs/audits/2026-11-15-track-d-cut-visible-no-nonempty-english.md

The OLD transfer hypothesis requiring an already nonempty Marked source
is redundant when one assumes UNIFORM cut-visible coverage into the
ACTUALLY CHOSEN Marked outputs: any failed Full corrected B3 produces a
real eligible positive Full cut-neighbour, whose coverage itself supplies
a chosen Marked source element.

No no-(I2) assumption, selected-front graph-age projection, or common
labelled inverse-source orbit is smuggled into the statement.
-/

namespace Kk

open SuccessorTree.V10

/-- If NO cut-eligible selected physical original is adjacent to the
tested cut, corrected B3 automatically passes. This is the actual
finite Henson normalized-family statement, without no-(I2).

No assertion about structural I1 or I2 follows from this result. -/
theorem henson_fullB3_of_no_eligible_cut_neighbour
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N cut M : Nat) (hCut : cut < N)
    (original : Fin M → Fin N)
    (Full : Fin M → Prop)
    (hNoCutNeighbour : ∀ v : Fin M, Full v →
      cut+1 ≤ (finiteNumericH (normalizedGraphModel E) k N).freeLevel
        (original v).val →
      (finiteNumericHL (normalizedGraphModel E) k N).binary
        cut (original v).val (0 : Fin 1) ≠ true) :
    (selectedStagePoolPrescribedData
      (finiteNumericH (normalizedGraphModel E) k N)
      cut original Full).CorrectedB3
        (hensonForbiddenFamily ell hell) := by
  classical
  by_contra hFailure
  obtain ⟨v,hFull,hFree,hEdge⟩ :=
    henson_failedSelectedB3_has_eligible_cut_neighbour
      ell hell k hK E hLoops hSym hClique
      N cut M hCut original Full hFailure
  exact hNoCutNeighbour v hFull hFree hEdge

/-- Complete cut-visible output coverage and marked corrected B3
imply Full corrected B3, WITHOUT requiring Marked.source nonempty.

In the sole case where a marked source witness is needed (Full fails),
the checked real forbidden-clique cut-neighbour and the UNIFORM
coverage condition provide it. This is strictly a statement about
chosen complete ordinary-L next-cut types at one numerical H cut.
-/
theorem henson_fullB3_of_cut_visible_complete_outputs_no_nonempty
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N cut M : Nat) (hCut : cut < N)
    (original : Fin M → Fin N)
    (Full Marked : Fin M → Prop)
    (hCutVisible : ∀ v : Fin M, Full v →
      cut+1 ≤ (finiteNumericH (normalizedGraphModel E) k N).freeLevel
        (original v).val →
      (finiteNumericHL (normalizedGraphModel E) k N).binary
        cut (original v).val (0 : Fin 1) = true →
      ∃ T, T ∈ (selectedStagePoolPrescribedData
          (finiteNumericH (normalizedGraphModel E) k N)
          cut original Marked).source ∧
        ((selectedStagePoolPrescribedData
          (finiteNumericH (normalizedGraphModel E) k N)
          cut original Marked).target T).lReduct =
          RelationalPrefixType.ofAgeModel
            (finiteNumericHL (normalizedGraphModel E) k N)
            (cut+1) (original v).val)
    (hMarked :
      (selectedStagePoolPrescribedData
        (finiteNumericH (normalizedGraphModel E) k N)
        cut original Marked).CorrectedB3
          (hensonForbiddenFamily ell hell)) :
    (selectedStagePoolPrescribedData
      (finiteNumericH (normalizedGraphModel E) k N)
      cut original Full).CorrectedB3
        (hensonForbiddenFamily ell hell) := by
  classical
  by_contra hFailure
  obtain ⟨v,hFull,hFree,hEdge⟩ :=
    henson_failedSelectedB3_has_eligible_cut_neighbour
      ell hell k hK E hLoops hSym hClique
      N cut M hCut original Full hFailure
  obtain ⟨T,hT,_hType⟩ := hCutVisible v hFull hFree hEdge
  have hNonempty :
      ∃ T, T ∈ (selectedStagePoolPrescribedData
        (finiteNumericH (normalizedGraphModel E) k N)
        cut original Marked).source := ⟨T,hT⟩
  exact hFailure
    (henson_fullB3_of_cut_visible_complete_outputs
      ell hell k hK E hLoops hSym hClique
      N cut M hCut original Full Marked
      hNonempty hCutVisible hMarked)

/-- The failure-projection form of the source-nonempty-free transfer.
It is still conditional on full COMPLETE chosen-type coverage:
this must be verified in the concrete omitted-level construction. -/
theorem henson_cut_visible_fullB3_failure_implies_marked_failure_no_nonempty
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N cut M : Nat) (hCut : cut < N)
    (original : Fin M → Fin N)
    (Full Marked : Fin M → Prop)
    (hCutVisible : ∀ v : Fin M, Full v →
      cut+1 ≤ (finiteNumericH (normalizedGraphModel E) k N).freeLevel
        (original v).val →
      (finiteNumericHL (normalizedGraphModel E) k N).binary
        cut (original v).val (0 : Fin 1) = true →
      ∃ T, T ∈ (selectedStagePoolPrescribedData
          (finiteNumericH (normalizedGraphModel E) k N)
          cut original Marked).source ∧
        ((selectedStagePoolPrescribedData
          (finiteNumericH (normalizedGraphModel E) k N)
          cut original Marked).target T).lReduct =
          RelationalPrefixType.ofAgeModel
            (finiteNumericHL (normalizedGraphModel E) k N)
            (cut+1) (original v).val)
    (hFailure :
      ¬ (selectedStagePoolPrescribedData
        (finiteNumericH (normalizedGraphModel E) k N)
        cut original Full).CorrectedB3
          (hensonForbiddenFamily ell hell)) :
    ¬ (selectedStagePoolPrescribedData
      (finiteNumericH (normalizedGraphModel E) k N)
      cut original Marked).CorrectedB3
        (hensonForbiddenFamily ell hell) := by
  intro hMarked
  exact hFailure
    (henson_fullB3_of_cut_visible_complete_outputs_no_nonempty
      ell hell k hK E hLoops hSym hClique
      N cut M hCut original Full Marked
      hCutVisible hMarked)


/-- At one actual represented no-(I2) Kpt closure, FULL corrected (B3)
follows from a MARKED corrected-(B3) source covering every genuinely
eligible physical positive Full cut-neighbour, WITHOUT an independently
given marked name.

No-(I2) is needed only to show that a represented marked name has its
complete next-cut ordinary-L type among the ACTUALLY CHOSEN marked
outputs, despite old L+ source-fibre deduplication. Once cut-visible
chosen-output coverage is established, the strengthened cut-visible
transfer does not need a separate nonemptiness premise.

This remains conditional on the all-Full-cut-neighbours-marked
hypothesis; it does NOT establish that hypothesis for a resolved diary. -/
theorem henson_fullB3_of_no_i2_marked_closure_cut_neighbours_no_nonempty
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N cut M : Nat) (hCut : cut < N)
    (original : Fin M → Fin N)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (Z : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (Full Marked : Fin M → Prop)
    (hMarkedRepresented : ∀ v : Fin M, Marked v →
      closureSelectedOriginal
        (hensonForbiddenFamily ell hell)
        (finiteNumericH (normalizedGraphModel E) k N)
        hAvoid original Z cut v)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      a ∈ Z ∧ ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        b ∈ Z ∧ SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut)
    (hAllCutNeighboursMarked : ∀ v : Fin M, Full v →
      cut+1 ≤ (finiteNumericH (normalizedGraphModel E) k N).freeLevel
        (original v).val →
      (finiteNumericHL (normalizedGraphModel E) k N).binary
        cut (original v).val (0 : Fin 1) = true → Marked v)
    (hMarkedB3 :
      (selectedStagePoolPrescribedData
        (finiteNumericH (normalizedGraphModel E) k N)
        cut original Marked).CorrectedB3
          (hensonForbiddenFamily ell hell)) :
    (selectedStagePoolPrescribedData
      (finiteNumericH (normalizedGraphModel E) k N)
      cut original Full).CorrectedB3
        (hensonForbiddenFamily ell hell) := by
  classical
  let A := finiteNumericH (normalizedGraphModel E) k N
  let C := finiteNumericHL (normalizedGraphModel E) k N
  let G := selectedStagePoolPrescribedData A cut original Marked
  have hVisible : ∀ v : Fin M, Full v →
      cut+1 ≤ A.freeLevel (original v).val →
      C.binary cut (original v).val (0 : Fin 1) = true →
      ∃ T, T ∈ G.source ∧
        (G.target T).lReduct =
          RelationalPrefixType.ofAgeModel C
            (cut+1) (original v).val := by
    intro v hFull hEligible hCutEdge
    have hv : Marked v :=
      hAllCutNeighboursMarked v hFull hEligible hCutEdge
    obtain ⟨T,hT,hType⟩ :=
      selected_named_nextL_permitted_of_no_I2
        (hensonForbiddenFamily ell hell)
        A hAvoid cut original Z Marked
        hMarkedRepresented hNoI2 v hv hEligible
    refine ⟨T,hT,?_⟩
    calc
      (G.target T).lReduct =
          (A.partialTypeAt (cut+1) (original v).val).lReduct :=
        hType.symm
      _ = RelationalPrefixType.ofAgeModel C
            (cut+1) (original v).val :=
        partialTypeAt_lReduct_eq_ofAgeModel
          A (cut+1) (original v).val
  exact henson_fullB3_of_cut_visible_complete_outputs_no_nonempty
    ell hell k hK E hLoops hSym hClique
    N cut M hCut original Full Marked hVisible hMarkedB3

#print axioms henson_fullB3_of_no_eligible_cut_neighbour
#print axioms henson_fullB3_of_cut_visible_complete_outputs_no_nonempty
#print axioms henson_cut_visible_fullB3_failure_implies_marked_failure_no_nonempty
#print axioms henson_fullB3_of_no_i2_marked_closure_cut_neighbours_no_nonempty

end Kk
