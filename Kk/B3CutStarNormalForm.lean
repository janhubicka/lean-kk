import Kk.B3ClosureFibreCoherence
import Kk.HensonZeroGenerationClique
import Mathlib.Tactic

/-!
# Track D: canonical cut-star normalization of full corrected (B3)

For a genuine finite K_ell-free numerical H, a failed selected-stage
corrected B3 test always has a *genuinely eligible selected original*
with a positive ordinary L-edge to the tested cut. This is proved
from the actual forbidden-clique signature, including generation zero.

At a single full Kpt closure Z with no (I2) meet at the cut, the
complete corrected B3 test of ALL closure-selected originals is
equivalent to the test on just the **cut-visible** subset. The
equivalence includes the empty-cut-star case: both tests pass then.

The cut-star subset may contain auxiliary parameters; it is NOT
identified with selected active macrodiary branches. Full relative
graph-age fidelity and the common labelled source orbit remain open.

English-first proof / hostile audit:
docs/audits/2026-11-13-track-d-cut-star-normalization-english.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Selected actual original names with a genuine positive ordinary
L-crossing to the tested cut. Their full source and upper types remain
those of the existing selected-stage prescribed function. -/
def hensonCutStarNames
    (E : Nat → Nat → Bool) (k N cut M : Nat)
    (original : Fin M → Fin N)
    (Full : Fin M → Prop) : Fin M → Prop :=
  fun v => Full v ∧
    (finiteNumericHL (normalizedGraphModel E) k N).binary
      cut (original v).val (0 : Fin 1) = true

/-- Any failed genuine selected-stage corrected B3 has a selected,
cut-eligible original with a TRUE ordinary-L edge to the cut.

The nonempty upper portion is extracted from the actual normalized
forbidden-clique signature, not assumed. The B3 age witness has no
auxiliary E; only its complete prescribed old-to-upper L type is used.
-/
theorem henson_failedSelectedB3_has_eligible_cut_neighbour
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
    (hFailure :
      ¬ (selectedStagePoolPrescribedData
        (finiteNumericH (normalizedGraphModel E) k N)
        cut original Full).CorrectedB3
          (hensonForbiddenFamily ell hell)) :
    ∃ v : Fin M,
      Full v ∧
      cut+1 ≤ (finiteNumericH (normalizedGraphModel E) k N).freeLevel
        (original v).val ∧
      (finiteNumericHL (normalizedGraphModel E) k N).binary
        cut (original v).val (0 : Fin 1) = true := by
  let family : List (NormalizedForbidden 1 0 1) :=
    hensonForbiddenFamily ell hell
  let K : AgeTestModel 1 0 1 := normalizedGraphModel E
  let C : AgeTestModel 1 0 1 := finiteNumericHL K k N
  let bad : NormalizedForbidden 1 0 1 :=
    .nontrivial ell (cliquePattern ell) (by omega)
      (cliquePattern_irreducible ell)
  have hBadMem : bad ∈ family := by
    simp [bad, family, hensonForbiddenFamily]
  have hAvoidK : ∀ b, b ∈ family → b.Avoids K :=
    (hensonForbiddenFamily_avoids_iff ell hell E).2
      ⟨hLoops,hSym,hClique⟩
  have hAvoidA : bad.Avoids C :=
    (finiteNumericH_avoids_family family K
      (by intro i; trivial) k N hAvoidK) bad hBadMem
  obtain ⟨W,_hFinite,hSocle,hDelete,hUpper,hBad⟩ :=
    henson_selectedB3_failure_has_clique_witness
      ell hell k hK E hLoops hSym hClique
      N cut M hCut original Full hFailure
  have hBound : bad.patternCard ≤ k+1 := by
    change ell ≤ k+1
    exact hK
  obtain ⟨e,r,hr,hrt,_hrk,_hIrred,hCopy,_hDeleteP,
      hLast,_hLow,hHigh⟩ :=
    normalizedForbidden_bounded_signature_cut
      C W cut k bad hBound
      hSocle hAvoidA (hDelete bad hBadMem) hBad
  let upper : Fin ell := ⟨r,hrt⟩
  have hUpperAbove : cut < e upper :=
    (hHigh upper).1 (by simp [upper])
  obtain ⟨v,hSelected,hFree,hType⟩ :=
    hUpper (e upper) (hCopy.2.1 upper) hUpperAbove
  let last : Fin ell := ⟨r-1,by omega⟩
  have hLastEq : e last = cut := hLast
  have hDistinct : last ≠ upper := by
    intro heq
    have hval := congrArg Fin.val heq
    dsimp [last,upper] at hval
    omega
  have hWEdge : W.binary cut (e upper) (0 : Fin 1) = true := by
    have hCopyEdge :=
      hCopy.2.2.1 last upper hDistinct (0 : Fin 1)
    simpa [hLastEq,cliquePattern,hDistinct] using hCopyEdge
  have hCross := congrArg
      (fun T : RelationalPrefixType (cut+1) 1 0 1 =>
        T.binary
          (some (⟨cut,Nat.lt_succ_self cut⟩ : Fin (cut+1)))
          none (0 : Fin 1)) hType
  change W.binary cut (e upper) (0 : Fin 1) =
    C.binary cut (original v).val (0 : Fin 1) at hCross
  exact ⟨v,hSelected,hFree,hCross.symm.trans hWEdge⟩

/-- A canonical normal form for the genuine complete corrected-B3
test at one NON-(I2) closure cut: retain exactly those Full-selected
originals which are adjacent to the cut in the true ambient L graph.

This includes the empty-cut-star case. The theorem does NOT assert
that this cut-star set equals the macrodiary's marked active branches.
The complete auxiliary parameter closure still determines Full. -/
theorem henson_fullB3_iff_cut_star_of_no_i2
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N cut M : Nat) (hCut : cut < N)
    (original : Fin M → Fin N)
    (Z : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (Full : Fin M → Prop)
    (hAvoidA : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (hFullRepresented : ∀ v : Fin M, Full v →
      closureSelectedOriginal
        (hensonForbiddenFamily ell hell)
        (finiteNumericH (normalizedGraphModel E) k N)
        hAvoidA original Z cut v)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      a ∈ Z ∧ ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        b ∈ Z ∧ SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :
    (selectedStagePoolPrescribedData
      (finiteNumericH (normalizedGraphModel E) k N)
      cut original Full).CorrectedB3
        (hensonForbiddenFamily ell hell) ↔
    (selectedStagePoolPrescribedData
      (finiteNumericH (normalizedGraphModel E) k N)
      cut original (hensonCutStarNames E k N cut M original Full)).CorrectedB3
        (hensonForbiddenFamily ell hell) := by
  classical
  let A := finiteNumericH (normalizedGraphModel E) k N
  let C := finiteNumericHL (normalizedGraphModel E) k N
  let Star : Fin M → Prop :=
    hensonCutStarNames E k N cut M original Full
  by_cases hStar : ∃ v : Fin M, Star v
  · obtain ⟨v0,hv0⟩ := hStar
    have hFull0 : Full v0 := hv0.1
    have hStarRepresented : ∀ v : Fin M, Star v →
        closureSelectedOriginal
          (hensonForbiddenFamily ell hell) A hAvoidA original Z cut v := by
      intro v hv
      exact hFullRepresented v hv.1
    have hFullNonempty : ∃ v : Fin M, Full v := ⟨v0,hFull0⟩
    constructor
    · intro hFullGood
      exact henson_fullB3_of_no_i2_marked_closure_cut_neighbours
        ell hell k hK E hLoops hSym hClique
        N cut M hCut original hAvoidA Z
        Star Full hFullNonempty hFullRepresented hNoI2
        (by
          intro v hv _hEligible _hEdge
          exact hv.1)
        hFullGood
    · intro hStarGood
      exact henson_fullB3_of_no_i2_marked_closure_cut_neighbours
        ell hell k hK E hLoops hSym hClique
        N cut M hCut original hAvoidA Z
        Full Star ⟨v0,hv0⟩ hStarRepresented hNoI2
        (by
          intro v hv _hEligible hEdge
          exact ⟨hv,hEdge⟩)
        hStarGood
  · have hFullGood :
        (selectedStagePoolPrescribedData A cut original Full).CorrectedB3
          (hensonForbiddenFamily ell hell) := by
      by_contra hFail
      obtain ⟨v,hFull,_hEligible,hEdge⟩ :=
        henson_failedSelectedB3_has_eligible_cut_neighbour
          ell hell k hK E hLoops hSym hClique
          N cut M hCut original Full hFail
      exact hStar ⟨v,⟨hFull,hEdge⟩⟩
    have hStarGood :
        (selectedStagePoolPrescribedData A cut original Star).CorrectedB3
          (hensonForbiddenFamily ell hell) := by
      intro S hS
      obtain ⟨v,hSelected,_hEligible,_hOld,_hTarget⟩ :=
        selectedStagePoolPrescribedData_source_original
          A cut original Star S hS
      exact False.elim (hStar ⟨v,hSelected⟩)
    exact ⟨fun _ => hStarGood,fun _ => hFullGood⟩

#print axioms henson_failedSelectedB3_has_eligible_cut_neighbour
#print axioms henson_fullB3_iff_cut_star_of_no_i2

end Kk
