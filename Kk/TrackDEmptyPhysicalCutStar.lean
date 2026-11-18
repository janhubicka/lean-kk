import Kk.TrackDPlannedStageRoles
import Kk.TrackDPreCutStageSource
import Kk.B3CutVisibleNoNonempty
import Mathlib.Tactic

/-!
# Track D: genuine physical empty cut-star eliminates corrected B3

English-first proof and hostile audit committed BEFORE the Lean source:
docs/audits/2026-11-18-track-d-empty-physical-cut-star-english.md

The actual pre-cut closure includes generated Kpt meets and E parameters.
An empty physical ordinary-L cut-star on the TRUE stage original pool
gives full corrected B3 without any Marked target. If genuine full I1/I2
are excluded, the actual run skips the cut. We apply this result
to (a) isolated dummy bases unconditionally on the retained Plan and
(b) omitted lower generations of selected coding bases, under a genuine
descending stage-Plan inclusion and selected independence.

No global omission induction or general diary BRD theorem is asserted.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Empty actual stage FULL physical cut-star suffices for actual
lower-real boringness under genuine no-I1/no-I2.
The stage B3 test is discharged directly, WITHOUT a nonempty
Marked source, then the verified same-Z stage/final pool theorem
passes it to the genuine final source.

Actual stage is Run.I(cut+1), never an assumed final retained Plan. -/
theorem henson_actualRun_lower_real_unselected_of_empty_stage_cutStar
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N : Nat)
    (U : Finset (Fin N))
    (hAvoidA : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (X : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (hX : X ⊆ ambientPrefixPool
      (hensonForbiddenFamily ell hell)
      (finiteNumericH (normalizedGraphModel E) k N)
      hAvoidA (U : Set (Fin N)))
    (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell)) X top)
    (hTop : ∃ x ∈ X, LevelTree.lev x = top)
    (idx g : Nat) (hg : g < k)
    (hPos : 0 < hPosition k idx g)
    (hBelow : hPosition k idx g < top)
    (hCut : hPosition k idx g < N)
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode
      (hensonForbiddenFamily ell hell),
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (hPosition k idx g+1)) X ∧
      LevelTree.lev z = hPosition k idx g)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode
      (hensonForbiddenFamily ell hell),
      a ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (hPosition k idx g+1)) X ∧
      ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        b ∈ SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily ell hell))
          (Run.I (hPosition k idx g+1)) X ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = hPosition k idx g) :
    let cut : Nat := hPosition k idx g
    let Stage : Finset (Fin N) :=
      hStageOriginals (normalizedGraphModel E) k N U (Run.I (cut+1))
    let original : Fin Stage.card → Fin N := hOriginalName Stage
    let Z : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)) :=
      SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (cut+1)) X
    let Full : Fin Stage.card → Prop :=
      closureSelectedOriginal (hensonForbiddenFamily ell hell)
        (finiteNumericH (normalizedGraphModel E) k N)
        hAvoidA original Z cut
    (∀ v : Fin Stage.card, Full v →
      cut+1 ≤ (finiteNumericH (normalizedGraphModel E) k N).freeLevel
        (original v).val →
      (finiteNumericHL (normalizedGraphModel E) k N).binary
        cut (original v).val (0 : Fin 1) ≠ true) →
    cut ∉ Run.I 0 := by
  classical
  intro cut Stage original Z Full hNoPositive
  have hStageB3 :
      (selectedStagePoolPrescribedData
        (finiteNumericH (normalizedGraphModel E) k N)
        cut original Full).CorrectedB3
          (hensonForbiddenFamily ell hell) :=
    henson_fullB3_of_no_eligible_cut_neighbour
      ell hell k hK E hLoops hSym hClique
      N cut Stage.card hCut original Full hNoPositive
  exact henson_actualRun_lower_real_unselected_of_stage_covered_marked_B3
    ell hell k hK E hLoops hSym hClique
    N U hAvoidA X hX top Run hTop
    idx g hg hPos hBelow hCut hNoI1 hNoI2
    Full
    (by intro v hv; exact hv)
    (by intro v hv j m hij hgm hm hAddr hEdge; exact hv)
    hStageB3

/-- An ISOLATED original Q dummy base has an empty ordinary-L
physical star at EVERY genuine lower-real cut, regardless of
what other actual higher cuts the run selected. Thus it cannot
produce nonstructural I3 once full structural I1/I2 is absent.

This does not exclude auxiliary-E-caused genuine I1/I2. -/
theorem henson_actualRun_isolated_dummy_lower_real_unselected
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N : Nat)
    (U : Finset (Fin N))
    (hAvoidA : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (X : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (hX : X ⊆ ambientPrefixPool
      (hensonForbiddenFamily ell hell)
      (finiteNumericH (normalizedGraphModel E) k N)
      hAvoidA (U : Set (Fin N)))
    (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell)) X top)
    (hTop : ∃ x ∈ X, LevelTree.lev x = top)
    (idx g : Nat) (hg : g < k)
    (hPos : 0 < hPosition k idx g)
    (hBelow : hPosition k idx g < top)
    (hCut : hPosition k idx g < N)
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode
      (hensonForbiddenFamily ell hell),
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (hPosition k idx g+1)) X ∧
      LevelTree.lev z = hPosition k idx g)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode
      (hensonForbiddenFamily ell hell),
      a ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (hPosition k idx g+1)) X ∧
      ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        b ∈ SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily ell hell))
          (Run.I (hPosition k idx g+1)) X ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = hPosition k idx g)
    (hIsolatedBase : ∀ j : Nat, E idx j = false) :
    hPosition k idx g ∉ Run.I 0 := by
  classical
  apply henson_actualRun_lower_real_unselected_of_empty_stage_cutStar
    ell hell k hK E hLoops hSym hClique
    N U hAvoidA X hX top Run hTop
    idx g hg hPos hBelow hCut hNoI1 hNoI2
  intro cut Stage original Z Full v hFull hFree hEdge
  intro hPositive
  obtain ⟨j,m,hij,hgm,hm,hAddress,hBase⟩ :=
    finiteNumericH_eligible_lower_cut_neighbour_is_higher
      E k N idx g hg hCut (original v) hFree hPositive
  have hZero : E idx j = false := hIsolatedBase j
  rw [hZero] at hBase
  cases hBase

/-- At a LOWER physical generation g<k of a selected coding base,
the actual stage positive ordinary cut-star is empty once its
already-fixed higher levels have the proposed whole-block/selected-top
roles. Independent selected coding vertices cannot be future
ordinary Q neighbours; auxiliary and dummy future roles are also
negative. Thus no CHOSEN B3 checking is needed in this subcase.

Actual full I1 and I2 exclusions and the descending higher-stage
Plan inclusion are still explicit premises. -/
theorem henson_actualRun_selected_coded_lower_real_unselected
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N : Nat)
    (U : Finset (Fin N))
    (hAvoidA : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (X : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (hX : X ⊆ ambientPrefixPool
      (hensonForbiddenFamily ell hell)
      (finiteNumericH (normalizedGraphModel E) k N)
      hAvoidA (U : Set (Fin N)))
    (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell)) X top)
    (hTop : ∃ x ∈ X, LevelTree.lev x = top)
    (idx g : Nat) (hg : g < k)
    (hPos : 0 < hPosition k idx g)
    (hBelow : hPosition k idx g < top)
    (hCut : hPosition k idx g < N)
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode
      (hensonForbiddenFamily ell hell),
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (hPosition k idx g+1)) X ∧
      LevelTree.lev z = hPosition k idx g)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode
      (hensonForbiddenFamily ell hell),
      a ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (hPosition k idx g+1)) X ∧
      ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        b ∈ SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily ell hell))
          (Run.I (hPosition k idx g+1)) X ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = hPosition k idx g)
    (Plan : Set Nat)
    (hAbove : Run.I (hPosition k idx g+1) ⊆ Plan)
    (role : Nat → ResolvedQBaseRole)
    (hQ : ResolvedQChronologicalAxioms role E)
    (hIndependent : ∀ i j,
      role i = .coded true →
      role j = .coded true → E i j = false)
    (hRootDummy : ∀ v : Fin N, v ∈ U →
      ∀ j m : Nat, v.val = hPosition k j m →
        role j = .dummy)
    (hPlanShape : ∀ v : Fin N, v.val ∈ Plan →
      0 < (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val →
      ∀ j m : Nat, v.val = hPosition k j m →
        (role j = .coded true ∧ m = k) ∨
        (∃ block : Nat, role j = .auxiliary block true))
    (hSelectedBase : role idx = .coded true) :
    hPosition k idx g ∉ Run.I 0 := by
  classical
  apply henson_actualRun_lower_real_unselected_of_empty_stage_cutStar
    ell hell k hK E hLoops hSym hClique
    N U hAvoidA X hX top Run hTop
    idx g hg hPos hBelow hCut hNoI1 hNoI2
  intro cut Stage original Z Full v hFull hFree hEdge
  intro hPositive
  obtain ⟨j,m,hij,hgm,hm,hAddress,hBase⟩ :=
    finiteNumericH_eligible_lower_cut_neighbour_is_higher
      E k N idx g hg hCut (original v) hFree hPositive
  have hNo : E idx j = false :=
    resolvedQ_stage_selected_base_has_no_retained_neighbour
      (normalizedGraphModel E) k N U
      (Run.I (cut+1)) Plan hAbove role E hQ hIndependent
      hRootDummy hPlanShape
      idx j m hij hSelectedBase v hAddress
  rw [hNo] at hBase
  cases hBase

#print axioms Kk.henson_actualRun_lower_real_unselected_of_empty_stage_cutStar
#print axioms Kk.henson_actualRun_isolated_dummy_lower_real_unselected
#print axioms Kk.henson_actualRun_selected_coded_lower_real_unselected

end Kk
