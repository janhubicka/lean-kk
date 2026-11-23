import Kk.TrackDPreCutStageSource
import Kk.TrackDResolvedQBaseRoles
import Mathlib.Tactic

/-!
# Track D: descending actual stage-role classification and canonical marked source

English-first proof and 20 hostile checks were committed BEFORE this Lean source:
docs/audits/2026-11-18-track-d-planned-stage-roles-english.md

The true stage original pool of Run.I(cut+1) is not guessed from the final
Run.I 0. Under the explicit higher-level descending induction and the
original-Q construction axioms, every positive physical source original
at an omitted base must be a selected TOP coding original.
The marked original source is defined by closure membership AND selected
TOP physical role, so no additional marked representation or base coverage
premise remains. The actually chosen marked corrected-B3 test and the
complete no-I1/no-I2 conditions are still separate application obligations.
-/

/-! Canonical-generation role contracts repaired after the English audit in
`docs/bounded_stage_roles_repair_english_20261123.md`. Every address tested
against root or Plan roles now carries its genuine generation bound m ≤ k. -/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Precisely the original-Q construction's chronological edge axioms.
Same-block auxiliary vertices can be adjacent; their retained flag is
constant. No assertion about full Kpt source selection follows. -/
structure ResolvedQChronologicalAxioms
    (role : Nat → ResolvedQBaseRole)
    (E : Nat → Nat → Bool) : Prop where
  sym : ∀ i j, E i j = E j i
  dummy : ∀ i j, role i = .dummy → E i j = false
  codedAux : ∀ i j (s : Bool) (block : Nat) (keep : Bool),
    i < j → role i = .coded s →
    role j = .auxiliary block keep → E i j = false
  auxDifferent : ∀ i j (p q : Nat) (a b : Bool),
    p ≠ q →
    role i = .auxiliary p a →
    role j = .auxiliary q b → E i j = false
  blockFlag : ∀ i j (block : Nat) (a b : Bool),
    role i = .auxiliary block a →
    role j = .auxiliary block b → a = b

/-- Every genuine finite stage original address either belongs to the
root cap, is a selected TOP coded original, or comes from a whole
retained auxiliary block, assuming ONLY the levels already selected
at this stage lie in the proposed retained set.

No source closure or no-I2 assumption is hidden here. -/
theorem resolvedQ_stage_name_shape_of_planned_levels
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N : Nat) (U : Finset (Fin N))
    (J Plan : Set Nat) (hJPlan : J ⊆ Plan)
    (role : Nat → ResolvedQBaseRole)
    (hRootDummy : ∀ v : Fin N, v ∈ U →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m →
        role j = .dummy)
    (hPlanShape : ∀ v : Fin N, v.val ∈ Plan →
      0 < (finiteNumericH K k N).freeLevel v.val →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m →
        (role j = .coded true ∧ m = k) ∨
        (∃ block : Nat, role j = .auxiliary block true))
    (v : Fin (hStageOriginals K k N U J).card)
    (j m : Nat) (hm : m ≤ k)
    (hAddr : (hOriginalName (hStageOriginals K k N U J) v).val =
      hPosition k j m) :
    role j = .dummy ∨
      (role j = .coded true ∧ m = k) ∨
      (∃ block : Nat, role j = .auxiliary block true) := by
  classical
  let Stage : Finset (Fin N) := hStageOriginals K k N U J
  have hMember : hOriginalName Stage v ∈ Stage :=
    hOriginalName_mem Stage v
  have hMember' :
      hOriginalName Stage v ∈ U ∨
        ((hOriginalName Stage v).val ∈ J ∧
          0 < (finiteNumericH K k N).freeLevel
            (hOriginalName Stage v).val) := by
    simpa only [Stage, hStageOriginals, Finset.mem_filter,
      Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      using hMember
  rcases hMember' with hRoot | ⟨hSelected,hPositive⟩
  · exact Or.inl (hRootDummy (hOriginalName Stage v)
      hRoot j m hm hAddr)
  · rcases hPlanShape (hOriginalName Stage v)
      (hJPlan hSelected) hPositive j m hm hAddr with hCode | hAux
    · exact Or.inr (Or.inl hCode)
    · exact Or.inr (Or.inr hAux)

/-- An omitted physical Q base has no positive later original
in a genuine descending-stage list except a selected TOP code.
The whole-block retained flag and true stage inclusion are explicit;
the actual selected type graph-age shadow is never substituted. -/
theorem resolvedQ_stage_omitted_positive_name_is_selected_top
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N : Nat) (U : Finset (Fin N))
    (J Plan : Set Nat) (hJPlan : J ⊆ Plan)
    (role : Nat → ResolvedQBaseRole)
    (E : Nat → Nat → Bool)
    (hQ : ResolvedQChronologicalAxioms role E)
    (hRootDummy : ∀ v : Fin N, v ∈ U →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m →
        role j = .dummy)
    (hPlanShape : ∀ v : Fin N, v.val ∈ Plan →
      0 < (finiteNumericH K k N).freeLevel v.val →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m →
        (role j = .coded true ∧ m = k) ∨
        (∃ block : Nat, role j = .auxiliary block true))
    (idx j m : Nat) (hm : m ≤ k) (hij : idx < j)
    (hOmitted : ResolvedQOmittedBase (role idx))
    (v : Fin (hStageOriginals K k N U J).card)
    (hAddr : (hOriginalName (hStageOriginals K k N U J) v).val =
      hPosition k j m)
    (hEdge : E idx j = true) :
    role j = .coded true ∧ m = k := by
  have hShape := resolvedQ_stage_name_shape_of_planned_levels
    K k N U J Plan hJPlan role hRootDummy hPlanShape
    v j m hm hAddr
  have hRetained : ResolvedQRetainedBase (role j) := by
    rcases hShape with hDummy | hCode | ⟨block,hAux⟩
    · exact Or.inl hDummy
    · exact Or.inr (Or.inl hCode.1)
    · exact Or.inr (Or.inr ⟨block,hAux⟩)
  have hCoded : role j = .coded true :=
    resolvedQ_omitted_base_positive_retained_is_selected_coding
      role E hQ.sym hQ.dummy hQ.codedAux
      hQ.auxDifferent hQ.blockFlag
      idx j hij hOmitted hRetained hEdge
  rcases hShape with hDummy | hCode | ⟨block,hAux⟩
  · rw [hDummy] at hCoded
    cases hCoded
  · exact ⟨hCoded,hCode.2⟩
  · rw [hAux] at hCoded
    cases hCoded

/-- For a selected coding base, independence makes the entire later
proposed-retained ORIGINAL-Q neighbour set empty, including dummy
and auxiliary targets; this is stronger than the omitted-base theorem. -/
theorem resolvedQ_stage_selected_base_has_no_retained_neighbour
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N : Nat) (U : Finset (Fin N))
    (J Plan : Set Nat) (hJPlan : J ⊆ Plan)
    (role : Nat → ResolvedQBaseRole)
    (E : Nat → Nat → Bool)
    (hQ : ResolvedQChronologicalAxioms role E)
    (hIndependent : ∀ i j,
      role i = .coded true →
      role j = .coded true → E i j = false)
    (hRootDummy : ∀ v : Fin N, v ∈ U →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m →
        role j = .dummy)
    (hPlanShape : ∀ v : Fin N, v.val ∈ Plan →
      0 < (finiteNumericH K k N).freeLevel v.val →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m →
        (role j = .coded true ∧ m = k) ∨
        (∃ block : Nat, role j = .auxiliary block true))
    (idx j m : Nat) (hm : m ≤ k) (hij : idx < j)
    (hSelected : role idx = .coded true)
    (v : Fin (hStageOriginals K k N U J).card)
    (hAddr : (hOriginalName (hStageOriginals K k N U J) v).val =
      hPosition k j m) :
    E idx j = false := by
  have hShape := resolvedQ_stage_name_shape_of_planned_levels
    K k N U J Plan hJPlan role hRootDummy hPlanShape
    v j m hm hAddr
  have hRetained : ResolvedQRetainedBase (role j) := by
    rcases hShape with hDummy | hCode | ⟨block,hAux⟩
    · exact Or.inl hDummy
    · exact Or.inr (Or.inl hCode.1)
    · exact Or.inr (Or.inr ⟨block,hAux⟩)
  exact resolvedQ_selected_coded_has_no_later_retained_neighbour
    role E hQ.sym hQ.dummy hQ.codedAux hIndependent
    idx j hij hSelected hRetained

/-- Canonical TRUE closure-represented marked source:
only selected TOP physical coding originals represented in the actual
pre-cut Kpt closure, never a selected-shadow arbitrary source. -/
def resolvedQStageSelectedTopMarked
    (role : Nat → ResolvedQBaseRole)
    (k : Nat) {N : Nat}
    (Stage : Finset (Fin N))
    (Full : Fin Stage.card → Prop)
    (v : Fin Stage.card) : Prop :=
  Full v ∧ ∃ j : Nat,
    (hOriginalName Stage v).val = hPosition k j k ∧
    role j = .coded true

/-- The full positive later-base neighbour coverage demanded by the
verified real-cut corrected-B3 transfer is automatically satisfied by
the CANONICAL closure-represented selected-TOP marked predicate.
All auxiliary Kpt parameters/meets are represented by true stage names.
No marked source existence premise remains; it can be empty. -/
theorem resolvedQ_stage_full_base_coverage_of_planned_levels
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N : Nat) (U : Finset (Fin N))
    (J Plan : Set Nat) (hJPlan : J ⊆ Plan)
    (role : Nat → ResolvedQBaseRole)
    (E : Nat → Nat → Bool)
    (hQ : ResolvedQChronologicalAxioms role E)
    (hRootDummy : ∀ v : Fin N, v ∈ U →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m →
        role j = .dummy)
    (hPlanShape : ∀ v : Fin N, v.val ∈ Plan →
      0 < (finiteNumericH K k N).freeLevel v.val →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m →
        (role j = .coded true ∧ m = k) ∨
        (∃ block : Nat, role j = .auxiliary block true))
    (idx : Nat) (hOmitted : ResolvedQOmittedBase (role idx))
    (Stage : Finset (Fin N))
    (hStage : Stage = hStageOriginals K k N U J)
    (Full : Fin Stage.card → Prop)
    (v : Fin Stage.card) (hFull : Full v)
    (j m : Nat) (hij : idx < j) (_hgm : 0 ≤ m) (hm : m ≤ k)
    (hAddr : (hOriginalName Stage v).val = hPosition k j m)
    (hEdge : E idx j = true) :
    resolvedQStageSelectedTopMarked role k Stage Full v := by
  subst Stage
  obtain ⟨hCode,hTop⟩ :=
    resolvedQ_stage_omitted_positive_name_is_selected_top
      K k N U J Plan hJPlan role E hQ
      hRootDummy hPlanShape idx j m hm hij hOmitted
      v hAddr hEdge
  refine ⟨hFull,j,?_,hCode⟩
  simpa only [hTop] using hAddr

/-- True physical AlgorithmRun lower-real cut:
the descending retained-role hypothesis and actual Q edge axioms
automatically discharge BOTH marked-source representation and FULL
positive higher-base neighbour coverage. The only remaining
nonstructural age gate is the ACTUAL CHOSEN marked corrected-B3 test,
alongside genuine full no-I1/no-I2.

The outer result excludes a cut of Run.I 0 without identifying the
unknown final original pool with the proposed retained source.
It makes no global diary/unavoidability/orbit claim. -/
theorem henson_actualRun_lower_real_unselected_of_planned_stage_markedB3
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
    (hRootDummy : ∀ v : Fin N, v ∈ U →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m →
        role j = .dummy)
    (hPlanShape : ∀ v : Fin N, v.val ∈ Plan →
      0 < (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m →
        (role j = .coded true ∧ m = k) ∨
        (∃ block : Nat, role j = .auxiliary block true))
    (hOmitted : ResolvedQOmittedBase (role idx)) :
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
    let Marked : Fin Stage.card → Prop :=
      resolvedQStageSelectedTopMarked role k Stage Full
    (selectedStagePoolPrescribedData
      (finiteNumericH (normalizedGraphModel E) k N)
      cut original Marked).CorrectedB3
        (hensonForbiddenFamily ell hell) →
    cut ∉ Run.I 0 := by
  classical
  intro cut Stage original Z Full Marked hMarkedB3
  apply henson_actualRun_lower_real_unselected_of_stage_covered_marked_B3
    ell hell k hK E hLoops hSym hClique
    N U hAvoidA X hX top Run hTop
    idx g hg hPos hBelow hCut hNoI1 hNoI2
    Marked
  · intro v hv
    exact hv.1
  · intro v hFull j m hij hgm hm hAddr hEdge
    exact resolvedQ_stage_full_base_coverage_of_planned_levels
      (normalizedGraphModel E) k N U
      (Run.I (cut+1)) Plan hAbove role E hQ
      hRootDummy hPlanShape
      idx hOmitted Stage rfl Full v hFull
      j m hij (Nat.zero_le m) hm hAddr hEdge
  · exact hMarkedB3

#print axioms Kk.resolvedQ_stage_name_shape_of_planned_levels
#print axioms Kk.resolvedQ_stage_omitted_positive_name_is_selected_top
#print axioms Kk.resolvedQ_stage_selected_base_has_no_retained_neighbour
#print axioms Kk.resolvedQ_stage_full_base_coverage_of_planned_levels
#print axioms Kk.henson_actualRun_lower_real_unselected_of_planned_stage_markedB3

end Kk
