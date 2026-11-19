import Kk.TrackDEvenRealNoI1
import Kk.TrackDZeroStarFullI2
import Kk.TrackDPhysicalHSymmetry
import Kk.TrackDEmptyPhysicalCutStar
import Kk.TrackDPlannedStageRoles
import Mathlib.Tactic

/-!
# Track D: actual lower-real zero-stage full Kpt source is boring

English proof and adversarial audit BEFORE Lean:
docs/audits/2026-11-19-track-d-true-run-zero-stage-boring-english.md

A genuinely empty ordinary L star on ALL eligible originals of the
ACTUAL pre-cut stage (Run.I(cut+1)) plus absence of a SEED exactly
ending at cut now imply the full I1/I2/I3 absence without any
independent structural or corrected B3 assumptions.

Corollaries handle isolated old-Q dummy bases and lower generations
of selected independent coded vertices; the latter still needs
the true descending stage-Plan hypothesis. No full diary/orbit/BRD
conclusion is asserted.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- An actual finite numerical Henson AlgorithmRun DOES NOT select a
positive lower-real cut if (a) no true seed ends there and (b) EVERY
eligible physical original in its TRUE already-fixed pre-cut stage
pool has zero ORDINARY L adjacency at that cut. This is stronger than
an empty shadow/star only among currently crossing selected names.

The proof separately derives genuine full I1 via source normal form,
genuine full I2 via complete L+/E strict-fork exclusion, and genuine
full chosen corrected B3 via actual empty stage source. -/
theorem henson_actualRun_lower_real_unselected_of_no_seed_and_zero_stage
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
    (hNoSeedAt : ¬ ∃ z : AdmissibleKptNode
      (hensonForbiddenFamily ell hell),
      z ∈ X ∧ LevelTree.lev z = hPosition k idx g)
    (hZeroStage : ∀ v : Fin N,
      v ∈ hStageOriginals (normalizedGraphModel E) k N U
        (Run.I (hPosition k idx g+1)) →
      hPosition k idx g+1 ≤
        (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val →
      (finiteNumericH (normalizedGraphModel E) k N).L.binary
        (hPosition k idx g) v.val (0 : Fin 1) = false) :
    hPosition k idx g ∉ Run.I 0 := by
  classical
  let family := hensonForbiddenFamily ell hell
  let K : AgeTestModel 1 0 1 := normalizedGraphModel E
  let A : EnumeratedPartialStructure 1 0 1 := finiteNumericH K k N
  let cut : Nat := hPosition k idx g
  let J : Set Nat := Run.I (cut+1)
  let Stage : Finset (Fin N) := hStageOriginals K k N U J
  let original : Fin Stage.card → Fin N := hOriginalName Stage
  let Z : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family) J X
  have hSymA : ∀ a b : Nat,
      A.L.binary a b (0 : Fin 1) =
        A.L.binary b a (0 : Fin 1) :=
    finiteNumericH_graph_ordinary_L_symmetric E hSym k N
  have hStageAmbient :
      ∀ v : Fin A.size,
        v ∈ ambientStagePool A (U : Set (Fin A.size)) J →
        v ∈ Stage := by
    intro v hv
    have hvOr : v ∈ U ∨
        (v.val ∈ J ∧ 0 < A.freeLevel v.val) := by
      change v ∈ (U : Set (Fin N)) ∪
        {i : Fin N | i.val ∈ J ∧ 0 < A.freeLevel i.val} at hv
      exact hv
    simpa only [Stage, hStageOriginals, Finset.mem_filter,
      Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      using hvOr
  have hStageZero :
      ∀ v : Fin A.size,
        v ∈ ambientStagePool A (U : Set (Fin A.size)) J →
        cut+1 ≤ A.freeLevel v.val →
        A.L.binary cut v.val (0 : Fin 1) = false := by
    intro v hv hFree
    exact hZeroStage v (hStageAmbient v hv) hFree
  have hNoI1 :
      ¬ ∃ z : AdmissibleKptNode family,
        z ∈ Z ∧ LevelTree.lev z = cut :=
    finiteNumericH_even_real_no_full_I1_of_zero_stage
      family K k N hAvoidA hSymA
      J X (U : Set (Fin A.size)) hX
      idx g hPos hNoSeedAt hStageZero
  obtain ⟨_hPoolSub,hPool,_hPoolFinal⟩ :=
    finiteNumericH_run_stage_and_final_pool_exhaust_same_closure
      family K k N hAvoidA U X hX top Run cut hBelow
  have hZeroFull : ∀ v : Fin Stage.card,
      closureSelectedOriginal family A hAvoidA original Z cut v →
      cut+1 ≤ A.freeLevel (original v).val →
      A.L.binary cut (original v).val (0 : Fin 1) = false := by
    intro v _ hFree
    have hv : original v ∈ Stage := hOriginalName_mem Stage v
    have hvAmbient :
        original v ∈ ambientStagePool A
          (U : Set (Fin A.size)) J := by
      have hvOr : original v ∈ U ∨
          ((original v).val ∈ J ∧
            0 < A.freeLevel (original v).val) := by
        simpa only [Stage, hStageOriginals, Finset.mem_filter,
          Finset.mem_univ, true_and, Set.mem_ofPred_eq] using hv
      change original v ∈ (U : Set (Fin N)) ∪
        {i : Fin N | i.val ∈ J ∧ 0 < A.freeLevel i.val}
      exact hvOr
    exact hStageZero (original v) hvAmbient hFree
  have hNoI2 :
      ¬ ∃ a : AdmissibleKptNode family, a ∈ Z ∧
        ∃ b : AdmissibleKptNode family, b ∈ Z ∧
          SMTree.Envelope.SameComponent a b ∧
          LevelTree.lev (LevelTree.meet a b) = cut :=
    full_kpt_no_i2_of_no_i1_and_zero_full_physical_star
      family A hSymA hAvoidA original Z hPool cut hZeroFull hNoI1
  apply henson_actualRun_lower_real_unselected_of_empty_stage_cutStar
    ell hell k hK E hLoops hSym hClique N U hAvoidA X hX
    top Run hTop idx g hg hPos hBelow hCut hNoI1 hNoI2
  intro v hFull hFree hPositive
  have hFalse := hZeroFull v hFull hFree
  rw [hFalse] at hPositive
  cases hPositive

/-- An actual isolated old-Q dummy base requires NO planned retained
stage hypotheses: literal physical H positive-neighbour generation
and base isolation give zero ordinary cut bits on ALL eligible stage
originals. No initial seed at the cut is the only new source condition.
Genuine I1/I2/I3 exclusions are derived, not hypothesized. -/
theorem henson_actualRun_isolated_dummy_lower_real_skip_of_no_seed
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
    (hNoSeedAt : ¬ ∃ z : AdmissibleKptNode
      (hensonForbiddenFamily ell hell),
      z ∈ X ∧ LevelTree.lev z = hPosition k idx g)
    (hIsolated : ∀ j, E idx j = false) :
    hPosition k idx g ∉ Run.I 0 := by
  apply henson_actualRun_lower_real_unselected_of_no_seed_and_zero_stage
    ell hell k hK E hLoops hSym hClique N U hAvoidA X hX
    top Run hTop idx g hg hPos hBelow hCut hNoSeedAt
  intro v _ hFree
  by_cases hp :
      (finiteNumericH (normalizedGraphModel E) k N).L.binary
        (hPosition k idx g) v.val (0 : Fin 1) = true
  · obtain ⟨j,m,_hij,_hgm,_hm,_hAddress,hBase⟩ :=
      finiteNumericH_eligible_lower_cut_neighbour_is_higher
        E k N idx g hg hCut v hFree hp
    have hZero : E idx j = false := hIsolated j
    rw [hZero] at hBase
    cases hBase
  · cases h :
      (finiteNumericH (normalizedGraphModel E) k N).L.binary
        (hPosition k idx g) v.val (0 : Fin 1) with
      | false => rfl
      | true => exact False.elim (hp h)

/-- Under the genuine descending stage-role hypothesis, a lower
generation of an independent selected coding vertex has NO possible
eligible physical positive ordinary-L neighbour among any actual
stage original (including all meet/auxiliary source representations).
Together with no seed ending at that cut this proves it boring;
NO explicit I1/I2 or B3 assumption remains.

Neither the descending Plan hypothesis nor seed exclusion is hidden
or inferred from a selected graph-age shadow. -/
theorem henson_actualRun_selected_coded_lower_real_skip_of_no_seed
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
    (hNoSeedAt : ¬ ∃ z : AdmissibleKptNode
      (hensonForbiddenFamily ell hell),
      z ∈ X ∧ LevelTree.lev z = hPosition k idx g)
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
  apply henson_actualRun_lower_real_unselected_of_no_seed_and_zero_stage
    ell hell k hK E hLoops hSym hClique N U hAvoidA X hX
    top Run hTop idx g hg hPos hBelow hCut hNoSeedAt
  intro v hv hFree
  let cut : Nat := hPosition k idx g
  let K : AgeTestModel 1 0 1 := normalizedGraphModel E
  let Stage : Finset (Fin N) :=
    hStageOriginals K k N U (Run.I (cut+1))
  by_cases hp :
      (finiteNumericH K k N).L.binary cut v.val (0 : Fin 1) = true
  · obtain ⟨j,m,hij,_hgm,_hm,hAddr,hBase⟩ :=
      finiteNumericH_eligible_lower_cut_neighbour_is_higher
        E k N idx g hg hCut v hFree hp
    let i : Fin Stage.card := Stage.equivFin ⟨v,hv⟩
    have hName : hOriginalName Stage i = v := by
      simp [hOriginalName,i] <;> rfl
    have hAddrName :
        (hOriginalName Stage i).val = hPosition k j m := by
      simpa only [hName] using hAddr
    have hNo : E idx j = false :=
      resolvedQ_stage_selected_base_has_no_retained_neighbour
        K k N U (Run.I (cut+1)) Plan hAbove
        role E hQ hIndependent hRootDummy hPlanShape
        idx j m hij hSelectedBase i hAddrName
    rw [hNo] at hBase
    cases hBase
  · cases h : (finiteNumericH K k N).L.binary
        cut v.val (0 : Fin 1) with
      | false => rfl
      | true => exact False.elim (hp h)

#print axioms Kk.henson_actualRun_lower_real_unselected_of_no_seed_and_zero_stage
#print axioms Kk.henson_actualRun_isolated_dummy_lower_real_skip_of_no_seed
#print axioms Kk.henson_actualRun_selected_coded_lower_real_skip_of_no_seed

end Kk
