import Kk.PositiveGenerationStructural
import Kk.ActualRunStructuralOrLowerReal
import Mathlib.Tactic

/-!
# Omitted TOP cuts and all positive-generation stage coherence

English proof and independent review were committed before implementation:
`docs/top_generation_stage_coherence_english_20261124.md` and
`docs/audits/2026-11-24-top-generation-coherence-independent-review-common-source.md`.

A positive later neighbour of a TOP cut is another TOP, by the exact
TOP-to-TOP gate. On the whole eligible stage, its cut column equals the
strictly older generation-zero column. This supplies the missing TOP
structural argument and extends positive coherence to 0<g<=k.
TOP B3 alone is not used as a structural test. Actual TOP nonselection
follows only after deriving both full structural exclusions.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Every positive ordinary neighbour strictly after a real TOP cut is a
TOP of a later base, with the same directed base atom. This decoder itself
permits k=0 and requires no ordinary symmetry or stage-role assumption. -/
theorem physical_top_real_cut_positive_generators
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k i y : Nat) (t : Fin d)
    (hLater : hPosition k i k < y)
    (hPositive : hNumericBinary B k (hPosition k i k) y t = true) :
    ∃ j : Nat, i < j ∧ y = hPosition k j k ∧ B i j t = true := by
  obtain ⟨u,j,q,m,huj,hq,hm,hGate,hDir⟩ :=
    (hNumericBinary_true_iff B k (hPosition k i k) y t).1 hPositive
  rcases hDir with ⟨hCut,hY,hB⟩ | ⟨hCut,hY,hB⟩
  · obtain ⟨hiu,hkq⟩ :=
      hPosition_injective_bounded k i k u q (Nat.le_refl k) hq hCut
    have hTop : m = k := by
      rcases hGate with hLess | ⟨hSame,hTop⟩
      · omega
      · omega
    refine ⟨j,by omega,?_,?_⟩
    · simpa only [hTop] using hY
    · simpa only [hiu] using hB
  · have hSmaller := hPosition_lt_of_block_lt k u j q m hq huj
    have hReverse : y < hPosition k i k := by
      calc
        y = hPosition k u q := hY
        _ < hPosition k j m := hSmaller
        _ = hPosition k i k := hCut.symm
    exact False.elim (by omega)

/-- The entire eligible stage column at an omitted TOP base equals its
column at the same base's generation-zero coordinate. Positive edges are
allowed: the TOP-to-TOP tie supplies the forward TOP bit. Both positive
implications are proved, so false bits are included as well. -/
theorem resolvedQ_top_generation_stage_cut_bit_eq_generation_zero
    (E : Nat → Nat → Bool)
    (k N : Nat) (hk : 0 < k) (U : Finset (Fin N))
    (J Plan : Set Nat) (hJPlan : J ⊆ Plan)
    (role : Nat → ResolvedQBaseRole)
    (hQ : ResolvedQChronologicalAxioms role E)
    (hRootDummy : ∀ v : Fin N, v ∈ U →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m → role j = .dummy)
    (hPlanShape : ∀ v : Fin N, v.val ∈ Plan →
      0 < (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m →
        (role j = .coded true ∧ m = k) ∨
        (∃ block : Nat, role j = .auxiliary block true))
    (b : Nat) (hCut : hPosition k b k < N)
    (hOmitted : ResolvedQOmittedBase (role b))
    (v : Fin (hStageOriginals (normalizedGraphModel E) k N U J).card)
    (hFree : hPosition k b k + 1 ≤
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel
        (hOriginalName
          (hStageOriginals (normalizedGraphModel E) k N U J) v).val) :
    (finiteNumericH (normalizedGraphModel E) k N).L.binary
        (hPosition k b k)
        (hOriginalName
          (hStageOriginals (normalizedGraphModel E) k N U J) v).val
        (0 : Fin 1) =
      (finiteNumericH (normalizedGraphModel E) k N).L.binary
        (hPosition k b 0)
        (hOriginalName
          (hStageOriginals (normalizedGraphModel E) k N U J) v).val
        (0 : Fin 1) := by
  let K : AgeTestModel 1 0 1 := normalizedGraphModel E
  let A : EnumeratedPartialStructure 1 0 1 := finiteNumericH K k N
  let Stage : Finset (Fin N) := hStageOriginals K k N U J
  let name : Fin Stage.card → Fin N := hOriginalName Stage
  let c : Nat := hPosition k b k
  let q : Nat := hPosition k b 0
  have hQOld : q < c := by
    dsimp [q,c,hPosition]
    omega
  have hQCut : q < N := lt_trans hQOld hCut
  have hFreeC : c+1 ≤ A.freeLevel (name v).val := hFree
  have hFreeQ : q+1 ≤ A.freeLevel (name v).val := by omega
  have hForward : A.L.binary c (name v).val (0 : Fin 1) = true →
      A.L.binary q (name v).val (0 : Fin 1) = true := by
    intro hPositive
    have hLater : hPosition k b k < (name v).val := by
      have hBound := A.freeLevel_le (name v).val
      change hPosition k b k+1 ≤ A.freeLevel (name v).val at hFreeC
      omega
    obtain ⟨j,hbj,hAddr,hEdge⟩ :=
      physical_top_real_cut_positive_generators K.binary k b (name v).val
        (0 : Fin 1) hLater hPositive
    change hNumericBinary K.binary k
      (hPosition k b 0) (name v).val (0 : Fin 1) = true
    rw [hAddr]
    exact (hNumericBinary_real_forward_iff K.binary k b j 0 k
      (0 : Fin 1) hbj (Nat.zero_le k) (Nat.le_refl k)).2
      ⟨Or.inl hk,hEdge⟩
  have hBackward : A.L.binary q (name v).val (0 : Fin 1) = true →
      A.L.binary c (name v).val (0 : Fin 1) = true := by
    intro hPositive
    obtain ⟨j,m,hbj,_hgm,hm,hAddr,hEdge⟩ :=
      finiteNumericH_eligible_lower_cut_neighbour_is_higher
        E k N b 0 hk hQCut (name v) hFreeQ hPositive
    obtain ⟨_hCode,hTop⟩ :=
      resolvedQ_stage_omitted_positive_name_is_selected_top
        K k N U J Plan hJPlan role E hQ hRootDummy hPlanShape
        b j m hm hbj hOmitted v hAddr hEdge
    have hTopAddr : (name v).val = hPosition k j k := by
      simpa only [hTop] using hAddr
    change hNumericBinary K.binary k
      (hPosition k b k) (name v).val (0 : Fin 1) = true
    rw [hTopAddr]
    apply (hNumericBinary_real_forward_iff K.binary k b j k k
      (0 : Fin 1) hbj (Nat.le_refl k) (Nat.le_refl k)).2
    refine ⟨Or.inr ⟨rfl,rfl⟩,?_⟩
    change E b j = true
    exact hEdge
  change A.L.binary c (name v).val (0 : Fin 1) =
    A.L.binary q (name v).val (0 : Fin 1)
  cases hC : A.L.binary c (name v).val (0 : Fin 1) with
  | false =>
    cases hQBit : A.L.binary q (name v).val (0 : Fin 1) with
    | false => rfl
    | true =>
      have hImpossible := hBackward hQBit
      rw [hC] at hImpossible
      cases hImpossible
  | true => exact (hForward hC).symm

/-- Complete old-to-next L+/E coherence on every eligible stage original
at an omitted TOP cut. The strictly old generation-zero bit determines the
new ordinary bit. No singleton neutrality, no-split or structural premise
is needed at this positive generation. -/
theorem resolvedQ_top_generation_stage_full_type_coherent
    (E : Nat → Nat → Bool)
    (k N : Nat) (hk : 0 < k) (U : Finset (Fin N))
    (J Plan : Set Nat) (hJPlan : J ⊆ Plan)
    (role : Nat → ResolvedQBaseRole)
    (hQ : ResolvedQChronologicalAxioms role E)
    (hRootDummy : ∀ v : Fin N, v ∈ U →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m → role j = .dummy)
    (hPlanShape : ∀ v : Fin N, v.val ∈ Plan →
      0 < (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m →
        (role j = .coded true ∧ m = k) ∨
        (∃ block : Nat, role j = .auxiliary block true))
    (b : Nat) (hCut : hPosition k b k < N)
    (hOmitted : ResolvedQOmittedBase (role b))
    (v w : Fin (hStageOriginals (normalizedGraphModel E) k N U J).card)
    (hFreeV : hPosition k b k+1 ≤
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel
        (hOriginalName (hStageOriginals (normalizedGraphModel E) k N U J) v).val)
    (hFreeW : hPosition k b k+1 ≤
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel
        (hOriginalName (hStageOriginals (normalizedGraphModel E) k N U J) w).val)
    (hOld :
      (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
        (hPosition k b k)
        (hOriginalName (hStageOriginals (normalizedGraphModel E) k N U J) v).val =
      (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
        (hPosition k b k)
        (hOriginalName (hStageOriginals (normalizedGraphModel E) k N U J) w).val) :
    (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
        (hPosition k b k+1)
        (hOriginalName (hStageOriginals (normalizedGraphModel E) k N U J) v).val =
      (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
        (hPosition k b k+1)
        (hOriginalName (hStageOriginals (normalizedGraphModel E) k N U J) w).val := by
  let A := finiteNumericH (normalizedGraphModel E) k N
  let Stage := hStageOriginals (normalizedGraphModel E) k N U J
  let name := hOriginalName Stage
  let c := hPosition k b k
  let q := hPosition k b 0
  have hQOld : q < c := by
    dsimp [q,c,hPosition]
    omega
  have hOldPhysical : A.partialTypeAt c (name v).val =
      A.partialTypeAt c (name w).val := hOld
  have hReduct : (A.partialTypeAt c (name v).val).lReduct =
      (A.partialTypeAt c (name w).val).lReduct :=
    congrArg (fun T : PartialTypeWithE c 1 0 1 => T.lReduct) hOldPhysical
  rw [partialTypeAt_lReduct_eq_ofAgeModel A c (name v).val,
    partialTypeAt_lReduct_eq_ofAgeModel A c (name w).val] at hReduct
  have hQBit := congrArg
    (fun T : RelationalPrefixType c 1 0 1 =>
      T.binary (some (⟨q,hQOld⟩ : Fin c)) none (0 : Fin 1)) hReduct
  change A.L.binary q (name v).val (0 : Fin 1) =
    A.L.binary q (name w).val (0 : Fin 1) at hQBit
  have hVBit := resolvedQ_top_generation_stage_cut_bit_eq_generation_zero
    E k N hk U J Plan hJPlan role hQ hRootDummy hPlanShape b hCut hOmitted v hFreeV
  have hWBit := resolvedQ_top_generation_stage_cut_bit_eq_generation_zero
    E k N hk U J Plan hJPlan role hQ hRootDummy hPlanShape b hCut hOmitted w hFreeW
  have hCutBit : A.L.binary c (name v).val (0 : Fin 1) =
      A.L.binary c (name w).val (0 : Fin 1) :=
    hVBit.trans (hQBit.trans hWBit.symm)
  have hSymA : ∀ i j : Nat,
      A.L.binary i j (0 : Fin 1) = A.L.binary j i (0 : Fin 1) :=
    finiteNumericH_graph_ordinary_L_symmetric E hQ.sym k N
  exact full_equal_ordinary_cut_column_determines_next_type
    A hSymA c (name v) (name w) hFreeV hFreeW hCutBit hOldPhysical

/-- Unified whole-stage coherence for ALL canonical positive generations
0<g<=k. The TOP branch is separate from the strictly lower branch, and
no claim is made at generation zero. -/
theorem resolvedQ_positive_generation_stage_full_type_coherent
    (E : Nat → Nat → Bool)
    (k N : Nat) (U : Finset (Fin N))
    (J Plan : Set Nat) (hJPlan : J ⊆ Plan)
    (role : Nat → ResolvedQBaseRole)
    (hQ : ResolvedQChronologicalAxioms role E)
    (hRootDummy : ∀ v : Fin N, v ∈ U →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m → role j = .dummy)
    (hPlanShape : ∀ v : Fin N, v.val ∈ Plan →
      0 < (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m →
        (role j = .coded true ∧ m = k) ∨
        (∃ block : Nat, role j = .auxiliary block true))
    (b g : Nat) (hg0 : 0 < g) (hg : g ≤ k)
    (hCut : hPosition k b g < N)
    (hOmitted : ResolvedQOmittedBase (role b))
    (v w : Fin (hStageOriginals (normalizedGraphModel E) k N U J).card)
    (hFreeV : hPosition k b g+1 ≤
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel
        (hOriginalName (hStageOriginals (normalizedGraphModel E) k N U J) v).val)
    (hFreeW : hPosition k b g+1 ≤
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel
        (hOriginalName (hStageOriginals (normalizedGraphModel E) k N U J) w).val)
    (hOld :
      (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
        (hPosition k b g)
        (hOriginalName (hStageOriginals (normalizedGraphModel E) k N U J) v).val =
      (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
        (hPosition k b g)
        (hOriginalName (hStageOriginals (normalizedGraphModel E) k N U J) w).val) :
    (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
        (hPosition k b g+1)
        (hOriginalName (hStageOriginals (normalizedGraphModel E) k N U J) v).val =
      (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
        (hPosition k b g+1)
        (hOriginalName (hStageOriginals (normalizedGraphModel E) k N U J) w).val := by
  rcases lt_or_eq_of_le hg with hLower | hTop
  · exact resolvedQ_positive_lower_generation_stage_full_type_coherent
      E k N U J Plan hJPlan role hQ hRootDummy hPlanShape
      b g hg0 hLower hCut hOmitted v w hFreeV hFreeW hOld
  · subst g
    exact resolvedQ_top_generation_stage_full_type_coherent
      E k N hg0 U J Plan hJPlan role hQ hRootDummy hPlanShape
      b hCut hOmitted v w hFreeV hFreeW hOld

/-- Every positive omitted real generation, INCLUDING TOP, has no full
I1 or I2 in the actual pre-cut closure. The arbitrary represented seed
family may consist of all planned cap ancestors; off-cut seed absence
is explicit and no structural verdict is assumed. -/
theorem resolvedQ_actualRun_positive_generation_no_full_I1_I2
    (family : List (NormalizedForbidden 1 0 1))
    (E : Nat → Nat → Bool) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family
      (finiteNumericH (normalizedGraphModel E) k N) hAvoid (U : Set (Fin N)))
    (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun (normalizedKptSMTree family) X top)
    (b g : Nat) (hg0 : 0 < g) (hg : g ≤ k)
    (hCut : hPosition k b g < N)
    (hNoSeedAt : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ X ∧ LevelTree.lev z = hPosition k b g)
    (Plan : Set Nat) (hAbove : Run.I (hPosition k b g+1) ⊆ Plan)
    (role : Nat → ResolvedQBaseRole)
    (hQ : ResolvedQChronologicalAxioms role E)
    (hRootDummy : ∀ v : Fin N, v ∈ U →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m → role j = .dummy)
    (hPlanShape : ∀ v : Fin N, v.val ∈ Plan →
      0 < (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m →
        (role j = .coded true ∧ m = k) ∨
        (∃ block : Nat, role j = .auxiliary block true))
    (hOmitted : ResolvedQOmittedBase (role b)) :
    let cut : Nat := hPosition k b g
    let Z : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family) (Run.I (cut+1)) X
    (¬ ∃ z : AdmissibleKptNode family, z ∈ Z ∧ LevelTree.lev z = cut) ∧
    (¬ ∃ a : AdmissibleKptNode family, a ∈ Z ∧
      ∃ b' : AdmissibleKptNode family, b' ∈ Z ∧
        SMTree.Envelope.SameComponent a b' ∧
        LevelTree.lev (LevelTree.meet a b') = cut) := by
  classical
  intro cut Z
  have hPositive : 0 < cut := by
    dsimp [cut,hPosition]
    omega
  apply finiteNumericH_even_real_no_full_I1_I2_of_coherent_stage
    family (normalizedGraphModel E) k N hAvoid U X hX
    (Run.I (cut+1)) b g hPositive hNoSeedAt
  intro v w hFreeV hFreeW hOld
  exact resolvedQ_positive_generation_stage_full_type_coherent
    E k N U (Run.I (cut+1)) Plan hAbove role hQ hRootDummy hPlanShape
    b g hg0 hg hCut hOmitted v w hFreeV hFreeW hOld

/-- An omitted TOP cut is both unselected and noninteresting in the actual
run. Full structural exclusion is derived first; the existing actual-run
classifier then rules out any remaining selected cut because its generation
would have to be strictly below TOP. No marked-B3 premise remains. -/
theorem henson_actualRun_omitted_top_generation_skip
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N : Nat) (U : Finset (Fin N))
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (X : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (hX : X ⊆ ambientPrefixPool
      (hensonForbiddenFamily ell hell)
      (finiteNumericH (normalizedGraphModel E) k N) hAvoid (U : Set (Fin N)))
    (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell)) X top)
    (hTop : ∃ x ∈ X, LevelTree.lev x = top)
    (b : Nat) (hBelow : hPosition k b k < top)
    (hCut : hPosition k b k < N)
    (hNoSeedAt : ¬ ∃ z : AdmissibleKptNode
      (hensonForbiddenFamily ell hell), z ∈ X ∧ LevelTree.lev z = hPosition k b k)
    (Plan : Set Nat) (hAbove : Run.I (hPosition k b k+1) ⊆ Plan)
    (role : Nat → ResolvedQBaseRole)
    (hQ : ResolvedQChronologicalAxioms role E)
    (hRootDummy : ∀ v : Fin N, v ∈ U →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m → role j = .dummy)
    (hPlanShape : ∀ v : Fin N, v.val ∈ Plan →
      0 < (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m →
        (role j = .coded true ∧ m = k) ∨
        (∃ block : Nat, role j = .auxiliary block true))
    (hOmitted : ResolvedQOmittedBase (role b)) :
    hPosition k b k ∉ Run.I 0 ∧
      ¬ SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree (hensonForbiddenFamily ell hell))
        (SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily ell hell))
          (Run.I (hPosition k b k+1)) X) (hPosition k b k) := by
  have hk : 0 < k := by omega
  have hPos : 0 < hPosition k b k := by
    unfold hPosition
    omega
  obtain ⟨hNoI1,hNoI2⟩ :=
    resolvedQ_actualRun_positive_generation_no_full_I1_I2
      (hensonForbiddenFamily ell hell) E k N hAvoid U X hX top Run
      b k hk (Nat.le_refl k) hCut hNoSeedAt Plan hAbove role hQ
      hRootDummy hPlanShape hOmitted
  have hUnselected : hPosition k b k ∉ Run.I 0 := by
    intro hSelected
    obtain ⟨g,j,hg,hGen⟩ :=
      henson_actualRun_nonstructural_selected_has_lower_real_cut
        ell hell k hK E hLoops hSym hClique N U hAvoid X hX
        top Run hTop (hPosition k b k) hPos hBelow hCut hSelected hNoI1 hNoI2
    have hEqual : k = g :=
      (hPosition_injective_bounded k b k j g (Nat.le_refl k)
        (Nat.le_of_lt hg) hGen).2
    omega
  refine ⟨hUnselected,?_⟩
  intro hInteresting
  have hSelected : hPosition k b k ∈ Run.I (hPosition k b k) := by
    rw [(Run.interesting_step (hPosition k b k) hBelow hInteresting).1]
    exact Set.mem_insert _ _
  rw [Run.I_eq_final_tail_of_run (hPosition k b k) (Nat.le_of_lt hBelow)] at hSelected
  exact hUnselected hSelected.1

#print axioms Kk.physical_top_real_cut_positive_generators
#print axioms Kk.resolvedQ_top_generation_stage_cut_bit_eq_generation_zero
#print axioms Kk.resolvedQ_top_generation_stage_full_type_coherent
#print axioms Kk.resolvedQ_positive_generation_stage_full_type_coherent
#print axioms Kk.resolvedQ_actualRun_positive_generation_no_full_I1_I2
#print axioms Kk.henson_actualRun_omitted_top_generation_skip

end Kk
