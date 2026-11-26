import Kk.TrackDPlannedStageRoles
import Kk.PhysicalLowerRealCutNeighbour
import Kk.TrackDPhysicalHSymmetry
import Kk.EqualCutFullType
import Mathlib.Tactic

/-!
# Complete actual-stage coherence at positive lower generations

English proof and independent reviews precede this source in
`docs/positive_generation_stage_coherence_english_20261123.md` and
`docs/bounded_stage_roles_repair_english_20261123.md`.

At an omitted resolved-Q base, every positive eligible current-stage
ordinary neighbour is a selected TOP original. Consequently the cut
column at every lower generation equals the generation-zero column.
At a strictly positive generation, that latter coordinate is already
old, so complete old type equality forces complete next L+/E equality.

The pool is the entire genuine stage original pool. Root and Plan
contracts apply only to canonical generations m ≤ k. No selected
shadow, age-neutrality, no-fork, no-I1, or no-I2 premise is used.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The exact ordinary cut bit of EVERY genuinely eligible actual stage
original agrees with its bit at the same base's generation-zero copy.
This includes negative bits and names with no ordinary positive edge.
The tested generation may be zero; it must remain strictly below TOP. -/
theorem resolvedQ_lower_generation_stage_cut_bit_eq_generation_zero
    (E : Nat → Nat → Bool)
    (k N : Nat) (U : Finset (Fin N))
    (J Plan : Set Nat) (hJPlan : J ⊆ Plan)
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
    (b g : Nat) (hg : g < k)
    (hCut : hPosition k b g < N)
    (hOmitted : ResolvedQOmittedBase (role b))
    (v : Fin (hStageOriginals (normalizedGraphModel E) k N U J).card)
    (hFree : hPosition k b g + 1 ≤
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel
        (hOriginalName
          (hStageOriginals (normalizedGraphModel E) k N U J) v).val) :
    (finiteNumericH (normalizedGraphModel E) k N).L.binary
        (hPosition k b g)
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
  let c : Nat := hPosition k b g
  let q : Nat := hPosition k b 0
  change A.L.binary c (name v).val (0 : Fin 1) =
    A.L.binary q (name v).val (0 : Fin 1)
  have hFreeC : c + 1 ≤ A.freeLevel (name v).val := hFree
  have hQLe : q ≤ c := by
    dsimp [q, c, hPosition]
    omega
  have hQCut : q < N := lt_of_le_of_lt hQLe hCut
  have hFreeQ : q + 1 ≤ A.freeLevel (name v).val := by omega
  have hk : 0 < k := by omega
  have hForward :
      A.L.binary c (name v).val (0 : Fin 1) = true →
      A.L.binary q (name v).val (0 : Fin 1) = true := by
    intro hPositive
    obtain ⟨j,m,hbj,_hgm,hm,hAddr,hEdge⟩ :=
      finiteNumericH_eligible_lower_cut_neighbour_is_higher
        E k N b g hg hCut (name v) hFreeC hPositive
    obtain ⟨_hCode,hTop⟩ :=
      resolvedQ_stage_omitted_positive_name_is_selected_top
        K k N U J Plan hJPlan role E hQ
        hRootDummy hPlanShape b j m hm hbj hOmitted
        v hAddr hEdge
    have hTopAddr : (name v).val = hPosition k j k := by
      simpa only [hTop] using hAddr
    change hNumericBinary K.binary k
      (hPosition k b 0) (name v).val (0 : Fin 1) = true
    rw [hTopAddr]
    apply (hNumericBinary_real_forward_iff K.binary
      k b j 0 k (0 : Fin 1) hbj (Nat.zero_le k) (Nat.le_refl k)).2
    refine ⟨Or.inl hk,?_⟩
    change E b j = true
    exact hEdge
  have hBackward :
      A.L.binary q (name v).val (0 : Fin 1) = true →
      A.L.binary c (name v).val (0 : Fin 1) = true := by
    intro hPositive
    obtain ⟨j,m,hbj,_hgm,hm,hAddr,hEdge⟩ :=
      finiteNumericH_eligible_lower_cut_neighbour_is_higher
        E k N b 0 hk hQCut (name v) hFreeQ hPositive
    obtain ⟨_hCode,hTop⟩ :=
      resolvedQ_stage_omitted_positive_name_is_selected_top
        K k N U J Plan hJPlan role E hQ
        hRootDummy hPlanShape b j m hm hbj hOmitted
        v hAddr hEdge
    have hTopAddr : (name v).val = hPosition k j k := by
      simpa only [hTop] using hAddr
    change hNumericBinary K.binary k
      (hPosition k b g) (name v).val (0 : Fin 1) = true
    rw [hTopAddr]
    apply (hNumericBinary_real_forward_iff K.binary
      k b j g k (0 : Fin 1) hbj (Nat.le_of_lt hg) (Nat.le_refl k)).2
    refine ⟨Or.inl hg,?_⟩
    change E b j = true
    exact hEdge
  cases hC : A.L.binary c (name v).val (0 : Fin 1) with
  | false =>
    cases hQBit : A.L.binary q (name v).val (0 : Fin 1) with
    | false => rfl
    | true =>
      have hImpossible := hBackward hQBit
      rw [hC] at hImpossible
      cases hImpossible
  | true =>
    exact (hForward hC).symm

/-- At a POSITIVE lower generation of an omitted resolved-Q base,
complete old types of any two eligible actual stage originals determine
their complete next L+/E types. The generation-zero coordinate is
strictly old and determines the ordinary cut bit by the first theorem.

No structural or chosen-age verdict is a hypothesis or conclusion here. -/
theorem resolvedQ_positive_lower_generation_stage_full_type_coherent
    (E : Nat → Nat → Bool)
    (k N : Nat) (U : Finset (Fin N))
    (J Plan : Set Nat) (hJPlan : J ⊆ Plan)
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
    (b g : Nat) (hg0 : 0 < g) (hg : g < k)
    (hCut : hPosition k b g < N)
    (hOmitted : ResolvedQOmittedBase (role b))
    (v w : Fin (hStageOriginals (normalizedGraphModel E) k N U J).card)
    (hFreeV : hPosition k b g + 1 ≤
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel
        (hOriginalName
          (hStageOriginals (normalizedGraphModel E) k N U J) v).val)
    (hFreeW : hPosition k b g + 1 ≤
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel
        (hOriginalName
          (hStageOriginals (normalizedGraphModel E) k N U J) w).val)
    (hOld :
      (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
        (hPosition k b g)
        (hOriginalName
          (hStageOriginals (normalizedGraphModel E) k N U J) v).val =
      (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
        (hPosition k b g)
        (hOriginalName
          (hStageOriginals (normalizedGraphModel E) k N U J) w).val) :
    (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
        (hPosition k b g + 1)
        (hOriginalName
          (hStageOriginals (normalizedGraphModel E) k N U J) v).val =
      (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
        (hPosition k b g + 1)
        (hOriginalName
          (hStageOriginals (normalizedGraphModel E) k N U J) w).val := by
  let K : AgeTestModel 1 0 1 := normalizedGraphModel E
  let A : EnumeratedPartialStructure 1 0 1 := finiteNumericH K k N
  let Stage : Finset (Fin N) := hStageOriginals K k N U J
  let name : Fin Stage.card → Fin N := hOriginalName Stage
  let c : Nat := hPosition k b g
  let q : Nat := hPosition k b 0
  have hQOld : q < c := by
    dsimp [q, c, hPosition]
    omega
  have hOldPhysical :
      A.partialTypeAt c (name v).val =
        A.partialTypeAt c (name w).val := hOld
  have hReduct :
      (A.partialTypeAt c (name v).val).lReduct =
        (A.partialTypeAt c (name w).val).lReduct :=
    congrArg (fun T : PartialTypeWithE c 1 0 1 => T.lReduct)
      hOldPhysical
  rw [partialTypeAt_lReduct_eq_ofAgeModel A c (name v).val,
    partialTypeAt_lReduct_eq_ofAgeModel A c (name w).val] at hReduct
  have hQBit := congrArg
    (fun T : RelationalPrefixType c 1 0 1 =>
      T.binary (some (⟨q,hQOld⟩ : Fin c)) none (0 : Fin 1)) hReduct
  change A.L.binary q (name v).val (0 : Fin 1) =
    A.L.binary q (name w).val (0 : Fin 1) at hQBit
  have hVBit :
      A.L.binary c (name v).val (0 : Fin 1) =
        A.L.binary q (name v).val (0 : Fin 1) :=
    resolvedQ_lower_generation_stage_cut_bit_eq_generation_zero
      E k N U J Plan hJPlan role hQ hRootDummy hPlanShape
      b g hg hCut hOmitted v hFreeV
  have hWBit :
      A.L.binary c (name w).val (0 : Fin 1) =
        A.L.binary q (name w).val (0 : Fin 1) :=
    resolvedQ_lower_generation_stage_cut_bit_eq_generation_zero
      E k N U J Plan hJPlan role hQ hRootDummy hPlanShape
      b g hg hCut hOmitted w hFreeW
  have hCutBit :
      A.L.binary c (name v).val (0 : Fin 1) =
        A.L.binary c (name w).val (0 : Fin 1) :=
    hVBit.trans (hQBit.trans hWBit.symm)
  have hSymA : ∀ i j : Nat,
      A.L.binary i j (0 : Fin 1) = A.L.binary j i (0 : Fin 1) :=
    finiteNumericH_graph_ordinary_L_symmetric E hQ.sym k N
  exact full_equal_ordinary_cut_column_determines_next_type
    A hSymA c (name v) (name w) hFreeV hFreeW hCutBit hOldPhysical

#print axioms Kk.resolvedQ_lower_generation_stage_cut_bit_eq_generation_zero
#print axioms Kk.resolvedQ_positive_lower_generation_stage_full_type_coherent

end Kk
