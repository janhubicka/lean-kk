import Kk.PositiveGenerationStageCoherence
import Kk.ResolvedQBlockSeparation
import Kk.K4GenerationZeroSourceSeparator
import Kk.K4SingletonOldNeighbour
import Kk.StageCoherenceStructural
import Mathlib.Tactic

/-!
# Whole actual-stage generation-zero coherence
English-first proof: docs/generation_zero_concrete_plan_english_20261124.md.
Two ordinary Q certificates remain: singleton neutrality (or its old-neighbour
consequence) and constancy on old selected base classes. We derive all physical
type comparisons, including root and auxiliary names, rather than assuming them.
-/

namespace Kk
open SuccessorTree
open SuccessorTree.V10

/-- Actual eligibility at a generation-zero real cut forces a later real BASE.
The E generator rules out same-base names even when their addresses are later. -/
theorem finiteNumericH_eligible_base_zero_has_later_real
    (K : AgeTestModel 1 0 1) (k N b : Nat) (v : Fin N)
    (hFree : hPosition k b 0 + 1 ≤ (finiteNumericH K k N).freeLevel v.val) :
    ∃ j m : Nat, b < j ∧ m ≤ k ∧ v.val = hPosition k j m := by
  let A := finiteNumericH K k N
  have hE : A.E (hPosition k b 0) v.val = true :=
    (A.E_iff_freeLevel (hPosition k b 0) v.val).2 (by exact hFree)
  have hFinite : finiteNumericHE k N (hPosition k b 0) v.val = true := hE
  obtain ⟨_,hExact⟩ := (finiteNumericHE_true_iff k N _ _).1 hFinite
  obtain ⟨j,m,hm,hAddr,hGen⟩ := (exactHEBool_true_iff k _ _).1 hExact
  rcases hGen with ⟨i,q,hij,hq,_hGate,hBefore⟩
  have hbi : b ≤ i := by
    by_contra hNot
    have hib : i < b := by omega
    have hlt := hPosition_lt_of_block_lt k i b q 0 hq hib
    omega
  exact ⟨j,m,by omega,hm,hAddr⟩

theorem full_old_type_eq_implies_ordinary_old_bit_eq
    (A : EnumeratedPartialStructure 1 0 1) (c q x y : Nat)
    (hq : q < c) (hOld : A.partialTypeAt c x = A.partialTypeAt c y) :
    A.L.binary q x (0 : Fin 1) = A.L.binary q y (0 : Fin 1) := by
  have hReduct := congrArg (fun T : PartialTypeWithE c 1 0 1 => T.lReduct) hOld
  rw [partialTypeAt_lReduct_eq_ofAgeModel A c x,
    partialTypeAt_lReduct_eq_ofAgeModel A c y] at hReduct
  have hBit := congrArg
    (fun T : RelationalPrefixType c 1 0 1 =>
      T.binary (some (⟨q,hq⟩ : Fin c)) none (0 : Fin 1)) hReduct
  exact hBit

/-- Canonical singleton neutrality at a real base insertion gives a genuine
old neighbour whenever that base is positive. One-sort actual old columns. -/
theorem k4_positive_old_neighbour_of_singleton_neutral
    (E : Nat → Nat → Bool) (b j : Nat) (hEdge : E b j = true)
    (hNeutral :
      integerGraphAgeCanonical 1 4
        (finiteOldColumnRawBound E 4 1 (Finset.range b) (fun p _ => E p j))
        (trackFSingletonSupport 1 4 (0 : Fin 1) (by decide)) =
      integerGraphAgeCanonical 1 4
        (finiteOldColumnRawBound E 4 1 (Finset.range (b+1)) (fun p _ => E p j))
        (trackFSingletonSupport 1 4 (0 : Fin 1) (by decide))) :
    ∃ p : Nat, p < b ∧ E p j = true := by
  have hAfter := (k4_canonical_singleton_le_two_iff_old_neighbour E 1
    (Finset.range (b+1)) (fun p _ => E p j) (0 : Fin 1)).2
      ⟨b,Finset.mem_range.mpr (Nat.lt_succ_self b),hEdge⟩
  have hBefore :
      integerGraphAgeCanonical 1 4
        (finiteOldColumnRawBound E 4 1 (Finset.range b) (fun p _ => E p j))
        (trackFSingletonSupport 1 4 (0 : Fin 1) (by decide)) ≤ 2 :=
    hNeutral.trans_le hAfter
  obtain ⟨p,hp,hBit⟩ := (k4_canonical_singleton_le_two_iff_old_neighbour E 1
    (Finset.range b) (fun p _ => E p j) (0 : Fin 1)).1 hBefore
  exact ⟨p,Finset.mem_range.mp hp,hBit⟩

/-- Ordinary base-profile certificates imply complete old-to-next coherence
at an omitted generation-zero cut of the entire actual stage J. -/
theorem resolvedQ_generation_zero_stage_full_type_coherent
    (E : Nat → Nat → Bool) (k N : Nat) (hk : 0 < k)
    (U : Finset (Fin N)) (J Plan : Set Nat) (hJPlan : J ⊆ Plan)
    (role : Nat → ResolvedQBaseRole)
    (hQ : ResolvedQChronologicalAxioms role E)
    (hRootDummy : ∀ v : Fin N, v ∈ U →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m → role j = .dummy)
    (hPlanShape : ∀ v : Fin N, v.val ∈ Plan →
      0 < (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m →
        (role j = .coded true ∧ m = k) ∨
        (∃ block : Nat, role j = .auxiliary block true))
    (hBlockInterval : ∀ p b j block : Nat, ∀ a d : Bool,
      p < b → b < j → role p = .auxiliary block a →
      role j = .auxiliary block d →
      role b = .dummy ∨ ∃ f : Bool, role b = .auxiliary block f)
    (b : Nat) (hCut : hPosition k b 0 < N)
    (hOmitted : ResolvedQOmittedBase (role b))
    (hOldNeighbour : ∀ j : Nat, b < j → role j = .coded true →
      E b j = true → ∃ p : Nat, p < b ∧ E p j = true)
    (hNoSplit : ∀ j j' : Nat, b < j → b < j' →
      role j = .coded true → role j' = .coded true →
      (∀ p : Nat, p < b → E p j = E p j') → E b j = E b j')
    (v w : Fin (hStageOriginals (normalizedGraphModel E) k N U J).card)
    (hFreeV : hPosition k b 0 + 1 ≤
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel
        (hOriginalName (hStageOriginals (normalizedGraphModel E) k N U J) v).val)
    (hFreeW : hPosition k b 0 + 1 ≤
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel
        (hOriginalName (hStageOriginals (normalizedGraphModel E) k N U J) w).val)
    (hOld : (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
      (hPosition k b 0)
      (hOriginalName (hStageOriginals (normalizedGraphModel E) k N U J) v).val =
      (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
      (hPosition k b 0)
      (hOriginalName (hStageOriginals (normalizedGraphModel E) k N U J) w).val) :
    (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
      (hPosition k b 0 + 1)
      (hOriginalName (hStageOriginals (normalizedGraphModel E) k N U J) v).val =
      (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
      (hPosition k b 0 + 1)
      (hOriginalName (hStageOriginals (normalizedGraphModel E) k N U J) w).val := by
  let K : AgeTestModel 1 0 1 := normalizedGraphModel E
  let A : EnumeratedPartialStructure 1 0 1 := finiteNumericH K k N
  let Stage := hStageOriginals K k N U J
  let name : Fin Stage.card → Fin N := hOriginalName Stage
  let c := hPosition k b 0
  have hPositiveTransfer : ∀ x y : Fin Stage.card,
      c+1 ≤ A.freeLevel (name x).val →
      c+1 ≤ A.freeLevel (name y).val →
      A.partialTypeAt c (name x).val = A.partialTypeAt c (name y).val →
      A.L.binary c (name x).val (0 : Fin 1) = true →
      A.L.binary c (name y).val (0 : Fin 1) = true := by
    intro x y hx hy hEq hPositive
    obtain ⟨j,m,hbj,_hgm,hm,hAddr,hEdge⟩ :=
      finiteNumericH_eligible_lower_cut_neighbour_is_higher E k N b 0 hk hCut
        (name x) hx hPositive
    obtain ⟨hRole,hTop⟩ :=
      resolvedQ_stage_omitted_positive_name_is_selected_top
        K k N U J Plan hJPlan role E hQ hRootDummy hPlanShape
        b j m hm hbj hOmitted x hAddr hEdge
    have hXAddr : (name x).val = hPosition k j k := by
      simpa only [hTop] using hAddr
    have hNonDummy : role b ≠ .dummy := by
      intro hD
      have hFalse := hQ.dummy b j hD
      rw [hEdge] at hFalse
      cases hFalse
    obtain ⟨p,hpb,hOldEdge⟩ := hOldNeighbour j hbj hRole hEdge
    obtain ⟨j',m',hbj',hm',hYAddr⟩ :=
      finiteNumericH_eligible_base_zero_has_later_real K k N b (name y) hy
    have hShape := resolvedQ_stage_name_shape_of_planned_levels
      K k N U J Plan hJPlan role hRootDummy hPlanShape y j' m' hm' hYAddr
    have hOldEq : ∀ q : Nat, q < b →
        A.L.binary (hPosition k q 0) (name x).val (0 : Fin 1) =
        A.L.binary (hPosition k q 0) (name y).val (0 : Fin 1) := by
      intro q hq
      exact full_old_type_eq_implies_ordinary_old_bit_eq A c
        (hPosition k q 0) (name x).val (name y).val
        (hPosition_lt_of_block_lt k q b 0 0 (Nat.zero_le k) hq) hEq
    have hXBit : ∀ q : Nat, q < b →
        A.L.binary (hPosition k q 0) (name x).val (0 : Fin 1) = E q j := by
      intro q hq
      change hNumericBinary K.binary k (hPosition k q 0) (name x).val
        (0 : Fin 1) = E q j
      rw [hXAddr]
      exact numericH_older_generation_to_top_exact K.binary k q j 0
        (0 : Fin 1) (hq.trans hbj) (Nat.zero_le k)
    have hYPositive : A.L.binary (hPosition k p 0) (name y).val
        (0 : Fin 1) = true :=
      (hOldEq p hpb).symm.trans ((hXBit p hpb).trans hOldEdge)
    have hNoNeg : E p j' ≠ false := by
      intro hNeg
      have hPhysicalNeg : A.L.binary (hPosition k p 0) (name y).val
          (0 : Fin 1) = false := by
        rw [hYAddr]
        exact finiteNumericH_preserves_original_nonedge K k N p j' 0 m'
          (hpb.trans hbj') (Nat.zero_le k) hm'
          (by intro t; fin_cases t; exact hNeg) (0 : Fin 1)
      rw [hYPositive] at hPhysicalNeg
      cases hPhysicalNeg
    have hYTop : role j' = .coded true ∧ m' = k := by
      rcases hShape with hDummy | hCode | ⟨block,hAux⟩
      · exact False.elim (hNoNeg ((hQ.sym p j').trans (hQ.dummy j' p hDummy)))
      · exact hCode
      · exact False.elim (hNoNeg
          (ResolvedQBlockSeparation.omitted_nondummy_later_retained_aux_old_column_zero
            role E hQ hBlockInterval b j' block hbj' hOmitted hNonDummy hAux p hpb))
    have hYTopAddr : (name y).val = hPosition k j' k := by
      simpa only [hYTop.2] using hYAddr
    have hYBit : ∀ q : Nat, q < b →
        A.L.binary (hPosition k q 0) (name y).val (0 : Fin 1) = E q j' := by
      intro q hq
      change hNumericBinary K.binary k (hPosition k q 0) (name y).val
        (0 : Fin 1) = E q j'
      rw [hYTopAddr]
      exact numericH_older_generation_to_top_exact K.binary k q j' 0
        (0 : Fin 1) (hq.trans hbj') (Nat.zero_le k)
    have hBaseEq : ∀ q : Nat, q < b → E q j = E q j' := by
      intro q hq
      exact (hXBit q hq).symm.trans ((hOldEq q hq).trans (hYBit q hq))
    have hYEdge : E b j' = true :=
      (hNoSplit j j' hbj hbj' hRole hYTop.1 hBaseEq).symm.trans hEdge
    change hNumericBinary K.binary k (hPosition k b 0) (name y).val
      (0 : Fin 1) = true
    rw [hYTopAddr]
    apply (hNumericBinary_real_forward_iff K.binary k b j' 0 k
      (0 : Fin 1) hbj' (Nat.zero_le k) (Nat.le_refl k)).2
    exact ⟨Or.inl hk,hYEdge⟩
  have hCutBit : A.L.binary c (name v).val (0 : Fin 1) =
      A.L.binary c (name w).val (0 : Fin 1) := by
    cases hV : A.L.binary c (name v).val (0 : Fin 1) with
    | false =>
      cases hW : A.L.binary c (name w).val (0 : Fin 1) with
      | false => rfl
      | true =>
        have hBad := hPositiveTransfer w v hFreeW hFreeV hOld.symm hW
        rw [hV] at hBad
        cases hBad
    | true => exact (hPositiveTransfer v w hFreeV hFreeW hOld hV).symm
  have hSymA : ∀ i j : Nat, A.L.binary i j (0 : Fin 1) =
      A.L.binary j i (0 : Fin 1) :=
    finiteNumericH_graph_ordinary_L_symmetric E hQ.sym k N
  exact full_equal_ordinary_cut_column_determines_next_type
    A hSymA c (name v) (name w) hFreeV hFreeW hCutBit hOld

end Kk
