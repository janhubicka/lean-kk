import Kk.PositiveGenerationStageCoherence
import Kk.ResolvedQBlockSeparation
import Kk.K4SingletonOldNeighbour
import Kk.NumericHTopAuxE
import Mathlib.Tactic

/-!
# Generation-zero whole-stage coherence from actual K4 singleton neutrality

English proof and independent review precede this source in
`docs/generation_zero_stage_coherence_english_20261124.md` and
`docs/audits/2026-11-24-generation-zero-coherence-independent-review.md`.

The singleton capacity is computed from every actual old Q base. Its
neutrality supplies a real old positive witness; that witness separates
positive selected TOPs from dummy roots and retained auxiliary originals.
A separate ordinary selected no-split property handles selected-selected
comparisons. Both construction properties are explicit, rather than an
assumed physical coherence or structural exclusion. The theorem quantifies
over the entire eligible stage, not just a marked B3 source.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The actual one-sort K4 canonical singleton capacity over ALL base
originals below b, with the literal old adjacency column into j. -/
noncomputable def resolvedQK4SingletonCapacity
    (E : Nat → Nat → Bool) (b j : Nat) : Nat :=
  integerGraphAgeCanonical 1 4
    (finiteOldColumnRawBound E 4 1 (Finset.range b)
      (fun p (_ : Fin 1) => E p j))
    (trackFSingletonSupport 1 4 (0 : Fin 1) (by decide))

/-- No new split of selected future complete ordinary base profiles.
This is an ordinary-Q construction property, not full physical coherence. -/
def ResolvedQSelectedNoSplitAt
    (role : Nat → ResolvedQBaseRole)
    (E : Nat → Nat → Bool) (b : Nat) : Prop :=
  ∀ j j' : Nat, b < j → b < j' →
    role j = .coded true → role j' = .coded true →
    (∀ p : Nat, p < b → E p j = E p j') → E b j = E b j'

/-- Neutrality of each selected future singleton's ACTUAL K4 finite
old-column canonical capacity when the one base b is added. -/
def ResolvedQK4SingletonNeutralAt
    (role : Nat → ResolvedQBaseRole)
    (E : Nat → Nat → Bool) (b : Nat) : Prop :=
  ∀ j : Nat, b < j → role j = .coded true →
    resolvedQK4SingletonCapacity E b j =
      resolvedQK4SingletonCapacity E (b+1) j

/-- A new positive bit with unchanged actual canonical singleton capacity
has a genuinely old positive base witness. No stipulated age label, graph
avoidance, or external old-neighbour assumption is used. -/
theorem resolvedQK4_singleton_neutral_positive_has_old_neighbour
    (E : Nat → Nat → Bool) (b j : Nat)
    (hNeutral : resolvedQK4SingletonCapacity E b j =
      resolvedQK4SingletonCapacity E (b+1) j)
    (hPositive : E b j = true) :
    ∃ p : Nat, p < b ∧ E p j = true := by
  have hAfter : resolvedQK4SingletonCapacity E (b+1) j ≤ 2 := by
    unfold resolvedQK4SingletonCapacity
    apply (k4_canonical_singleton_le_two_iff_old_neighbour
      E 1 (Finset.range (b+1)) (fun p (_ : Fin 1) => E p j)
      (0 : Fin 1)).2
    exact ⟨b, Finset.mem_range.mpr (by omega), hPositive⟩
  have hBefore : resolvedQK4SingletonCapacity E b j ≤ 2 := by
    rw [hNeutral]
    exact hAfter
  unfold resolvedQK4SingletonCapacity at hBefore
  obtain ⟨p,hp,hBit⟩ :=
    (k4_canonical_singleton_le_two_iff_old_neighbour
      E 1 (Finset.range b) (fun p (_ : Fin 1) => E p j)
      (0 : Fin 1)).1 hBefore
  exact ⟨p, Finset.mem_range.mp hp, hBit⟩

/-- Complete old-type equality determines the ordinary generation-zero
cut bit on EVERY eligible original of the physical stage, from the exact
ordinary-Q no-split and K4 singleton-neutrality construction properties.
The old witness is derived, and no no-I1/no-I2 condition is assumed. -/
theorem resolvedQ_zero_generation_stage_cut_bit_eq
    (E : Nat → Nat → Bool)
    (k N : Nat) (hk : 0 < k) (U : Finset (Fin N))
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
    (hBlockInterval :
      ∀ p b j block : Nat, ∀ pastFlag futureFlag : Bool,
        p < b → b < j →
        role p = .auxiliary block pastFlag →
        role j = .auxiliary block futureFlag →
        role b = .dummy ∨
          ∃ middleFlag : Bool, role b = .auxiliary block middleFlag)
    (b : Nat) (hCut : hPosition k b 0 < N)
    (hOmitted : ResolvedQOmittedBase (role b))
    (hNonDummy : role b ≠ .dummy)
    (hNoSplit : ResolvedQSelectedNoSplitAt role E b)
    (hNeutral : ResolvedQK4SingletonNeutralAt role E b)
    (v w : Fin (hStageOriginals (normalizedGraphModel E) k N U J).card)
    (hFreeV : hPosition k b 0 + 1 ≤
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel
        (hOriginalName
          (hStageOriginals (normalizedGraphModel E) k N U J) v).val)
    (hFreeW : hPosition k b 0 + 1 ≤
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel
        (hOriginalName
          (hStageOriginals (normalizedGraphModel E) k N U J) w).val)
    (hOld :
      (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
        (hPosition k b 0)
        (hOriginalName
          (hStageOriginals (normalizedGraphModel E) k N U J) v).val =
      (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
        (hPosition k b 0)
        (hOriginalName
          (hStageOriginals (normalizedGraphModel E) k N U J) w).val) :
    (finiteNumericH (normalizedGraphModel E) k N).L.binary
        (hPosition k b 0)
        (hOriginalName
          (hStageOriginals (normalizedGraphModel E) k N U J) v).val
        (0 : Fin 1) =
      (finiteNumericH (normalizedGraphModel E) k N).L.binary
        (hPosition k b 0)
        (hOriginalName
          (hStageOriginals (normalizedGraphModel E) k N U J) w).val
        (0 : Fin 1) := by
  let K : AgeTestModel 1 0 1 := normalizedGraphModel E
  let A : EnumeratedPartialStructure 1 0 1 := finiteNumericH K k N
  let Stage : Finset (Fin N) := hStageOriginals K k N U J
  let name : Fin Stage.card → Fin N := hOriginalName Stage
  let cut : Nat := hPosition k b 0
  have hTopBit : ∀ q j : Nat, q < j →
      A.L.binary (hPosition k q 0) (hPosition k j k) (0 : Fin 1) =
        E q j := by
    intro q j hqj
    change hNumericBinary K.binary k
      (hPosition k q 0) (hPosition k j k) (0 : Fin 1) =
        K.binary q j (0 : Fin 1)
    exact numericH_older_generation_to_top_exact
      K.binary k q j 0 (0 : Fin 1) hqj (Nat.zero_le k)
  have hTransport : ∀ x y : Fin Stage.card,
      cut+1 ≤ A.freeLevel (name x).val →
      cut+1 ≤ A.freeLevel (name y).val →
      A.partialTypeAt cut (name x).val =
        A.partialTypeAt cut (name y).val →
      A.L.binary cut (name x).val (0 : Fin 1) = true →
      A.L.binary cut (name y).val (0 : Fin 1) = true := by
    intro x y hFreeX hFreeY hOldXY hPositiveX
    have hOldBits : ∀ old : Nat, old < cut →
        A.L.binary old (name x).val (0 : Fin 1) =
          A.L.binary old (name y).val (0 : Fin 1) := by
      intro old hOldCut
      have hReduct :
          (A.partialTypeAt cut (name x).val).lReduct =
            (A.partialTypeAt cut (name y).val).lReduct :=
        congrArg (fun T : PartialTypeWithE cut 1 0 1 => T.lReduct) hOldXY
      rw [partialTypeAt_lReduct_eq_ofAgeModel A cut (name x).val,
        partialTypeAt_lReduct_eq_ofAgeModel A cut (name y).val] at hReduct
      have hBit := congrArg
        (fun T : RelationalPrefixType cut 1 0 1 =>
          T.binary (some (⟨old,hOldCut⟩ : Fin cut)) none (0 : Fin 1)) hReduct
      exact hBit
    obtain ⟨j,m,hbj,_hgm,hm,hAddrX,hEdgeX⟩ :=
      finiteNumericH_eligible_lower_cut_neighbour_is_higher
        E k N b 0 hk hCut (name x) hFreeX hPositiveX
    obtain ⟨hCodeX,hTopX⟩ :=
      resolvedQ_stage_omitted_positive_name_is_selected_top
        K k N U J Plan hJPlan role E hQ hRootDummy hPlanShape
        b j m hm hbj hOmitted x hAddrX hEdgeX
    have hTopAddrX : (name x).val = hPosition k j k := by
      simpa only [hTopX] using hAddrX
    obtain ⟨p,hpb,hPj⟩ :=
      resolvedQK4_singleton_neutral_positive_has_old_neighbour
        E b j (hNeutral j hbj hCodeX) hEdgeX
    have hOldCoord : hPosition k p 0 < cut :=
      hPosition_lt_of_block_lt k p b 0 0 (Nat.zero_le k) hpb
    have hOldInside : hPosition k p 0 < N := lt_trans hOldCoord hCut
    have hOldPositiveX :
        A.L.binary (hPosition k p 0) (name x).val (0 : Fin 1) = true := by
      rw [hTopAddrX, hTopBit p j (lt_trans hpb hbj)]
      exact hPj
    have hOldPositiveY :
        A.L.binary (hPosition k p 0) (name y).val (0 : Fin 1) = true :=
      (hOldBits (hPosition k p 0) hOldCoord).symm.trans hOldPositiveX
    have hOldFreeY : hPosition k p 0 + 1 ≤ A.freeLevel (name y).val := by
      omega
    obtain ⟨j',m',hpj',_hgm',hm',hAddrY,hEdgeY⟩ :=
      finiteNumericH_eligible_lower_cut_neighbour_is_higher
        E k N p 0 hk hOldInside (name y) hOldFreeY hOldPositiveY
    have hShapeY := resolvedQ_stage_name_shape_of_planned_levels
      K k N U J Plan hJPlan role hRootDummy hPlanShape y j' m' hm' hAddrY
    have hAfter : hPosition k b 0 < (name y).val := by
      have hBound := A.freeLevel_le (name y).val
      change hPosition k b 0 + 1 ≤ A.freeLevel (name y).val at hFreeY
      omega
    rcases hShapeY with hDummyY | hCodedY | ⟨block,hAuxY⟩
    · have hZero : E p j' = false :=
        (hQ.sym p j').trans (hQ.dummy j' p hDummyY)
      rw [hZero] at hEdgeY
      cases hEdgeY
    · have hTopAddrY : (name y).val = hPosition k j' k := by
        simpa only [hCodedY.2] using hAddrY
      have hj'Positive : 0 < j' := by omega
      have hTopInside : hPosition k j' k < N := by
        rw [← hTopAddrY]
        exact (name y).isLt
      have hTopFree : A.freeLevel (name y).val =
          hPosition k (j'-1) k + 1 := by
        rw [hTopAddrY]
        exact finiteNumericH_top_freeLevel_exact K k N j' hk hj'Positive hTopInside
      have hbj' : b < j' := by
        by_contra hNotLater
        have hPrev : j'-1 < b := by omega
        have hPreviousBefore :=
          hPosition_lt_of_block_lt k (j'-1) b k 0 (Nat.le_refl k) hPrev
        rw [hTopFree] at hFreeY
        change hPosition k b 0 + 1 ≤ hPosition k (j'-1) k + 1 at hFreeY
        omega
      have hProfiles : ∀ q : Nat, q < b → E q j = E q j' := by
        intro q hqb
        have hCoordinate : hPosition k q 0 < cut :=
          hPosition_lt_of_block_lt k q b 0 0 (Nat.zero_le k) hqb
        have hBits := hOldBits (hPosition k q 0) hCoordinate
        rw [hTopAddrX, hTopAddrY,
          hTopBit q j (lt_trans hqb hbj),
          hTopBit q j' (lt_trans hqb hbj')] at hBits
        exact hBits
      have hNewEqual : E b j = E b j' :=
        hNoSplit j j' hbj hbj' hCodeX hCodedY.1 hProfiles
      change A.L.binary (hPosition k b 0) (name y).val (0 : Fin 1) = true
      rw [hTopAddrY, hTopBit b j' hbj']
      exact hNewEqual.symm.trans hEdgeX
    · have hbLe : b ≤ j' := by
        by_contra hNotLe
        have hj'b : j' < b := by omega
        have hBefore :=
          hPosition_lt_of_block_lt k j' b m' 0 hm' hj'b
        rw [hAddrY] at hAfter
        omega
      have hNe : j' ≠ b := by
        intro hEq
        have hAuxB : role b = .auxiliary block true := by
          simpa only [hEq] using hAuxY
        rw [hAuxB] at hOmitted
        simp [ResolvedQOmittedBase] at hOmitted
      have hbj' : b < j' := by omega
      have hZero :=
        ResolvedQBlockSeparation.omitted_nondummy_later_retained_aux_old_column_zero
          role E hQ hBlockInterval b j' block hbj' hOmitted hNonDummy hAuxY p hpb
      rw [hZero] at hEdgeY
      cases hEdgeY
  change A.L.binary cut (name v).val (0 : Fin 1) =
    A.L.binary cut (name w).val (0 : Fin 1)
  cases hV : A.L.binary cut (name v).val (0 : Fin 1) with
  | false =>
    cases hW : A.L.binary cut (name w).val (0 : Fin 1) with
    | false => rfl
    | true =>
      have hImpossible := hTransport w v hFreeW hFreeV hOld.symm hW
      rw [hV] at hImpossible
      cases hImpossible
  | true =>
    exact (hTransport v w hFreeV hFreeW hOld hV).symm

/-- Complete whole-stage old-to-next L+/E coherence at an omitted
non-dummy generation-zero cut, derived from actual K4 singleton neutrality
and selected ordinary no-split. The complete closure structural lift can
be applied afterward; neither structural verdict is an input here. -/
theorem resolvedQ_zero_generation_stage_full_type_coherent
    (E : Nat → Nat → Bool)
    (k N : Nat) (hk : 0 < k) (U : Finset (Fin N))
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
    (hBlockInterval :
      ∀ p b j block : Nat, ∀ pastFlag futureFlag : Bool,
        p < b → b < j →
        role p = .auxiliary block pastFlag →
        role j = .auxiliary block futureFlag →
        role b = .dummy ∨
          ∃ middleFlag : Bool, role b = .auxiliary block middleFlag)
    (b : Nat) (hCut : hPosition k b 0 < N)
    (hOmitted : ResolvedQOmittedBase (role b))
    (hNonDummy : role b ≠ .dummy)
    (hNoSplit : ResolvedQSelectedNoSplitAt role E b)
    (hNeutral : ResolvedQK4SingletonNeutralAt role E b)
    (v w : Fin (hStageOriginals (normalizedGraphModel E) k N U J).card)
    (hFreeV : hPosition k b 0 + 1 ≤
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel
        (hOriginalName
          (hStageOriginals (normalizedGraphModel E) k N U J) v).val)
    (hFreeW : hPosition k b 0 + 1 ≤
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel
        (hOriginalName
          (hStageOriginals (normalizedGraphModel E) k N U J) w).val)
    (hOld :
      (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
        (hPosition k b 0)
        (hOriginalName
          (hStageOriginals (normalizedGraphModel E) k N U J) v).val =
      (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
        (hPosition k b 0)
        (hOriginalName
          (hStageOriginals (normalizedGraphModel E) k N U J) w).val) :
    (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
        (hPosition k b 0 + 1)
        (hOriginalName
          (hStageOriginals (normalizedGraphModel E) k N U J) v).val =
      (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
        (hPosition k b 0 + 1)
        (hOriginalName
          (hStageOriginals (normalizedGraphModel E) k N U J) w).val := by
  let A := finiteNumericH (normalizedGraphModel E) k N
  let name := hOriginalName (hStageOriginals (normalizedGraphModel E) k N U J)
  have hCutBits := resolvedQ_zero_generation_stage_cut_bit_eq
    E k N hk U J Plan hJPlan role hQ hRootDummy hPlanShape hBlockInterval
    b hCut hOmitted hNonDummy hNoSplit hNeutral v w hFreeV hFreeW hOld
  have hSymA : ∀ i j : Nat,
      A.L.binary i j (0 : Fin 1) = A.L.binary j i (0 : Fin 1) :=
    finiteNumericH_graph_ordinary_L_symmetric E hQ.sym k N
  exact full_equal_ordinary_cut_column_determines_next_type
    A hSymA (hPosition k b 0) (name v) (name w) hFreeV hFreeW hCutBits hOld

#print axioms Kk.resolvedQK4_singleton_neutral_positive_has_old_neighbour
#print axioms Kk.resolvedQ_zero_generation_stage_cut_bit_eq
#print axioms Kk.resolvedQ_zero_generation_stage_full_type_coherent

end Kk
