import Kk.FiniteCliqueIntegerWitness
import Kk.FiniteCliqueSupportWitness
import Mathlib.Tactic

/-!
# Track A: exact finite old-to-future reference age from clique capacities

English proof and hostile audit committed FIRST:
  docs/finite_old_column_reference_age_english_audit.md

For a finite old graph P and a full typed old-column assignment c,
the abstract continuation age of EVERY finite labelled graph W is
determined by exact clique capacities in common old neighbourhoods.
This yields raw bounds B(T) and, using the already verified joint
canonicalization lemma, the SAME age constraints for G_B.

No physical unbounded resolved-copy schedule, auxiliary Kpt E/B3, or
common labelled source is asserted. The old and future pools are
disjoint and BOTH old/future directed L columns are explicitly fixed.
-/

namespace Kk

/-- Common original old neighbours of *every* sort in T.
No assumption that this set is a clique: its actual graph clique
capacity, rather than cardinality, determines the age bound. -/
noncomputable def oldSupportCommonNeighbourPool {d : Nat}
    (P : Finset Nat) (c : Nat → Fin d → Bool)
    (T : Finset (Fin d)) : Finset Nat := by
  classical
  exact P.filter (fun p => ∀ t ∈ T, c p t = true)

/-- Raw finite continuation bound for any nonempty admissible support:
maximum size ell-1 minus the actual clique capacity of the common
old neighbours to ALL sorts in that support simultaneously. -/
noncomputable def finiteOldColumnRawBound
    (E : Nat → Nat → Bool) (ell d : Nat)
    (P : Finset Nat) (c : Nat → Fin d → Bool)
    (T : IntegerGraphSupport d ell) : Nat :=
  ell - 1 -
    finiteDirectedCliqueCapacity E (oldSupportCommonNeighbourPool P c T.1)

/-- Full old-plus-future K_ell-freeness forces every normalized support
multiplicity bound, even for an arbitrary finite future W with repeated
sort labels. The old clique capacity is attained, and complete
two-direction crossing columns make the joined clique literal. -/
theorem finiteOldFuture_free_implies_raw_support
    (E : Nat → Nat → Bool) (ell d : Nat)
    (P W : Finset Nat) (sort : Nat → Fin d)
    (c : Nat → Fin d → Bool)
    (hDisjoint : Disjoint P W)
    (hColumns : ∀ p ∈ P, ∀ w ∈ W,
      E p w = c p (sort w) ∧ E w p = c p (sort w))
    (hFree : finitePoolCliqueCheck E ell (P ∪ W) = false) :
    ∀ s : Finset Nat, s ⊆ W → IsDirectedCliqueOn E s →
      ∀ T : IntegerGraphSupport d ell,
        (s.filter (fun w => sort w ∈ T.1)).card ≤
          finiteOldColumnRawBound E ell d P c T := by
  classical
  intro s hsW hsClique T
  let U : Finset Nat := oldSupportCommonNeighbourPool P c T.1
  let V : Finset Nat := s.filter (fun w => sort w ∈ T.1)
  obtain ⟨r, hrU, hrClique, hrCard⟩ :=
    finiteDirectedCliqueCapacity_attained E U
  have hUsubP : U ⊆ P := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hrP : r ⊆ P := hrU.trans hUsubP
  have hVsubW : V ⊆ W := by
    intro w hw
    exact hsW (Finset.mem_filter.mp hw).1
  have hVClique : IsDirectedCliqueOn E V := by
    intro x hx y hy hxy
    exact hsClique x (Finset.mem_filter.mp hx).1
      y (Finset.mem_filter.mp hy).1 hxy
  have hRVDisjoint : Disjoint r V := by
    apply Finset.disjoint_left.mpr
    intro x hx hr
    exact (Finset.disjoint_left.mp hDisjoint) (hrP hx) (hVsubW hr)
  have hJoinClique : IsDirectedCliqueOn E (r ∪ V) := by
    intro x hx y hy hxy
    rcases Finset.mem_union.mp hx with hxR | hxV
    · rcases Finset.mem_union.mp hy with hyR | hyV
      · exact hrClique x hxR y hyR hxy
      · have hMem : x ∈ U := hrU hxR
        have hBit : c x (sort y) = true := by
          have hAll := (Finset.mem_filter.mp hMem).2
          exact hAll (sort y) (Finset.mem_filter.mp hyV).2
        exact (hColumns x (hrP hxR) y (hVsubW hyV)).1.trans hBit
    · rcases Finset.mem_union.mp hy with hyR | hyV
      · have hMem : y ∈ U := hrU hyR
        have hBit : c y (sort x) = true := by
          have hAll := (Finset.mem_filter.mp hMem).2
          exact hAll (sort x) (Finset.mem_filter.mp hxV).2
        exact (hColumns y (hrP hyR) x (hVsubW hxV)).2.trans hBit
      · exact hVClique x hxV y hyV hxy
  have hJoinSub : r ∪ V ⊆ P ∪ W := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxR | hxV
    · exact Finset.mem_union.mpr (Or.inl (hrP hxR))
    · exact Finset.mem_union.mpr (Or.inr (hVsubW hxV))
  have hCardUnion : (r ∪ V).card = r.card + V.card :=
    Finset.card_union_of_disjoint hRVDisjoint
  have hBound := directedClique_card_le_capacity
    E (P ∪ W) (r ∪ V) hJoinSub hJoinClique
  have hFreeBound :=
    (finitePoolCliqueCheck_false_iff_capacity_lt E ell (P ∪ W)).mp hFree
  change V.card ≤ ell - 1 - finiteDirectedCliqueCapacity E U
  omega

/-- Conversely, if the old P and future W are individually free and
every realized W-clique meets the raw all-support bounds, no forbidden
clique can straddle P and W. This proves the missing *completeness*
of the old-column reference capacity description. -/
theorem finiteOldFuture_free_of_all_raw_support
    (E : Nat → Nat → Bool) (ell d : Nat)
    (P W : Finset Nat) (sort : Nat → Fin d)
    (c : Nat → Fin d → Bool)
    (hDisjoint : Disjoint P W)
    (hColumns : ∀ p ∈ P, ∀ w ∈ W,
      E p w = c p (sort w) ∧ E w p = c p (sort w))
    (hPFree : finitePoolCliqueCheck E ell P = false)
    (hWFree : finitePoolCliqueCheck E ell W = false)
    (hBounds : ∀ s : Finset Nat, s ⊆ W → IsDirectedCliqueOn E s →
      ∀ T : IntegerGraphSupport d ell,
        (s.filter (fun w => sort w ∈ T.1)).card ≤
          finiteOldColumnRawBound E ell d P c T) :
    finitePoolCliqueCheck E ell (P ∪ W) = false := by
  classical
  apply (finitePoolCliqueCheck_false_iff E ell (P ∪ W)).2
  rintro ⟨H, hHSub, hHCard, hHClique⟩
  let X : Finset Nat := H ∩ P
  let Y : Finset Nat := H ∩ W
  have hXSub : X ⊆ P := Finset.inter_subset_right
  have hYSub : Y ⊆ W := Finset.inter_subset_right
  have hXClique : IsDirectedCliqueOn E X := by
    intro x hx y hy hxy
    exact hHClique x (Finset.mem_inter.mp hx).1
      y (Finset.mem_inter.mp hy).1 hxy
  have hYClique : IsDirectedCliqueOn E Y := by
    intro x hx y hy hxy
    exact hHClique x (Finset.mem_inter.mp hx).1
      y (Finset.mem_inter.mp hy).1 hxy
  have hYNonempty : Y.Nonempty := by
    by_contra hNo
    have hEmpty : Y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hNo
    have hHSubP : H ⊆ P := by
      intro z hz
      rcases Finset.mem_union.mp (hHSub hz) with hPz | hWz
      · exact hPz
      · have hYz : z ∈ Y := Finset.mem_inter.mpr ⟨hz, hWz⟩
        rw [hEmpty] at hYz
        exact False.elim ((Finset.not_mem_empty z) hYz)
    exact ((finitePoolCliqueCheck_false_iff E ell P).mp hPFree)
      ⟨H, hHSubP, hHCard, hHClique⟩
  have hYSmall : Y.card < ell :=
    finiteClique_card_lt_of_pool_cliqueFree E ell W Y
      hWFree hYSub hYClique
  let Tset : Finset (Fin d) := Y.image sort
  have hTNonempty : Tset.Nonempty := by
    obtain ⟨w, hw⟩ := hYNonempty
    exact ⟨sort w, Finset.mem_image.mpr ⟨w, hw, rfl⟩⟩
  have hTCard : Tset.card ≤ ell - 1 := by
    have hImageBound : Tset.card ≤ Y.card := Finset.card_image_le
    omega
  let T : IntegerGraphSupport d ell := ⟨Tset, hTNonempty, hTCard⟩
  have hYFilter : Y.filter (fun w => sort w ∈ T.1) = Y := by
    apply Finset.filter_eq_self.mpr
    intro w hw
    exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
  have hXCommon : X ⊆ oldSupportCommonNeighbourPool P c T.1 := by
    intro x hx
    change x ∈ P.filter (fun p => ∀ t ∈ T.1, c p t = true)
    apply Finset.mem_filter.mpr
    refine ⟨hXSub hx, ?_⟩
    intro t ht
    obtain ⟨w, hwY, hSort⟩ := Finset.mem_image.mp ht
    have hWw : w ∈ W := hYSub hwY
    have hXx : x ∈ H := (Finset.mem_inter.mp hx).1
    have hHw : w ∈ H := (Finset.mem_inter.mp hwY).1
    have hDifferent : x ≠ w := by
      intro hEq
      have hxW : x ∈ W := hEq.symm ▸ hWw
      exact (Finset.disjoint_left.mp hDisjoint) (hXSub hx) hxW
    have hEdge : E x w = true := hHClique x hXx w hHw hDifferent
    have hCol : E x w = c x (sort w) :=
      (hColumns x (hXSub hx) w hWw).1
    have hC : c x (sort w) = true := hCol.symm.trans hEdge
    simpa only [hSort] using hC
  have hXCapacity : X.card ≤
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool P c T.1) :=
    directedClique_card_le_capacity E
      (oldSupportCommonNeighbourPool P c T.1) X hXCommon hXClique
  have hXYDisjoint : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro z hzX hzY
    exact (Finset.disjoint_left.mp hDisjoint)
      (hXSub hzX) (hYSub hzY)
  have hSplit : H = X ∪ Y := by
    apply Finset.Subset.antisymm
    · intro z hz
      rcases Finset.mem_union.mp (hHSub hz) with hzP | hzW
      · exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_inter.mpr ⟨hz, hzP⟩))
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_inter.mpr ⟨hz, hzW⟩))
    · intro z hz
      rcases Finset.mem_union.mp hz with hzX | hzY
      · exact (Finset.mem_inter.mp hzX).1
      · exact (Finset.mem_inter.mp hzY).1
  have hSplitCard : H.card = X.card + Y.card := by
    rw [hSplit, Finset.card_union_of_disjoint hXYDisjoint]
  have hRawBound := hBounds Y hYSub hYClique T
  rw [hYFilter] at hRawBound
  change Y.card ≤ ell - 1 -
    finiteDirectedCliqueCapacity E
      (oldSupportCommonNeighbourPool P c T.1) at hRawBound
  omega

/-- EXACT full finite reference-age equivalence with the raw B(T)
computed from every common old-neighbour clique capacity. This works
for any arbitrary finite future edge pattern W and is not restricted
to one chosen selected top original. -/
theorem finiteOldFuture_free_iff_raw_support
    (E : Nat → Nat → Bool) (ell d : Nat)
    (P W : Finset Nat) (sort : Nat → Fin d)
    (c : Nat → Fin d → Bool)
    (hDisjoint : Disjoint P W)
    (hColumns : ∀ p ∈ P, ∀ w ∈ W,
      E p w = c p (sort w) ∧ E w p = c p (sort w))
    (hPFree : finitePoolCliqueCheck E ell P = false) :
    finitePoolCliqueCheck E ell (P ∪ W) = false ↔
      finitePoolCliqueCheck E ell W = false ∧
      (∀ s : Finset Nat, s ⊆ W → IsDirectedCliqueOn E s →
        ∀ T : IntegerGraphSupport d ell,
          (s.filter (fun w => sort w ∈ T.1)).card ≤
            finiteOldColumnRawBound E ell d P c T) := by
  constructor
  · intro hFree
    exact ⟨finitePoolCliqueCheck_oldFuture_implies_future_false
      E ell P W hFree,
      finiteOldFuture_free_implies_raw_support E ell d P W sort c
        hDisjoint hColumns hFree⟩
  · rintro ⟨hWFree, hBounds⟩
    exact finiteOldFuture_free_of_all_raw_support E ell d P W
      sort c hDisjoint hColumns hPFree hWFree hBounds

/-- SAME exact old-plus-future criterion using the verified
integer-witness canonicalizer G_B of the actual raw clique capacities.
No false pointwise equality B=G_B is asserted, and G_B is a genuinely
positive graph age only with additional verified eligibility data. -/
theorem finiteOldFuture_free_iff_canonical_support
    (E : Nat → Nat → Bool) (ell d : Nat)
    (P W : Finset Nat) (sort : Nat → Fin d)
    (c : Nat → Fin d → Bool)
    (hDisjoint : Disjoint P W)
    (hColumns : ∀ p ∈ P, ∀ w ∈ W,
      E p w = c p (sort w) ∧ E w p = c p (sort w))
    (hPFree : finitePoolCliqueCheck E ell P = false) :
    finitePoolCliqueCheck E ell (P ∪ W) = false ↔
      finitePoolCliqueCheck E ell W = false ∧
      (∀ s : Finset Nat, s ⊆ W → IsDirectedCliqueOn E s →
        ∀ T : IntegerGraphSupport d ell,
          (s.filter (fun w => sort w ∈ T.1)).card ≤
            integerGraphAgeCanonical d ell
              (finiteOldColumnRawBound E ell d P c) T) := by
  have hRaw := finiteOldFuture_free_iff_raw_support
    E ell d P W sort c hDisjoint hColumns hPFree
  constructor
  · intro hFree
    obtain ⟨hWFree, hBounds⟩ := hRaw.mp hFree
    have hCanon := finiteClique_all_constraints_integerCanonical_iff
      E W sort (finiteOldColumnRawBound E ell d P c) hWFree
    exact ⟨hWFree, hCanon.mpr hBounds⟩
  · rintro ⟨hWFree, hBounds⟩
    have hCanon := finiteClique_all_constraints_integerCanonical_iff
      E W sort (finiteOldColumnRawBound E ell d P c) hWFree
    exact hRaw.mpr ⟨hWFree, hCanon.mp hBounds⟩

#print axioms Kk.finiteOldFuture_free_implies_raw_support
#print axioms Kk.finiteOldFuture_free_of_all_raw_support
#print axioms Kk.finiteOldFuture_free_iff_raw_support
#print axioms Kk.finiteOldFuture_free_iff_canonical_support

end Kk
