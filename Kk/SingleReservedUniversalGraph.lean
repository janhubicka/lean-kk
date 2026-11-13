import Kk.UniversalFutureDisjointCliques
import Kk.RawSupportBlockBudget
import Mathlib.Tactic

/-!
# Actual one-reserved-support-block plus universal-future finite L graph

English proof and hostile mathematical audit committed FIRST:
  docs/single_reserved_universal_graph_english_audit.md

The finite carrier is a tagged disjoint union of a genuine complete
reserved clique of size ell-1-B(T) (Nat truncated) and the ACTUAL
feasible universal future W_B from PR #86. Every reserved/future
L atom is the exact two-direction support indicator. No clique of
cardinality ell exists in the constructed carrier.

This does NOT claim a compatible embedding over a fixed old Henson
prefix, auxiliary H+ Kpt E records, complete B3 or labelled orbit.
-/

namespace Kk

/-- Reserved block coordinates and all possible typed future coordinates;
the designated finite carrier selects ONLY the feasible future ones. -/
abbrev SingleReservedFutureVertex (d ell : Nat)
    (B : IntegerGraphSupport d ell → Nat)
    (T : IntegerGraphSupport d ell) :=
  Sum (Fin (ell-1-B T)) (UniversalWitnessVertex d ell)

/-- The actually used finite carrier includes the complete reserved
block and precisely the B-feasible universal future. -/
noncomputable def singleReservedFutureCarrier
    (d ell : Nat) (B : IntegerGraphSupport d ell → Nat)
    (T : IntegerGraphSupport d ell) :
    Finset (SingleReservedFutureVertex d ell B T) := by
  classical
  exact ((Finset.univ : Finset (Fin (ell-1-B T))).image Sum.inl) ∪
    (universalWitnessFuture d ell B).image Sum.inr

/-- Literal Boolean ordinary-L table. Both mixed directions are
equal to the exact support bit; distinct reserved vertices form a
clique, and future vertices use their genuine universal L graph. -/
def singleReservedFutureEdge {d ell : Nat}
    {B : IntegerGraphSupport d ell → Nat}
    (T : IntegerGraphSupport d ell)
    (x y : SingleReservedFutureVertex d ell B T) : Bool :=
  match x,y with
  | Sum.inl q, Sum.inl p => decide (q ≠ p)
  | Sum.inl _, Sum.inr v => decide (v.2.1 ∈ T.1)
  | Sum.inr v, Sum.inl _ => decide (v.2.1 ∈ T.1)
  | Sum.inr v, Sum.inr w => universalWitnessEdge v w

/-- Directed clique in the literal tagged finite graph. -/
def IsSingleReservedFutureClique {d ell : Nat}
    {B : IntegerGraphSupport d ell → Nat}
    (T : IntegerGraphSupport d ell)
    (s : Finset (SingleReservedFutureVertex d ell B T)) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
    singleReservedFutureEdge T x y = true

theorem singleReservedFutureEdge_symmetric {d ell : Nat}
    {B : IntegerGraphSupport d ell → Nat}
    (T : IntegerGraphSupport d ell)
    (x y : SingleReservedFutureVertex d ell B T) :
    singleReservedFutureEdge T x y =
      singleReservedFutureEdge T y x := by
  cases x with
  | inl q =>
    cases y with
    | inl p => simp [singleReservedFutureEdge, ne_comm]
    | inr v => rfl
  | inr v =>
    cases y with
    | inl q => rfl
    | inr w => exact universalWitnessEdge_symmetric v w

theorem singleReservedFutureEdge_irreflexive {d ell : Nat}
    {B : IntegerGraphSupport d ell → Nat}
    (T : IntegerGraphSupport d ell)
    (x : SingleReservedFutureVertex d ell B T) :
    singleReservedFutureEdge T x x = false := by
  cases x with
  | inl q => simp [singleReservedFutureEdge]
  | inr v => exact universalWitnessEdge_irreflexive v

/-- EVERY directed clique in the explicitly constructed finite
carrier has <ell vertices. This is a proof of real K_ell-freeness
of an actual tagged Boolean-L graph, not a conditional age profile.

The crucial cases are: no reserved vertex, or at least one reserved
vertex forcing all future clique vertices to have sorts in T.
Truncated subtraction is handled by the exact raw-block budget. -/
theorem singleReservedFuture_no_forbidden_clique
    (d ell : Nat) (hell : 0 < ell)
    (B : IntegerGraphSupport d ell → Nat)
    (T : IntegerGraphSupport d ell)
    (s : Finset (SingleReservedFutureVertex d ell B T))
    (hSub : s ⊆ singleReservedFutureCarrier d ell B T)
    (hClique : IsSingleReservedFutureClique T s) :
    s.card < ell := by
  classical
  let Qs : Finset (Fin (ell-1-B T)) :=
    Finset.univ.filter
      (fun q => (Sum.inl q : SingleReservedFutureVertex d ell B T) ∈ s)
  let Ws : Finset (UniversalWitnessVertex d ell) :=
    (universalWitnessFuture d ell B).filter
      (fun v => (Sum.inr v : SingleReservedFutureVertex d ell B T) ∈ s)
  have hWsSub : Ws ⊆ universalWitnessFuture d ell B :=
    Finset.filter_subset _ _
  have hWsClique : IsUniversalWitnessClique Ws := by
    intro v hv w hw hvw
    have hvS : (Sum.inr v : SingleReservedFutureVertex d ell B T) ∈ s :=
      (Finset.mem_filter.mp hv).2
    have hwS : (Sum.inr w : SingleReservedFutureVertex d ell B T) ∈ s :=
      (Finset.mem_filter.mp hw).2
    have hNe : (Sum.inr v : SingleReservedFutureVertex d ell B T) ≠
        Sum.inr w := by
      intro hEq
      exact hvw (Sum.inr.inj hEq)
    exact hClique (Sum.inr v) hvS (Sum.inr w) hwS hNe
  have hWsSmall : Ws.card < ell :=
    universalWitnessFuture_clique_card_lt d ell hell B Ws hWsSub hWsClique
  have hQCard : Qs.card ≤ ell-1-B T := by
    have h := Finset.card_le_card (Finset.filter_subset
      (fun q : Fin (ell-1-B T) =>
        (Sum.inl q : SingleReservedFutureVertex d ell B T) ∈ s)
      (Finset.univ))
    simpa only [Finset.card_univ, Fintype.card_fin] using h
  have hCover : s ⊆
      Qs.image (fun q => (Sum.inl q : SingleReservedFutureVertex d ell B T)) ∪
      Ws.image (fun v => (Sum.inr v : SingleReservedFutureVertex d ell B T)) := by
    intro z hz
    cases z with
    | inl q =>
        have hq : q ∈ Qs := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,hz⟩
        exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_image.mpr ⟨q,hq,rfl⟩))
    | inr v =>
        have hIn : (Sum.inr v : SingleReservedFutureVertex d ell B T) ∈
            singleReservedFutureCarrier d ell B T := hSub hz
        have hvFuture : v ∈ universalWitnessFuture d ell B := by
          unfold singleReservedFutureCarrier at hIn
          rcases Finset.mem_union.mp hIn with hr | hf
          · obtain ⟨q,_,heq⟩ := Finset.mem_image.mp hr
            cases heq
          · obtain ⟨u,hu,heq⟩ := Finset.mem_image.mp hf
            cases heq
            exact hu
        have hv : v ∈ Ws := Finset.mem_filter.mpr ⟨hvFuture,hz⟩
        exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_image.mpr ⟨v,hv,rfl⟩))
  have hQImageCard :
      (Qs.image (fun q => (Sum.inl q : SingleReservedFutureVertex d ell B T))).card =
      Qs.card := by
    apply Finset.card_image_of_injective
    intro q p hp
    exact Sum.inl.inj hp
  have hWImageCard :
      (Ws.image (fun v => (Sum.inr v : SingleReservedFutureVertex d ell B T))).card =
      Ws.card := by
    apply Finset.card_image_of_injective
    intro v w heq
    exact Sum.inr.inj heq
  have hCard :
      s.card ≤ Qs.card + Ws.card := by
    have hSubCard := Finset.card_le_card hCover
    have hUnionCard :=
      Finset.card_union_le
        (Qs.image (fun q => (Sum.inl q : SingleReservedFutureVertex d ell B T)))
        (Ws.image (fun v => (Sum.inr v : SingleReservedFutureVertex d ell B T)))
    rw [hQImageCard, hWImageCard] at hUnionCard
    omega
  by_cases hQNonempty : Qs.Nonempty
  · obtain ⟨q,hq⟩ := hQNonempty
    have hqS : (Sum.inl q : SingleReservedFutureVertex d ell B T) ∈ s :=
      (Finset.mem_filter.mp hq).2
    have hAllSupport : ∀ v ∈ Ws, v.2.1 ∈ T.1 := by
      intro v hv
      have hvS : (Sum.inr v : SingleReservedFutureVertex d ell B T) ∈ s :=
        (Finset.mem_filter.mp hv).2
      have hEdge := hClique
        (Sum.inl q) hqS (Sum.inr v) hvS
        (by intro h; cases h)
      change decide (v.2.1 ∈ T.1) = true at hEdge
      exact decide_eq_true_eq.mp hEdge
    have hWFilter : Ws.filter (fun v => v.2.1 ∈ T.1) = Ws :=
      Finset.filter_eq_self.mpr hAllSupport
    have hRaw :=
      universalWitnessFuture_clique_respects_raw
        d ell hell B Ws hWsSub hWsClique T
    rw [hWFilter] at hRaw
    have hBudget :=
      rawSupportBlock_add_clique_below
        ell (B T) Ws.card hell hRaw hWsSmall
    omega
  · have hQEmpty : Qs = ∅ := Finset.not_nonempty_iff_eq_empty.mp hQNonempty
    rw [hQEmpty] at hCard
    simp at hCard
    omega

#print axioms singleReservedFutureEdge_symmetric
#print axioms singleReservedFutureEdge_irreflexive
#print axioms singleReservedFuture_no_forbidden_clique

end Kk
