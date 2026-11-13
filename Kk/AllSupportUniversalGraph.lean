import Kk.SingleReservedUniversalGraph
import Mathlib.Tactic

/-!
# An explicit finite ordinary-L graph encoding ALL raw support constraints

English mathematical proof and hostile audit committed FIRST:
  docs/all_support_universal_graph_english_audit.md

There is one genuine complete reserved block for EACH admissible support
T, with exactly ell-1-B(T) vertices (Nat truncated subtraction).
Different reserved blocks have no L edges. All reserved-to-future L
atoms are the exact corresponding sort-support bits in BOTH ordered
directions, and the common finite future is the verified W_B from
PRs #86 and #88. The designated finite graph is K_ell-free.

Unlike a conditional four-pool theorem this L graph is explicitly
constructed. This is not a full numerical H+ Kpt E/parameter-closed
source, a chronological resolved diary or a labelled monoid orbit.
-/

namespace Kk

/-- Genuine tagged reserved coordinates. The dependent Fin type
records the exact (possibly zero) raw-support block size. -/
abbrev AllSupportReservedSlot (d ell : Nat)
    (B : IntegerGraphSupport d ell → Nat) :=
  Σ T : IntegerGraphSupport d ell, Fin (ell-1-B T)

/-- Disjoint sum of all possible reserved slots and ordinary-L
universal future coordinates. The latter are restricted to W_B
by the designated carrier below. -/
abbrev AllSupportFutureVertex (d ell : Nat)
    (B : IntegerGraphSupport d ell → Nat) :=
  Sum (AllSupportReservedSlot d ell B) (UniversalWitnessVertex d ell)

/-- Finite carrier of ALL reserved blocks plus precisely the feasible
future vertices. No infeasible dependent-sum vertex is included. -/
noncomputable def allSupportFutureCarrier
    (d ell : Nat) (B : IntegerGraphSupport d ell → Nat) :
    Finset (AllSupportFutureVertex d ell B) := by
  classical
  exact ((Finset.univ : Finset (AllSupportReservedSlot d ell B)).image Sum.inl) ∪
    (universalWitnessFuture d ell B).image Sum.inr

/-- Complete off-diagonal L inside each individual reserved support block;
no edges across different reserved blocks. Every mixed reserved/future
bit, in BOTH directions, is exactly the tag's support membership. -/
def allSupportFutureEdge {d ell : Nat}
    {B : IntegerGraphSupport d ell → Nat}
    (x y : AllSupportFutureVertex d ell B) : Bool :=
  match x,y with
  | Sum.inl q, Sum.inl p => decide (q.1 = p.1 ∧ q ≠ p)
  | Sum.inl q, Sum.inr v => decide (v.2.1 ∈ q.1.1)
  | Sum.inr v, Sum.inl q => decide (v.2.1 ∈ q.1.1)
  | Sum.inr v, Sum.inr w => universalWitnessEdge v w

def IsAllSupportFutureClique {d ell : Nat}
    {B : IntegerGraphSupport d ell → Nat}
    (s : Finset (AllSupportFutureVertex d ell B)) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y → allSupportFutureEdge x y = true

theorem allSupportFutureEdge_symmetric {d ell : Nat}
    {B : IntegerGraphSupport d ell → Nat}
    (x y : AllSupportFutureVertex d ell B) :
    allSupportFutureEdge x y = allSupportFutureEdge y x := by
  cases x with
  | inl q =>
    cases y with
    | inl p => simp [allSupportFutureEdge, eq_comm, ne_comm]
    | inr v => rfl
  | inr v =>
    cases y with
    | inl q => rfl
    | inr w => exact universalWitnessEdge_symmetric v w

theorem allSupportFutureEdge_irreflexive {d ell : Nat}
    {B : IntegerGraphSupport d ell → Nat}
    (x : AllSupportFutureVertex d ell B) :
    allSupportFutureEdge x x = false := by
  cases x with
  | inl q => simp [allSupportFutureEdge]
  | inr v => exact universalWitnessEdge_irreflexive v

/-- Every directed clique of the explicit finite graph is K_ell-free.
An arbitrary clique meeting a reserved block is confined to ONE
support tag T, and every one of its future vertices lies in T.
Its size is bounded by the actual reserved block cardinality plus
the supported future clique count, which is strictly below ell. -/
theorem allSupportFuture_no_forbidden_clique
    (d ell : Nat) (hell : 0 < ell)
    (B : IntegerGraphSupport d ell → Nat)
    (s : Finset (AllSupportFutureVertex d ell B))
    (hSub : s ⊆ allSupportFutureCarrier d ell B)
    (hClique : IsAllSupportFutureClique s) :
    s.card < ell := by
  classical
  let Qs : Finset (AllSupportReservedSlot d ell B) :=
    Finset.univ.filter
      (fun q => (Sum.inl q : AllSupportFutureVertex d ell B) ∈ s)
  let Ws : Finset (UniversalWitnessVertex d ell) :=
    (universalWitnessFuture d ell B).filter
      (fun v => (Sum.inr v : AllSupportFutureVertex d ell B) ∈ s)
  have hWsSub : Ws ⊆ universalWitnessFuture d ell B :=
    Finset.filter_subset _ _
  have hWsClique : IsUniversalWitnessClique Ws := by
    intro v hv w hw hvw
    have hvS : (Sum.inr v : AllSupportFutureVertex d ell B) ∈ s :=
      (Finset.mem_filter.mp hv).2
    have hwS : (Sum.inr w : AllSupportFutureVertex d ell B) ∈ s :=
      (Finset.mem_filter.mp hw).2
    have hNe : (Sum.inr v : AllSupportFutureVertex d ell B) ≠
        Sum.inr w := by
      intro hEq
      exact hvw (Sum.inr.inj hEq)
    exact hClique (Sum.inr v) hvS (Sum.inr w) hwS hNe
  have hWsSmall : Ws.card < ell :=
    universalWitnessFuture_clique_card_lt d ell hell B Ws hWsSub hWsClique
  have hCover : s ⊆
      Qs.image (fun q => (Sum.inl q : AllSupportFutureVertex d ell B)) ∪
      Ws.image (fun v => (Sum.inr v : AllSupportFutureVertex d ell B)) := by
    intro z hz
    cases z with
    | inl q =>
        have hq : q ∈ Qs :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩
        exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_image.mpr ⟨q,hq,rfl⟩))
    | inr v =>
        have hCarrier : (Sum.inr v : AllSupportFutureVertex d ell B) ∈
            allSupportFutureCarrier d ell B := hSub hz
        have hvFuture : v ∈ universalWitnessFuture d ell B := by
          unfold allSupportFutureCarrier at hCarrier
          rcases Finset.mem_union.mp hCarrier with hr | hf
          · obtain ⟨q,_,heq⟩ := Finset.mem_image.mp hr
            cases heq
          · obtain ⟨u,hu,heq⟩ := Finset.mem_image.mp hf
            cases heq
            exact hu
        have hv : v ∈ Ws :=
          Finset.mem_filter.mpr ⟨hvFuture,hz⟩
        exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_image.mpr ⟨v,hv,rfl⟩))
  have hQImageCard :
      (Qs.image (fun q => (Sum.inl q : AllSupportFutureVertex d ell B))).card =
      Qs.card := by
    apply Finset.card_image_of_injective
    intro q p hEq
    exact Sum.inl.inj hEq
  have hWImageCard :
      (Ws.image (fun v => (Sum.inr v : AllSupportFutureVertex d ell B))).card =
      Ws.card := by
    apply Finset.card_image_of_injective
    intro v w hEq
    exact Sum.inr.inj hEq
  have hCard : s.card ≤ Qs.card + Ws.card := by
    have hSubCard := Finset.card_le_card hCover
    have hUnionCard :=
      Finset.card_union_le
        (Qs.image (fun q => (Sum.inl q : AllSupportFutureVertex d ell B)))
        (Ws.image (fun v => (Sum.inr v : AllSupportFutureVertex d ell B)))
    rw [hQImageCard,hWImageCard] at hUnionCard
    omega
  by_cases hQNonempty : Qs.Nonempty
  · obtain ⟨q,hq⟩ := hQNonempty
    let T : IntegerGraphSupport d ell := q.1
    have hqS : (Sum.inl q : AllSupportFutureVertex d ell B) ∈ s :=
      (Finset.mem_filter.mp hq).2
    have hSameTag : ∀ p ∈ Qs, p.1 = T := by
      intro p hp
      by_cases hpq : p = q
      · exact congrArg Sigma.fst hpq
      · have hpS : (Sum.inl p : AllSupportFutureVertex d ell B) ∈ s :=
          (Finset.mem_filter.mp hp).2
        have hNe : (Sum.inl q : AllSupportFutureVertex d ell B) ≠
            Sum.inl p := by
          intro heq
          exact hpq (Sum.inl.inj heq).symm
        have hEdge := hClique (Sum.inl q) hqS (Sum.inl p) hpS hNe
        change decide (q.1 = p.1 ∧ q ≠ p) = true at hEdge
        exact (decide_eq_true_eq.mp hEdge).1.symm
    let QFull : Finset (AllSupportReservedSlot d ell B) :=
      (Finset.univ : Finset (Fin (ell-1-B T))).image
        (fun t => (⟨T,t⟩ : AllSupportReservedSlot d ell B))
    have hQSub : Qs ⊆ QFull := by
      intro p hp
      have hpTag := hSameTag p hp
      rcases p with ⟨U,t⟩
      change U = T at hpTag
      subst U
      exact Finset.mem_image.mpr ⟨t,Finset.mem_univ _,rfl⟩
    have hQFullCard : QFull.card = ell-1-B T := by
      unfold QFull
      have hInj : Function.Injective
          (fun t : Fin (ell-1-B T) =>
            (⟨T,t⟩ : AllSupportReservedSlot d ell B)) := by
        intro x y hEq
        cases hEq
        rfl
      rw [Finset.card_image_of_injective _ hInj]
      simp
    have hQCard : Qs.card ≤ ell-1-B T :=
      (Finset.card_le_card hQSub).trans (le_of_eq hQFullCard)
    have hAllSupport : ∀ v ∈ Ws, v.2.1 ∈ T.1 := by
      intro v hv
      have hvS : (Sum.inr v : AllSupportFutureVertex d ell B) ∈ s :=
        (Finset.mem_filter.mp hv).2
      have hEdge := hClique (Sum.inl q) hqS (Sum.inr v) hvS
        (by intro heq; cases heq)
      change decide (v.2.1 ∈ q.1.1) = true at hEdge
      exact decide_eq_true_eq.mp hEdge
    have hWFilter : Ws.filter (fun v => v.2.1 ∈ T.1) = Ws :=
      Finset.filter_eq_self.mpr hAllSupport
    have hRaw := universalWitnessFuture_clique_respects_raw
      d ell hell B Ws hWsSub hWsClique T
    rw [hWFilter] at hRaw
    have hBudget := rawSupportBlock_add_clique_below
      ell (B T) Ws.card hell hRaw hWsSmall
    omega
  · have hQEmpty : Qs = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hQNonempty
    rw [hQEmpty] at hCard
    simp at hCard
    omega

#print axioms allSupportFutureEdge_symmetric
#print axioms allSupportFutureEdge_irreflexive
#print axioms allSupportFuture_no_forbidden_clique

end Kk
