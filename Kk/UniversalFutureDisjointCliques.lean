import Kk.ConcreteCanonicalMaximizers
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# One finite ordinary-L future realizing all feasible normalized clique vectors

The English construction and hostile audit were committed BEFORE this
Lean file in docs/universal_future_disjoint_cliques_english_audit.md.

For each normalized weight vector w, let its component consist of all
actual typed vertices of the previously verified complete L-clique.
The common finite future W_B is the disjoint union of precisely those
components whose weights obey every raw bound B(U), with no binary
edges between different component indices.

Theorems show:
* each component is an exact complete finite labelled clique;
* every clique in W_B lies in ONE feasible component;
* hence W_B is K_ell-free and every clique obeys all raw B bounds;
* EVERY feasible normalized vector has its full complete component.

No old graph, reserved support blocks, Henson extension, numerical-H
auxiliary E, B3 parameter closure or labelled orbit is claimed here.
-/

namespace Kk

/-- Ambient finite dependent sum carrying *all* normalized typed clique
vertices. Feasible components are selected by a finite pool below. -/
abbrev UniversalWitnessVertex (d ell : Nat) :=
  Σ w : IntegerCliqueWeights d ell, IntegerWitnessVertex w

/-- Image of a genuine complete typed clique as one named component of
the common finite dependent sum. The index w remains part of the vertex
identity even if two components have equal abstract sizes. -/
noncomputable def universalWitnessComponent
    {d ell : Nat} (w : IntegerCliqueWeights d ell) :
    Finset (UniversalWitnessVertex d ell) := by
  classical
  exact (Finset.univ : Finset (IntegerWitnessVertex w)).image (Sigma.mk w)

/-- The ONE finite future pool formed from ALL feasible normalized
weight vectors for the arbitrary raw upper-bound function B. -/
noncomputable def universalWitnessFuture (d ell : Nat)
    (B : IntegerGraphSupport d ell → Nat) :
    Finset (UniversalWitnessVertex d ell) := by
  classical
  exact (feasibleIntegerCliqueVectors d ell B).biUnion universalWitnessComponent

/-- Literal symmetric irreflexive ordinary-L edge relation:
same feasible-component INDEX and different vertices. -/
def universalWitnessEdge {d ell : Nat}
    (x y : UniversalWitnessVertex d ell) : Bool :=
  decide (x.1 = y.1 ∧ x ≠ y)

/-- Directed completeness of a subset for the genuine chosen L edge. -/
def IsUniversalWitnessClique {d ell : Nat}
    (s : Finset (UniversalWitnessVertex d ell)) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y → universalWitnessEdge x y = true

theorem universalWitnessEdge_symmetric {d ell : Nat}
    (x y : UniversalWitnessVertex d ell) :
    universalWitnessEdge x y = universalWitnessEdge y x := by
  simp [universalWitnessEdge, eq_comm, ne_comm]

theorem universalWitnessEdge_irreflexive {d ell : Nat}
    (x : UniversalWitnessVertex d ell) :
    universalWitnessEdge x x = false := by
  simp [universalWitnessEdge]

/-- A vertex belongs to a component if and only if its first
(dependent Sigma) index equals that component's normalized weight. -/
theorem universalWitness_mem_component_iff
    {d ell : Nat} (w : IntegerCliqueWeights d ell)
    (v : UniversalWitnessVertex d ell) :
    v ∈ universalWitnessComponent w ↔ v.1 = w := by
  classical
  constructor
  · intro h
    obtain ⟨t,_,heq⟩ := Finset.mem_image.mp h
    cases heq
    rfl
  · intro h
    rcases v with ⟨j,t⟩
    change j = w at h
    subst j
    exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩

theorem universalWitnessComponent_injective
    {d ell : Nat} (w : IntegerCliqueWeights d ell) :
    Function.Injective
      (fun v : IntegerWitnessVertex w =>
        (⟨w,v⟩ : UniversalWitnessVertex d ell)) := by
  intro x y h
  cases h
  rfl

/-- The named Sigma component has the same cardinality as the
complete typed clique it represents; every copy is injective. -/
theorem universalWitnessComponent_card
    {d ell : Nat} (w : IntegerCliqueWeights d ell) :
    (universalWitnessComponent w).card =
      Fintype.card (IntegerWitnessVertex w) := by
  classical
  unfold universalWitnessComponent
  rw [Finset.card_image_of_injective _
    (universalWitnessComponent_injective w)]
  rfl

/-- The actual named-component cardinality is below ell. The
positivity condition excludes the ell=0 degenerate weight subtype. -/
theorem universalWitnessComponent_card_lt
    {d ell : Nat} (w : IntegerCliqueWeights d ell)
    (hell : 0 < ell) :
    (universalWitnessComponent w).card < ell := by
  rw [universalWitnessComponent_card]
  exact integerWitnessVertex_card_lt w hell

/-- Named-component label support counts agree EXACTLY with the
existing normalized integer graph-age witness API. -/
theorem universalWitnessComponent_support_card
    {d ell : Nat} (w : IntegerCliqueWeights d ell)
    (T : IntegerGraphSupport d ell) :
    ((universalWitnessComponent w).filter (fun u => u.2.1 ∈ T.1)).card =
      integerCliqueOnSupport w T := by
  classical
  have hImage :
      (universalWitnessComponent w).filter (fun u => u.2.1 ∈ T.1) =
        ((Finset.univ : Finset (IntegerWitnessVertex w)).filter
          (fun v => v.1 ∈ T.1)).image (Sigma.mk w) := by
    ext u
    constructor
    · intro hu
      obtain ⟨v,_,heq⟩ :=
        Finset.mem_image.mp (Finset.mem_filter.mp hu).1
      subst u
      apply Finset.mem_image.mpr
      refine ⟨v,?_,rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2⟩
    · intro hu
      obtain ⟨v,hv,heq⟩ := Finset.mem_image.mp hu
      subst u
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr
        ⟨v,Finset.mem_univ _,rfl⟩, ?_⟩
      exact (Finset.mem_filter.mp hv).2
  rw [hImage, Finset.card_image_of_injective _
    (universalWitnessComponent_injective w)]
  exact integerWitnessVertex_support_eq_integerCliqueOnSupport w T

/-- Each named component is literally a complete directed L-clique
in the common graph. No additional finite graph-age axiom. -/
theorem universalWitnessComponent_clique
    {d ell : Nat} (w : IntegerCliqueWeights d ell) :
    IsUniversalWitnessClique (universalWitnessComponent w) := by
  intro x hx y hy hxy
  have hxWeight := (universalWitness_mem_component_iff w x).mp hx
  have hyWeight := (universalWitness_mem_component_iff w y).mp hy
  simp [universalWitnessEdge, hxWeight,hyWeight,hxy]

/-- A positive ordinary-L edge can only join vertices with the
same normalized-vector component INDEX. -/
theorem universalWitnessEdge_same_index
    {d ell : Nat} (x y : UniversalWitnessVertex d ell)
    (h : universalWitnessEdge x y = true) : x.1 = y.1 := by
  exact (decide_eq_true_eq.mp h).1

/-- Every nonempty clique of the common graph lies within the named
component of any one of its vertices. -/
theorem universalWitnessClique_single_component
    {d ell : Nat}
    (s : Finset (UniversalWitnessVertex d ell))
    (hClique : IsUniversalWitnessClique s)
    (hNonempty : s.Nonempty) :
    ∃ w : IntegerCliqueWeights d ell,
      s ⊆ universalWitnessComponent w := by
  obtain ⟨x,hx⟩ := hNonempty
  refine ⟨x.1,?_⟩
  intro y hy
  apply (universalWitness_mem_component_iff x.1 y).2
  by_cases hxy : x = y
  · exact congrArg Sigma.fst hxy.symm
  · exact universalWitnessEdge_same_index y x
      (hClique y hy x hx (Ne.symm hxy))

/-- All component indices used by the future pool are genuinely
feasible for the same WHOLE raw support-bound system B. -/
theorem universalWitnessFuture_clique_in_feasible_component
    (d ell : Nat) (hell : 0 < ell)
    (B : IntegerGraphSupport d ell → Nat)
    (s : Finset (UniversalWitnessVertex d ell))
    (hSub : s ⊆ universalWitnessFuture d ell B)
    (hClique : IsUniversalWitnessClique s) :
    ∃ w ∈ feasibleIntegerCliqueVectors d ell B,
      s ⊆ universalWitnessComponent w := by
  classical
  by_cases hne : s.Nonempty
  · obtain ⟨x,hx⟩ := hne
    have hxFeasible : x.1 ∈ feasibleIntegerCliqueVectors d ell B := by
      obtain ⟨w,hw,hxw⟩ := Finset.mem_biUnion.mp (hSub hx)
      have heq : x.1 = w := (universalWitness_mem_component_iff w x).mp hxw
      exact heq ▸ hw
    obtain ⟨w,hwSub⟩ :=
      universalWitnessClique_single_component s hClique ⟨x,hx⟩
    have hwEq : w = x.1 := by
      have hmem : x ∈ universalWitnessComponent w := hwSub hx
      exact ((universalWitness_mem_component_iff w x).mp hmem).symm
    refine ⟨w,?_,hwSub⟩
    exact hwEq ▸ hxFeasible
  · obtain ⟨w,hw⟩ := feasibleIntegerCliqueVectors_nonempty d ell hell B
    refine ⟨w,hw,?_⟩
    have hsEmpty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hsEmpty]

/-- The one finite universal future is K_ell-free in its explicit
ordinary-L graph: EVERY directed clique has fewer than ell vertices. -/
theorem universalWitnessFuture_clique_card_lt
    (d ell : Nat) (hell : 0 < ell)
    (B : IntegerGraphSupport d ell → Nat)
    (s : Finset (UniversalWitnessVertex d ell))
    (hSub : s ⊆ universalWitnessFuture d ell B)
    (hClique : IsUniversalWitnessClique s) : s.card < ell := by
  obtain ⟨w,_,hsComp⟩ :=
    universalWitnessFuture_clique_in_feasible_component
      d ell hell B s hSub hClique
  exact lt_of_le_of_lt (Finset.card_le_card hsComp)
    (universalWitnessComponent_card_lt w hell)

/-- There are NO spurious raw support-count patterns: each clique
inside W_B satisfies EVERY original B(T) bound. The universal
pool can be non-complete; its cliques never mix distinct components. -/
theorem universalWitnessFuture_clique_respects_raw
    (d ell : Nat) (hell : 0 < ell)
    (B : IntegerGraphSupport d ell → Nat)
    (s : Finset (UniversalWitnessVertex d ell))
    (hSub : s ⊆ universalWitnessFuture d ell B)
    (hClique : IsUniversalWitnessClique s)
    (T : IntegerGraphSupport d ell) :
    (s.filter (fun u => u.2.1 ∈ T.1)).card ≤ B T := by
  classical
  obtain ⟨w, hw, hsComp⟩ :=
    universalWitnessFuture_clique_in_feasible_component
      d ell hell B s hSub hClique
  have hwB : WitnessRespects
      (integerCliqueOnSupport (d := d) (ell := ell)) B w := by
    change w ∈ Finset.univ.filter
      (WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell)) B)
      at hw
    exact (Finset.mem_filter.mp hw).2
  have hFiltSub :
      s.filter (fun u => u.2.1 ∈ T.1) ⊆
        (universalWitnessComponent w).filter
          (fun u => u.2.1 ∈ T.1) := by
    intro u hu
    exact Finset.mem_filter.mpr
      ⟨hsComp (Finset.mem_filter.mp hu).1,
        (Finset.mem_filter.mp hu).2⟩
  have hCard := Finset.card_le_card hFiltSub
  rw [universalWitnessComponent_support_card] at hCard
  exact hCard.trans (hwB T)

/-- EVERY feasible normalized labelled vector occurs as the
COMPLETE directed clique of its own named component, contained
in the common finite future W_B. Its full support counts agree
on ALL admissible sorts, not just a chosen maximizer support. -/
theorem universalWitnessFuture_realizes_every_feasible
    (d ell : Nat) (hell : 0 < ell)
    (B : IntegerGraphSupport d ell → Nat)
    (w : IntegerCliqueWeights d ell)
    (hw : w ∈ feasibleIntegerCliqueVectors d ell B) :
    (universalWitnessComponent w ⊆ universalWitnessFuture d ell B) ∧
    IsUniversalWitnessClique (universalWitnessComponent w) ∧
    (∀ T : IntegerGraphSupport d ell,
      ((universalWitnessComponent w).filter
        (fun u => u.2.1 ∈ T.1)).card = integerCliqueOnSupport w T) ∧
    (universalWitnessComponent w).card < ell := by
  classical
  refine ⟨?_,universalWitnessComponent_clique w,
    universalWitnessComponent_support_card w,
    universalWitnessComponent_card_lt w hell⟩
  intro u hu
  exact Finset.mem_biUnion.mpr ⟨w,hw,hu⟩

#print axioms universalWitnessEdge_symmetric
#print axioms universalWitnessEdge_irreflexive
#print axioms universalWitness_mem_component_iff
#print axioms universalWitnessComponent_card
#print axioms universalWitnessComponent_support_card
#print axioms universalWitnessComponent_clique
#print axioms universalWitnessClique_single_component
#print axioms universalWitnessFuture_clique_in_feasible_component
#print axioms universalWitnessFuture_clique_card_lt
#print axioms universalWitnessFuture_clique_respects_raw
#print axioms universalWitnessFuture_realizes_every_feasible

end Kk
