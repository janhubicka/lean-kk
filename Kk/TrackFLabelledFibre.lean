import Mathlib.Tactic

/-!
# Track F: exact labelled diary fibres for finite binary graphs

Every distinct diary whose coded graph is isomorphic to A contributes
exactly |Aut(A)| labelled isomorphism types, not |A|! in general.
The proof uses actual binary-relation isomorphisms, preserving both
positive and negative graph relations, and allows diary-dependent carriers.
This is a finite combinatorial lemma, not an unavoidability theorem.
-/

namespace Kk

universe u v w

/-- A genuine binary relational isomorphism, preserving edges and
nonedges simultaneously. The carrier types may differ. -/
abbrev TrackFRelIso {α : Type u} {β : Type v}
    (R : α → α → Prop) (S : β → β → Prop) :=
  {e : α ≃ β // ∀ x y, R x y ↔ S (e x) (e y)}

/-- Every binary relational isomorphism type on two finite carriers is
finite, as a subtype of the finite equivalence type. -/
noncomputable instance trackFRelIsoFintype
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (R : α → α → Prop) (S : β → β → Prop) :
    Fintype (TrackFRelIso R S) := by
  classical
  exact inferInstanceAs
    (Fintype {e : α ≃ β // ∀ x y, R x y ↔ S (e x) (e y)})

/-- Inverse of a binary relational isomorphism. -/
def trackFRelIsoSymm
    {α : Type u} {β : Type v}
    {R : α → α → Prop} {S : β → β → Prop}
    (f : TrackFRelIso R S) : TrackFRelIso S R := by
  refine ⟨f.1.symm, ?_⟩
  intro x y
  simpa using (f.2 (f.1.symm x) (f.1.symm y)).symm

/-- Composition preserves *both* edges and nonedges. -/
def trackFRelIsoTrans
    {α : Type u} {β : Type v} {γ : Type w}
    {R : α → α → Prop} {S : β → β → Prop}
    {T : γ → γ → Prop}
    (f : TrackFRelIso R S) (g : TrackFRelIso S T) :
    TrackFRelIso R T := by
  refine ⟨f.1.trans g.1, ?_⟩
  intro x y
  exact (f.2 x y).trans (g.2 (f.1 x) (f.1 y))

/-- For a fixed isomorphism h : A ≅ B, isomorphisms A ≅ B
form a torsor for the automorphism group Aut(A). The equivalence is
precomposition by the genuine graph automorphism (not by all
permutations of A). -/
def trackFRelIsoAutEquiv
    {α : Type u} {β : Type v}
    {R : α → α → Prop} {S : β → β → Prop}
    (h : TrackFRelIso R S) :
    TrackFRelIso R R ≃ TrackFRelIso R S where
  toFun := fun a => trackFRelIsoTrans a h
  invFun := fun g => trackFRelIsoTrans g (trackFRelIsoSymm h)
  left_inv := by
    intro a
    apply Subtype.ext
    apply Equiv.ext
    intro x
    simp [trackFRelIsoTrans, trackFRelIsoSymm]
  right_inv := by
    intro g
    apply Subtype.ext
    apply Equiv.ext
    intro x
    simp [trackFRelIsoTrans, trackFRelIsoSymm]

/-- Counting **distinct diary objects** d and genuine labelled graph
isomorphisms from A onto each coded graph gives the copy diary count
times the actual automorphism-group order of A.

This theorem assumes each coded graph has a chosen graph isomorphism
from A, but does not assume an unproved diary bijection, does not count
the big Ramsey degree, and does not assert type unavoidability. -/
theorem trackF_card_labelled_diaries
    {D : Type u} [Fintype D]
    {A : Type v} [Fintype A]
    (R : A → A → Prop)
    (Carrier : D → Type w)
    [∀ d : D, Fintype (Carrier d)]
    (S : ∀ d, Carrier d → Carrier d → Prop)
    (h : ∀ d, TrackFRelIso R (S d)) :
    Fintype.card (Sigma fun d : D => TrackFRelIso R (S d)) =
      Fintype.card D * Fintype.card (TrackFRelIso R R) := by
  classical
  calc
    Fintype.card (Sigma fun d : D => TrackFRelIso R (S d)) =
        ∑ d : D, Fintype.card (TrackFRelIso R (S d)) := Fintype.card_sigma
    _ = ∑ d : D, Fintype.card (TrackFRelIso R R) := by
      apply Finset.sum_congr rfl
      intro d _
      exact Fintype.card_congr (trackFRelIsoAutEquiv (h d)).symm
    _ = Fintype.card D * Fintype.card (TrackFRelIso R R) := by
      simp

end Kk
