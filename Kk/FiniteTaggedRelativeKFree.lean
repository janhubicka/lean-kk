import Kk.FiniteTaggedFutureEncoding
import Kk.FiniteOldColumnAge
import Kk.NumericPrefixCanonicalCover
import Mathlib.Tactic

/-!
# Track A: all raw old-column bounds imply a genuine finite relative K-free target

English proof and adversarial audit FIRST:
  docs/finite_tagged_relative_kfree_english_audit.md

The exact finite-tagged Nat graph A is defined in
Kk.FiniteTaggedFutureEncoding. This module proves its entire literal
old-plus-future prefix is K_ell-free whenever the original entire
old prefix is K_ell-free and EVERY directed future clique obeys
the actual common-old-neighbour raw bounds B_P(T), on EVERY
admissible nonempty support T.

The source future V may be any finite graph (not necessarily a clique).
Its original/future two-directed typed crossing bits are a definition,
not assumptions. A is therefore a genuine relative compatible finite
ordinary-L target; applying the pinned Henson theorem requires the
separately checked symmetry/loop-freeness of old E and finite future R.

This is a finite compatibility theorem, not yet the specialized
universal witness W_B or the unbounded resolved-copy schedule,
and not auxiliary Kpt E/B3/monoid orbit.
-/

namespace Kk

/-- Directed cliquehood for a finite tagged type V, exactly as for
the existing Nat-based finite clique checker. -/
def IsFiniteTaggedClique {V : Type*}
    (R : V → V → Bool) (s : Finset V) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y → R x y = true

/-- A future tagged clique is precisely its fully induced literal
Nat-coded image. Both orientations of every L bit are used. -/
theorem finiteTagged_clique_iff_image
    {d : Nat} {V : Type*} [Fintype V]
    (b : Nat) (E : Nat → Nat → Bool)
    (R : V → V → Bool) (sort : V → Fin d)
    (c : Nat → Fin d → Bool) (s : Finset V) :
    IsFiniteTaggedClique R s ↔
      IsDirectedCliqueOn
        (finiteTaggedOldFutureEdge b E R sort c)
        (s.image (finiteTaggedIndex b)) := by
  classical
  constructor
  · intro hClique x hx y hy hxy
    obtain ⟨u,hu,hux⟩ := Finset.mem_image.mp hx
    obtain ⟨v,hv,hvy⟩ := Finset.mem_image.mp hy
    have huv : u ≠ v := by
      intro heq
      subst v
      exact hxy (hux.symm.trans hvy)
    have hSource := hClique u hu v hv huv
    have hEdge := finiteTaggedEdge_future_future
      b E R sort c u v
    have hTarget :
        finiteTaggedOldFutureEdge b E R sort c
          (finiteTaggedIndex b u) (finiteTaggedIndex b v) = true :=
      hEdge.trans hSource
    simpa only [hux,hvy] using hTarget
  · intro hClique u hu v hv huv
    have hCodeNe : finiteTaggedIndex b u ≠ finiteTaggedIndex b v := by
      intro heq
      exact huv (finiteTaggedIndex_injective b heq)
    have hTarget :=
      hClique (finiteTaggedIndex b u)
        (Finset.mem_image.mpr ⟨u,hu,rfl⟩)
        (finiteTaggedIndex b v)
        (Finset.mem_image.mpr ⟨v,hv,rfl⟩) hCodeNe
    exact (finiteTaggedEdge_future_future b E R sort c u v).symm.trans
      hTarget

/-- Every finite subset of the coded future is exactly the image
of its finite tagged-type preimage. No default tagged vertex is
chosen, so the empty V case is valid. -/
theorem finiteTagged_future_subset_pullback_image
    {V : Type*} [Fintype V] (b : Nat)
    (t : Finset Nat)
    (ht : t ⊆ finiteTaggedFuturePool (V := V) b) :
    (((Finset.univ : Finset V).filter
      (fun v => finiteTaggedIndex b v ∈ t)).image
        (finiteTaggedIndex b)) = t := by
  classical
  apply Finset.Subset.antisymm
  · intro z hz
    obtain ⟨v,hv,hvz⟩ := Finset.mem_image.mp hz
    exact hvz ▸ (Finset.mem_filter.mp hv).2
  · intro z hz
    have hTarget : z ∈ finiteTaggedFuturePool (V := V) b := ht hz
    change z ∈ ((Finset.univ : Finset V).image
        (finiteTaggedIndex b)) at hTarget
    obtain ⟨v,hv,hvz⟩ := Finset.mem_image.mp hTarget
    exact Finset.mem_image.mpr
      ⟨v,Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hvz ▸ hz⟩,hvz⟩

/-- The exact sort-support cardinality of every finite tagged clique
is preserved by the code, using the TOTAL labelled Nat map
from the encoder (which requires d>0). -/
theorem finiteTagged_support_count_image
    {d ell : Nat} {V : Type*} [Fintype V]
    (hd : 0 < d) (b : Nat)
    (sort : V → Fin d) (s : Finset V)
    (T : IntegerGraphSupport d ell) :
    (((s.image (finiteTaggedIndex b)).filter
      (fun z => finiteTaggedFutureSort hd sort b z ∈ T.1))).card =
        (s.filter (fun v => sort v ∈ T.1)).card := by
  classical
  have hFilterImage :
      ((s.image (finiteTaggedIndex b)).filter
        (fun z => finiteTaggedFutureSort hd sort b z ∈ T.1)) =
      (s.filter (fun v => sort v ∈ T.1)).image
        (finiteTaggedIndex b) := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzImg,hzType⟩ := Finset.mem_filter.mp hz
      obtain ⟨v,hv,hvz⟩ := Finset.mem_image.mp hzImg
      have hvType : sort v ∈ T.1 := by
        simpa only [← hvz,finiteTaggedFutureSort_index] using hzType
      exact Finset.mem_image.mpr
        ⟨v,Finset.mem_filter.mpr ⟨hv,hvType⟩,hvz⟩
    · intro hz
      obtain ⟨v,hv,hvz⟩ := Finset.mem_image.mp hz
      obtain ⟨hvs,hvType⟩ := Finset.mem_filter.mp hv
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨v,hvs,hvz⟩,?_⟩
      simpa only [← hvz,finiteTaggedFutureSort_index] using hvType
  rw [hFilterImage]
  exact Finset.card_image_of_injective _
    (finiteTaggedIndex_injective b)

/-- Exact K_ell-freeness of the coded future from the same property
of every directed clique in the finite tagged source V. -/
theorem finiteTagged_future_KFree
    {d : Nat} {V : Type*} [Fintype V]
    (b ell : Nat) (E : Nat → Nat → Bool)
    (R : V → V → Bool) (sort : V → Fin d)
    (c : Nat → Fin d → Bool)
    (hSmall : ∀ s : Finset V, IsFiniteTaggedClique R s → s.card < ell) :
    finitePoolCliqueCheck
      (finiteTaggedOldFutureEdge b E R sort c)
      ell (finiteTaggedFuturePool (V := V) b) = false := by
  classical
  apply (finitePoolCliqueCheck_false_iff
    (finiteTaggedOldFutureEdge b E R sort c)
    ell (finiteTaggedFuturePool (V := V) b)).2
  rintro ⟨t,htSub,htCard,htClique⟩
  let s : Finset V := (Finset.univ : Finset V).filter
    (fun v => finiteTaggedIndex b v ∈ t)
  have hImage : s.image (finiteTaggedIndex b) = t :=
    finiteTagged_future_subset_pullback_image b t htSub
  have hsClique : IsFiniteTaggedClique R s := by
    apply (finiteTagged_clique_iff_image b E R sort c s).mpr
    rw [hImage]
    exact htClique
  have hsSmall := hSmall s hsClique
  have hCardImage :
      (s.image (finiteTaggedIndex b)).card = s.card :=
    Finset.card_image_of_injective _
      (finiteTaggedIndex_injective b)
  rw [hImage] at hCardImage
  omega

/-- All labelled clique counts of the ACTUAL coded Nat future
satisfy the SAME raw bound B as the original arbitrary tagged
source graph. Includes every support and every directed clique. -/
theorem finiteTagged_future_raw_bounds
    {d ell : Nat} {V : Type*} [Fintype V]
    (hd : 0 < d) (b : Nat) (E : Nat → Nat → Bool)
    (R : V → V → Bool) (sort : V → Fin d)
    (c : Nat → Fin d → Bool)
    (B : IntegerGraphSupport d ell → Nat)
    (hBounds : ∀ s : Finset V, IsFiniteTaggedClique R s →
      ∀ T : IntegerGraphSupport d ell,
        (s.filter (fun v => sort v ∈ T.1)).card ≤ B T) :
    ∀ t : Finset Nat,
      t ⊆ finiteTaggedFuturePool (V := V) b →
      IsDirectedCliqueOn (finiteTaggedOldFutureEdge b E R sort c) t →
      ∀ T : IntegerGraphSupport d ell,
        (t.filter (fun z =>
          finiteTaggedFutureSort hd sort b z ∈ T.1)).card ≤ B T := by
  classical
  intro t htW htClique T
  let s : Finset V := (Finset.univ : Finset V).filter
    (fun v => finiteTaggedIndex b v ∈ t)
  have hImage : s.image (finiteTaggedIndex b) = t :=
    finiteTagged_future_subset_pullback_image b t htW
  have hsClique : IsFiniteTaggedClique R s := by
    apply (finiteTagged_clique_iff_image b E R sort c s).mpr
    rw [hImage]
    exact htClique
  have hCounts := finiteTagged_support_count_image hd b sort s T
  rw [hImage] at hCounts
  have hSourceBound := hBounds s hsClique T
  rw [← hCounts] at hSourceBound
  exact hSourceBound

/-- The raw graph-age bounds computed from the literal OLD Nat
prefix are unchanged after gluing an exactly typed finite future,
because the old-old L atoms agree off-diagonal in BOTH directions. -/
theorem finiteTagged_old_reference_raw_bounds_eq
    {d : Nat} {V : Type*} [Fintype V]
    (b ell : Nat) (E : Nat → Nat → Bool)
    (R : V → V → Bool) (sort : V → Fin d)
    (c : Nat → Fin d → Bool) :
    ∀ T : IntegerGraphSupport d ell,
      finiteOldColumnRawBound
        (finiteTaggedOldFutureEdge b E R sort c)
        ell d (Finset.range b) c T =
      finiteOldColumnRawBound E ell d (Finset.range b) c T := by
  intro T
  have hCapacity :
      finiteDirectedCliqueCapacity
        (finiteTaggedOldFutureEdge b E R sort c)
        (oldSupportCommonNeighbourPool (Finset.range b) c T.1) =
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b) c T.1) := by
    apply finiteDirectedCliqueCapacity_eq_of_offDiagonal_agreement
      E (finiteTaggedOldFutureEdge b E R sort c)
    intro x hx y hy hxy
    have hxB : x < b := Finset.mem_range.mp
      (Finset.mem_filter.mp hx).1
    have hyB : y < b := Finset.mem_range.mp
      (Finset.mem_filter.mp hy).1
    exact (finiteTaggedEdge_old_old
      b E R sort c x y hxB hyB).symm
  change ell - 1 -
      finiteDirectedCliqueCapacity
        (finiteTaggedOldFutureEdge b E R sort c)
        (oldSupportCommonNeighbourPool (Finset.range b) c T.1) =
    ell - 1 -
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b) c T.1)
  rw [hCapacity]

/-- The ENTIRE glued original prefix [0,b+card V) is a genuine
K_ell-free finite ordinary-L target, provided the old prefix
is free and ALL tagged future cliques obey the ACTUAL old-prefix
common-neighbour raw support bounds B_P(T).

The new table A itself is EXPLICITLY constructed by the encoder;
no unsupported relative embedding axiom is inserted. This is
the essential missing finite-compatibility check before applying
the pinned Henson extension and obtaining a common finite physical
witness front over a fixed old enumeration. -/
theorem finiteTagged_old_future_glued_KFree
    {d : Nat} {V : Type*} [Fintype V]
    (hd : 0 < d) (b ell : Nat)
    (E : Nat → Nat → Bool)
    (R : V → V → Bool) (sort : V → Fin d)
    (c : Nat → Fin d → Bool)
    (hOldFree : finitePoolCliqueCheck E ell (Finset.range b) = false)
    (hSmall : ∀ s : Finset V, IsFiniteTaggedClique R s → s.card < ell)
    (hBounds : ∀ s : Finset V, IsFiniteTaggedClique R s →
      ∀ T : IntegerGraphSupport d ell,
        (s.filter (fun v => sort v ∈ T.1)).card ≤
          finiteOldColumnRawBound E ell d (Finset.range b) c T) :
    finitePoolCliqueCheck
      (finiteTaggedOldFutureEdge b E R sort c)
      ell (Finset.range (b + Fintype.card V)) = false := by
  classical
  let A : Nat → Nat → Bool := finiteTaggedOldFutureEdge b E R sort c
  let P : Finset Nat := Finset.range b
  let W : Finset Nat := finiteTaggedFuturePool (V := V) b
  let tau : Nat → Fin d := finiteTaggedFutureSort hd sort b
  have hPFreeA : finitePoolCliqueCheck A ell P = false := by
    apply (finitePoolCliqueCheck_false_iff_reference E A ell P
      (by
        intro x hx y hy hxy
        exact (finiteTaggedEdge_old_old b E R sort c x y
          (Finset.mem_range.mp hx) (Finset.mem_range.mp hy)).symm)).mp
    exact hOldFree
  have hWFree : finitePoolCliqueCheck A ell W = false :=
    finiteTagged_future_KFree b ell E R sort c hSmall
  have hDisjoint : Disjoint P W := by
    apply Finset.disjoint_left.mpr
    intro x hxP hxW
    have hxOld : x < b := Finset.mem_range.mp hxP
    have hxLater : b ≤ x :=
      ((finiteTaggedFuturePool_mem_iff (V := V) b x).mp hxW).1
    omega
  have hColumns :
      ∀ p ∈ P, ∀ w ∈ W,
        A p w = c p (tau w) ∧ A w p = c p (tau w) := by
    intro p hp w hw
    change w ∈ ((Finset.univ : Finset V).image
      (finiteTaggedIndex b)) at hw
    obtain ⟨v,hv,hwv⟩ := Finset.mem_image.mp hw
    have hSort : tau w = sort v := by
      rw [← hwv]
      exact finiteTaggedFutureSort_index hd sort b v
    change finiteTaggedOldFutureEdge b E R sort c p w =
        c p (tau w) ∧
      finiteTaggedOldFutureEdge b E R sort c w p =
        c p (tau w)
    rw [hSort, ← hwv]
    exact ⟨finiteTaggedEdge_old_future b E R sort c p v
        (Finset.mem_range.mp hp),
      finiteTaggedEdge_future_old b E R sort c p v
        (Finset.mem_range.mp hp)⟩
  have hBoundsA : ∀ s : Finset Nat,
      s ⊆ W → IsDirectedCliqueOn A s →
      ∀ T : IntegerGraphSupport d ell,
        (s.filter (fun w => tau w ∈ T.1)).card ≤
          finiteOldColumnRawBound A ell d P c T := by
    intro s hsW hsClique T
    have hOriginal := finiteTagged_future_raw_bounds
      hd b E R sort c
      (finiteOldColumnRawBound E ell d (Finset.range b) c)
      hBounds s hsW hsClique T
    change (s.filter (fun w =>
      finiteTaggedFutureSort hd sort b w ∈ T.1)).card ≤
        finiteOldColumnRawBound A ell d (Finset.range b) c T
    rw [finiteTagged_old_reference_raw_bounds_eq b ell E R sort c T]
    exact hOriginal
  have hGlued := finiteOldFuture_free_of_all_raw_support
    A ell d P W tau c hDisjoint hColumns hPFreeA hWFree hBoundsA
  have hUnion : P ∪ W = Finset.range (b + Fintype.card V) := by
    ext z
    simp only [Finset.mem_union, Finset.mem_range]
    change (z < b ∨ z ∈ finiteTaggedFuturePool (V := V) b) ↔
      z < b + Fintype.card V
    rw [finiteTaggedFuturePool_mem_iff]
    omega
  rw [← hUnion]
  exact hGlued

#print axioms Kk.finiteTagged_clique_iff_image
#print axioms Kk.finiteTagged_future_subset_pullback_image
#print axioms Kk.finiteTagged_support_count_image
#print axioms Kk.finiteTagged_future_KFree
#print axioms Kk.finiteTagged_future_raw_bounds
#print axioms Kk.finiteTagged_old_reference_raw_bounds_eq
#print axioms Kk.finiteTagged_old_future_glued_KFree

end Kk
