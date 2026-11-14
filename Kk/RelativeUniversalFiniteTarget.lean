import Kk.FiniteTaggedRelativeKFree
import Kk.UniversalFutureExactProfile
import Mathlib.Tactic

/-!
# Track A: literal finite universal relative K-free target over fixed old prefix

English proof and 14 hostile checks committed FIRST:
  docs/relative_universal_finite_target_english_audit.md

Take the actual old-original prefix [0,b), compute its exact full
typed raw age B_P(T)=ell-1-cliqueCap(common old c-neighbours(T)),
and take the SUBTYPE of the already checked finite
universalWitnessFuture d ell B_P vertices.

This module verifies that the subtype's inherited ordinary graph:
* is symmetric and irreflexive;
* is K_ell-free and obeys every B_P support bound;
* realizes every feasible normalized clique weight vector, all
  support counts simultaneously, in the SAME finite future.

The explicit tagged Nat encoder and the generic raw-bound gluing
theorem then yield a genuinely K_ell-free FULL old-plus-future
target on [0,b+card V). This is a constructed compatible
relative finite L graph, not an existential relative-universality
axiom.

The subsequent physical pinned Henson embedding is a separate
checked theorem in Track A PR #137. No infinite resolved diary,
numerical-H+ auxiliary Kpt E/B3, or common labelled source orbit
is asserted here.
-/

namespace Kk

/-- Only vertices actually in the verified common finite universal
future are retained. This handles arbitrary raw B with zero values
and does not add any spurious future original. -/
abbrev RelativeUniversalTaggedVertex (d ell : Nat)
    (B : IntegerGraphSupport d ell → Nat) :=
  {u : UniversalWitnessVertex d ell //
    u ∈ universalWitnessFuture d ell B}

/-- The subtype of a finite witnessed pool is finite, even when its
underlying set is empty. No default vertex is chosen. -/
noncomputable instance relativeUniversalTaggedFintype
    (d ell : Nat) (B : IntegerGraphSupport d ell → Nat) :
    Fintype (RelativeUniversalTaggedVertex d ell B) := by
  classical
  infer_instance

/-- Actual future ordinary-L edge, inherited with ALL bits from
the previously verified universal disjoint-clique graph. -/
def relativeUniversalTaggedEdge
    (d ell : Nat) (B : IntegerGraphSupport d ell → Nat)
    (v w : RelativeUniversalTaggedVertex d ell B) : Bool :=
  universalWitnessEdge v.1 w.1

/-- The genuine witness vertex's sort is the first coordinate of
its dependent integer witness slot, including multiplicities. -/
def relativeUniversalTaggedSort
    (d ell : Nat) (B : IntegerGraphSupport d ell → Nat)
    (v : RelativeUniversalTaggedVertex d ell B) : Fin d :=
  v.1.2.1

theorem relativeUniversalTaggedEdge_symmetric
    (d ell : Nat) (B : IntegerGraphSupport d ell → Nat)
    (v w : RelativeUniversalTaggedVertex d ell B) :
    relativeUniversalTaggedEdge d ell B v w =
      relativeUniversalTaggedEdge d ell B w v :=
  universalWitnessEdge_symmetric v.1 w.1

theorem relativeUniversalTaggedEdge_irreflexive
    (d ell : Nat) (B : IntegerGraphSupport d ell → Nat)
    (v : RelativeUniversalTaggedVertex d ell B) :
    relativeUniversalTaggedEdge d ell B v v = false :=
  universalWitnessEdge_irreflexive v.1

/-- Every directed clique in the actual finite subtype corresponds
exactly to a directed clique in the original verified Sigma future,
using the injective underlying-vertex map. -/
theorem relativeUniversalTagged_clique_iff_image
    (d ell : Nat) (B : IntegerGraphSupport d ell → Nat)
    (s : Finset (RelativeUniversalTaggedVertex d ell B)) :
    IsFiniteTaggedClique (relativeUniversalTaggedEdge d ell B) s ↔
      IsUniversalWitnessClique (s.image Subtype.val) := by
  classical
  constructor
  · intro hc x hx y hy hxy
    obtain ⟨v,hv,hvx⟩ := Finset.mem_image.mp hx
    obtain ⟨w,hw,hwy⟩ := Finset.mem_image.mp hy
    have hvw : v ≠ w := by
      intro h
      subst w
      exact hxy (hvx.symm.trans hwy)
    have hV : relativeUniversalTaggedEdge d ell B v w = true :=
      hc v hv w hw hvw
    change universalWitnessEdge v.1 w.1 = true at hV
    simpa only [hvx,hwy] using hV
  · intro hc v hv w hw hvw
    have hValNe : v.1 ≠ w.1 := by
      intro h
      exact hvw (Subtype.ext h)
    have hV := hc v.1
      (Finset.mem_image.mpr ⟨v,hv,rfl⟩)
      w.1 (Finset.mem_image.mpr ⟨w,hw,rfl⟩) hValNe
    exact hV

/-- Every actual labelled sort count of a tagged-clique subset
equals the count of the underlying Sigma future. -/
theorem relativeUniversalTagged_image_support_count_eq
    (d ell : Nat) (B : IntegerGraphSupport d ell → Nat)
    (s : Finset (RelativeUniversalTaggedVertex d ell B))
    (T : IntegerGraphSupport d ell) :
    ((s.image Subtype.val).filter (fun u => u.2.1 ∈ T.1)).card =
      (s.filter (fun v => relativeUniversalTaggedSort d ell B v ∈ T.1)).card := by
  classical
  have hFilter :
      (s.image Subtype.val).filter (fun u => u.2.1 ∈ T.1) =
      (s.filter (fun v => relativeUniversalTaggedSort d ell B v ∈ T.1)).image
        Subtype.val := by
    ext u
    constructor
    · intro hu
      obtain ⟨hImage,hSort⟩ := Finset.mem_filter.mp hu
      obtain ⟨v,hv,hvu⟩ := Finset.mem_image.mp hImage
      subst u
      have hvSort : relativeUniversalTaggedSort d ell B v ∈ T.1 := by
        simpa only [relativeUniversalTaggedSort] using hSort
      exact Finset.mem_image.mpr
        ⟨v,Finset.mem_filter.mpr ⟨hv,hvSort⟩,rfl⟩
    · intro hu
      obtain ⟨v,hv,hvu⟩ := Finset.mem_image.mp hu
      obtain ⟨hvs,hvSort⟩ := Finset.mem_filter.mp hv
      subst u
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨v,hvs,rfl⟩,?_⟩
      simpa only [relativeUniversalTaggedSort] using hvSort
  rw [hFilter]
  exact Finset.card_image_of_injective _ Subtype.val_injective

/-- Every actual finite tagged clique remains smaller than ell;
the inherited graph cannot accidentally connect different
feasible normalized witness components. -/
theorem relativeUniversalTagged_clique_card_lt
    (d ell : Nat) (hell : 0 < ell)
    (B : IntegerGraphSupport d ell → Nat)
    (s : Finset (RelativeUniversalTaggedVertex d ell B))
    (hc : IsFiniteTaggedClique
      (relativeUniversalTaggedEdge d ell B) s) :
    s.card < ell := by
  classical
  have hSub : s.image Subtype.val ⊆ universalWitnessFuture d ell B := by
    intro u hu
    obtain ⟨v,hv,hvu⟩ := Finset.mem_image.mp hu
    exact hvu ▸ v.2
  have hImageClique :=
    (relativeUniversalTagged_clique_iff_image d ell B s).mp hc
  have hBound := universalWitnessFuture_clique_card_lt
    d ell hell B (s.image Subtype.val) hSub hImageClique
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hBound
  exact hBound

/-- Every clique in the SAME finite universal tagged subtype obeys
EVERY raw support bound B(T), not just the selected one. -/
theorem relativeUniversalTagged_clique_respects_raw
    (d ell : Nat) (hell : 0 < ell)
    (B : IntegerGraphSupport d ell → Nat)
    (s : Finset (RelativeUniversalTaggedVertex d ell B))
    (hc : IsFiniteTaggedClique
      (relativeUniversalTaggedEdge d ell B) s)
    (T : IntegerGraphSupport d ell) :
    (s.filter (fun v =>
      relativeUniversalTaggedSort d ell B v ∈ T.1)).card ≤ B T := by
  classical
  have hSub : s.image Subtype.val ⊆ universalWitnessFuture d ell B := by
    intro u hu
    obtain ⟨v,hv,hvu⟩ := Finset.mem_image.mp hu
    exact hvu ▸ v.2
  have hImageClique :=
    (relativeUniversalTagged_clique_iff_image d ell B s).mp hc
  have hRaw := universalWitnessFuture_clique_respects_raw
    d ell hell B (s.image Subtype.val) hSub hImageClique T
  rw [relativeUniversalTagged_image_support_count_eq] at hRaw
  exact hRaw

/-- For each B-feasible normalized vector w, the actual subtype
component tagged by w is a directed clique with EXACTLY the
prescribed labelled counts for ALL nonempty supports simultaneously.
All those components belong to ONE common finite future subtype. -/
theorem relativeUniversalTagged_realizes_every_feasible
    (d ell : Nat) (hell : 0 < ell)
    (B : IntegerGraphSupport d ell → Nat)
    (w : IntegerCliqueWeights d ell)
    (hw : w ∈ feasibleIntegerCliqueVectors d ell B) :
    ∃ s : Finset (RelativeUniversalTaggedVertex d ell B),
      IsFiniteTaggedClique (relativeUniversalTaggedEdge d ell B) s ∧
      (∀ T : IntegerGraphSupport d ell,
        (s.filter (fun v =>
          relativeUniversalTaggedSort d ell B v ∈ T.1)).card =
            integerCliqueOnSupport w T) := by
  classical
  obtain ⟨hCompSub,hCompClique,hCompCounts,_⟩ :=
    universalWitnessFuture_realizes_every_feasible d ell hell B w hw
  let s : Finset (RelativeUniversalTaggedVertex d ell B) :=
    (Finset.univ : Finset (RelativeUniversalTaggedVertex d ell B)).filter
      (fun v => v.1.1 = w)
  have hImage : s.image Subtype.val = universalWitnessComponent w := by
    ext u
    constructor
    · intro hu
      obtain ⟨v,hv,hvu⟩ := Finset.mem_image.mp hu
      have hWeight := (Finset.mem_filter.mp hv).2
      apply (universalWitness_mem_component_iff w u).2
      simpa only [← hvu] using hWeight
    · intro hu
      let v : RelativeUniversalTaggedVertex d ell B := ⟨u,hCompSub hu⟩
      apply Finset.mem_image.mpr
      refine ⟨v,?_,rfl⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,
        (universalWitness_mem_component_iff w u).mp hu⟩
  have hsClique : IsFiniteTaggedClique
      (relativeUniversalTaggedEdge d ell B) s := by
    apply (relativeUniversalTagged_clique_iff_image d ell B s).mpr
    rw [hImage]
    exact hCompClique
  refine ⟨s,hsClique,?_⟩
  intro T
  have hCounts := relativeUniversalTagged_image_support_count_eq
    d ell B s T
  rw [hImage] at hCounts
  exact hCounts.symm.trans (hCompCounts T)

/-- The CONSTRUCTED old-plus-universal-future finite Nat table is
K_ell-free over any fixed K_ell-free old prefix, with B being
the ACTUAL raw common-old-neighbour clique-capacity function.

No positivity of raw B is required: zero bounds remove infeasible
future witness components instead of making the joined target unsafe. -/
theorem finiteOldPrefix_universal_tagged_target_KFree
    (d ell b : Nat) (hell : 2 ≤ ell) (hd : 0 < d)
    (E : Nat → Nat → Bool)
    (c : Nat → Fin d → Bool)
    (hOldFree : finitePoolCliqueCheck E ell (Finset.range b) = false) :
    let B := finiteOldColumnRawBound E ell d (Finset.range b) c
    let V := RelativeUniversalTaggedVertex d ell B
    finitePoolCliqueCheck
      (finiteTaggedOldFutureEdge b E
        (relativeUniversalTaggedEdge d ell B)
        (relativeUniversalTaggedSort d ell B) c)
      ell (Finset.range (b + Fintype.card V)) = false := by
  classical
  exact finiteTagged_old_future_glued_KFree
    hd b ell E
    (relativeUniversalTaggedEdge d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c))
    (relativeUniversalTaggedSort d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c))
    c hOldFree
    (fun s hs => relativeUniversalTagged_clique_card_lt
      d ell (by omega)
      (finiteOldColumnRawBound E ell d (Finset.range b) c) s hs)
    (fun s hs T => relativeUniversalTagged_clique_respects_raw
      d ell (by omega)
      (finiteOldColumnRawBound E ell d (Finset.range b) c) s hs T)

/-- One and the SAME explicitly constructed old-plus-future target
contains literal Nat-coded copies of EVERY feasible labelled clique
vector, with correct counts on EVERY support simultaneously. -/
theorem finiteOldPrefix_universal_tagged_target_realizes_every
    (d ell b : Nat) (hell : 2 ≤ ell) (hd : 0 < d)
    (E : Nat → Nat → Bool) (c : Nat → Fin d → Bool)
    (B : IntegerGraphSupport d ell → Nat)
    (w : IntegerCliqueWeights d ell)
    (hw : w ∈ feasibleIntegerCliqueVectors d ell B) :
    let V := RelativeUniversalTaggedVertex d ell B
    let W : Finset Nat := finiteTaggedFuturePool (V := V) b
    let A : Nat → Nat → Bool := finiteTaggedOldFutureEdge b E
      (relativeUniversalTaggedEdge d ell B)
      (relativeUniversalTaggedSort d ell B) c
    let tau : Nat → Fin d :=
      finiteTaggedFutureSort hd (relativeUniversalTaggedSort d ell B) b
    ∃ s : Finset Nat,
      s ⊆ W ∧ IsDirectedCliqueOn A s ∧
      (∀ T : IntegerGraphSupport d ell,
        (s.filter (fun z => tau z ∈ T.1)).card =
          integerCliqueOnSupport w T) := by
  classical
  obtain ⟨s,hsClique,hsCounts⟩ :=
    relativeUniversalTagged_realizes_every_feasible
      d ell (by omega) B w hw
  refine ⟨s.image (finiteTaggedIndex b),?_,?_,?_⟩
  · intro z hz
    obtain ⟨v,hv,hvz⟩ := Finset.mem_image.mp hz
    change z ∈ finiteTaggedFuturePool
      (V := RelativeUniversalTaggedVertex d ell B) b
    change z ∈ ((Finset.univ :
      Finset (RelativeUniversalTaggedVertex d ell B)).image
        (finiteTaggedIndex b))
    exact Finset.mem_image.mpr ⟨v,Finset.mem_univ _,hvz⟩
  · exact (finiteTagged_clique_iff_image b E
      (relativeUniversalTaggedEdge d ell B)
      (relativeUniversalTaggedSort d ell B) c s).mp hsClique
  · intro T
    exact (finiteTagged_support_count_image hd b
      (relativeUniversalTaggedSort d ell B) s T).trans
      (hsCounts T)

/-- The constructed finite future has NO spurious supported clique
profiles: every literal Nat-coded future clique obeys the same
complete raw bounds B as its tagged universal source. -/
theorem finiteOldPrefix_universal_tagged_target_no_spurious
    (d ell b : Nat) (hell : 2 ≤ ell) (hd : 0 < d)
    (E : Nat → Nat → Bool) (c : Nat → Fin d → Bool)
    (B : IntegerGraphSupport d ell → Nat) :
    let V := RelativeUniversalTaggedVertex d ell B
    let W : Finset Nat := finiteTaggedFuturePool (V := V) b
    let A : Nat → Nat → Bool := finiteTaggedOldFutureEdge b E
      (relativeUniversalTaggedEdge d ell B)
      (relativeUniversalTaggedSort d ell B) c
    let tau : Nat → Fin d :=
      finiteTaggedFutureSort hd (relativeUniversalTaggedSort d ell B) b
    ∀ s : Finset Nat, s ⊆ W → IsDirectedCliqueOn A s →
      ∀ T : IntegerGraphSupport d ell,
        (s.filter (fun z => tau z ∈ T.1)).card ≤ B T := by
  classical
  exact finiteTagged_future_raw_bounds hd b E
    (relativeUniversalTaggedEdge d ell B)
    (relativeUniversalTaggedSort d ell B) c B
    (fun s hs T => relativeUniversalTagged_clique_respects_raw
      d ell (by omega) B s hs T)

#print axioms Kk.relativeUniversalTaggedEdge_symmetric
#print axioms Kk.relativeUniversalTaggedEdge_irreflexive
#print axioms Kk.relativeUniversalTagged_clique_iff_image
#print axioms Kk.relativeUniversalTagged_image_support_count_eq
#print axioms Kk.relativeUniversalTagged_clique_card_lt
#print axioms Kk.relativeUniversalTagged_clique_respects_raw
#print axioms Kk.relativeUniversalTagged_realizes_every_feasible
#print axioms Kk.finiteOldPrefix_universal_tagged_target_KFree
#print axioms Kk.finiteOldPrefix_universal_tagged_target_realizes_every
#print axioms Kk.finiteOldPrefix_universal_tagged_target_no_spurious

end Kk
