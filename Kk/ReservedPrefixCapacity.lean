import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Powerset
import Lean.Elab.Tactic.Omega

namespace Kk

/-- Literal numerical-H real-copy generation gate for two copies of
  *distinct* original labels in a symmetric complete original clique. -/
def reservedCopyEdge (k : Nat) (x y : Nat × Nat) : Prop :=
  (x.1 < y.1 ∧ (x.2 < y.2 ∨ (x.2 = k ∧ y.2 = k))) ∨
  (y.1 < x.1 ∧ (y.2 < x.2 ∨ (x.2 = k ∧ y.2 = k)))

def IsReservedCopyClique (k : Nat) (s : Finset (Nat × Nat)) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y → reservedCopyEdge k x y

/-- The entire REAL-copy pool from one isolated reserved block up
  to and including label `a`, generation `g`. -/
def reservedPrefixPool (k a g : Nat) : Finset (Nat × Nat) :=
  ((Finset.range (a+1)).product (Finset.range (k+1))).filter
    (fun x => x.1 < a ∨ (x.1 = a ∧ x.2 ≤ g))

private theorem reservedCopyEdge_label_ne (k : Nat) (x y : Nat × Nat)
    (h : reservedCopyEdge k x y) : x.1 ≠ y.1 := by
  rcases h with h | h <;> omega

private theorem reservedCopyEdge_level_ne_below_top (k : Nat) (x y : Nat × Nat)
    (h : reservedCopyEdge k x y) (hxk : x.2 < k) : x.2 ≠ y.2 := by
  rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> rcases h with h | ⟨h1,h2⟩ <;> omega

private theorem reservedPrefixPool_bound (k a g : Nat)
    (x : Nat × Nat) (hx : x ∈ reservedPrefixPool k a g) :
    x.1 ≤ a ∧ x.2 ≤ k ∧ (x.1 = a → x.2 ≤ g) := by
  rcases x with ⟨b,h⟩
  have hh := Finset.mem_filter.mp hx
  have hprod := Finset.mem_product.mp hh.1
  have hb : b < a+1 := Finset.mem_range.mp hprod.1
  have ht : h < k+1 := Finset.mem_range.mp hprod.2
  -- Proof uses the prefix clause in the filter, not the product's cardinality.
  rcases hh.2 with ha | ⟨ha,hg⟩
  · exact ⟨by omega,by omega,by omega⟩
  · exact ⟨by omega,by omega,by omega⟩


/-- The original-label projection is injective on any clique, because
 copies of one original have no edges. -/
private theorem reservedClique_label_inj (k : Nat) (s : Finset (Nat × Nat))
    (hs : IsReservedCopyClique k s) :
    Set.InjOn (fun x : Nat × Nat => x.1) ↑s := by
  intro x hx y hy heq
  by_contra hne
  have hEdge := hs x hx y hy hne
  exact (reservedCopyEdge_label_ne k x y hEdge) heq

/-- Every clique in the prefix contains at most one copy for each of
  the a+1 original labels. -/
theorem reservedPrefixClique_card_le_succ (k a g : Nat)
    (s : Finset (Nat × Nat))
    (hs : s ⊆ reservedPrefixPool k a g)
    (hc : IsReservedCopyClique k s) : s.card ≤ a+1 := by
  have hMap : Set.MapsTo (fun x : Nat × Nat => x.1) ↑s
      (↑(Finset.range (a+1))) := by
    intro x hx
    have hb := (reservedPrefixPool_bound k a g x (hs hx)).1
    have hB : x.1 < a + 1 := Nat.lt_succ_of_le hb
    exact Finset.mem_coe.mpr (Finset.mem_range.mpr hB)
  have h := Finset.card_le_card_of_injOn (s:=s) (t:=Finset.range (a+1))
    (fun x : Nat × Nat => x.1) hMap (reservedClique_label_inj k s hc)
  simpa using h


/-- A strict lower generation of the pivot cannot be reached by a top-tie.
  Any adjacent earlier label must have an even earlier generation. -/
private theorem reservedEdge_before_nontop
    (k : Nat) (x y : Nat × Nat)
    (hxy : reservedCopyEdge k x y)
    (hLabel : x.1 < y.1) (hyTop : y.2 < k) : x.2 < y.2 := by
  rcases hxy with ⟨_, hg⟩ | ⟨hbad, _⟩
  · rcases hg with h | ⟨hx,hy⟩
    · exact h
    · omega
  · omega

/-- Sharp upper bound in the non-top case: if the pivot generation g is
  below its original label a, no clique reaches size a+1. -/
theorem reservedPrefixClique_card_le_label_of_generation_lt
    (k a g : Nat) (hka : a ≤ k) (hga : g < a)
    (s : Finset (Nat × Nat))
    (hs : s ⊆ reservedPrefixPool k a g)
    (hc : IsReservedCopyClique k s) : s.card ≤ a := by
  classical
  by_cases hHasPivot : ∃ y ∈ s, y.1 = a
  · obtain ⟨y,hy,hyLabel⟩ := hHasPivot
    have hyGen : y.2 ≤ g :=
      (reservedPrefixPool_bound k a g y (hs hy)).2.2 hyLabel
    have hyTop : y.2 < k := by omega
    let t := s.erase y
    have hMap : Set.MapsTo (fun x : Nat × Nat => x.2) ↑t
        (↑(Finset.range y.2)) := by
      intro x hx
      have hxSub : x ∈ s := (Finset.mem_erase.mp hx).2
      have hxNe : x ≠ y := (Finset.mem_erase.mp hx).1
      have hEdge := hc x hxSub y hy hxNe
      have hNotSameLabel := reservedCopyEdge_label_ne k x y hEdge
      have hLabelLe := (reservedPrefixPool_bound k a g x (hs hxSub)).1
      have hLabelLt : x.1 < y.1 := by omega
      have hGenLt := reservedEdge_before_nontop k x y hEdge hLabelLt hyTop
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr hGenLt)
    have hInj : Set.InjOn (fun x : Nat × Nat => x.2) ↑t := by
      intro x hx z hz hEqual
      by_contra hNe
      have hxSub : x ∈ s := (Finset.mem_erase.mp hx).2
      have hzSub : z ∈ s := (Finset.mem_erase.mp hz).2
      have hEdge := hc x hxSub z hzSub hNe
      have hxGen : x.2 < y.2 := Finset.mem_range.mp
        (Finset.mem_coe.mp (hMap hx))
      have hxTop : x.2 < k := by omega
      exact (reservedCopyEdge_level_ne_below_top k x z hEdge hxTop) hEqual
    have hBound : t.card ≤ y.2 := by
      have h := Finset.card_le_card_of_injOn (s:=t) (t:=Finset.range y.2)
        (fun x : Nat × Nat => x.2) hMap hInj
      simpa only [Finset.card_range] using h
    have hErase : t.card + 1 = s.card := Finset.card_erase_add_one hy
    omega
  · have hMap : Set.MapsTo (fun x : Nat × Nat => x.1) ↑s
        (↑(Finset.range a)) := by
      intro x hx
      have hLabelLe := (reservedPrefixPool_bound k a g x (hs hx)).1
      have hNe : x.1 ≠ a := by
        intro hxEq
        exact hHasPivot ⟨x, hx, hxEq⟩
      have hLabelLt : x.1 < a := by omega
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr hLabelLt)
    have h := Finset.card_le_card_of_injOn (s:=s) (t:=Finset.range a)
      (fun x : Nat × Nat => x.1) hMap (reservedClique_label_inj k s hc)
    simpa only [Finset.card_range] using h


/-- Choosing the top generation for each strictly earlier original
  gives a clique of exactly a vertices, even when g=0. -/
def reservedTopWitness (k a : Nat) : Finset (Nat × Nat) :=
  (Finset.range a).image (fun b => (b,k))

private theorem reservedTopWitness_card (k a : Nat) :
    (reservedTopWitness k a).card = a := by
  unfold reservedTopWitness
  have hInj : Function.Injective (fun b : Nat => (b,k)) := by
    intro b c heq
    exact congrArg Prod.fst heq
  rw [Finset.card_image_of_injective _ hInj, Finset.card_range]

private theorem reservedTopWitness_subset (k a g : Nat) :
    reservedTopWitness k a ⊆ reservedPrefixPool k a g := by
  intro x hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
  have hbLt : b < a := Finset.mem_range.mp hb
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    exact ⟨Finset.mem_range.mpr (by omega),
      Finset.mem_range.mpr (by omega)⟩
  · exact Or.inl hbLt

private theorem reservedTopWitness_clique (k a : Nat) :
    IsReservedCopyClique k (reservedTopWitness k a) := by
  intro x hx y hy hxy
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hy
  have hNe : b ≠ c := by
    intro hbc
    subst c
    exact hxy rfl
  by_cases hbc : b < c
  · exact Or.inl ⟨hbc, Or.inr ⟨rfl,rfl⟩⟩
  · have hcb : c < b := by omega
    exact Or.inr ⟨hcb, Or.inr ⟨rfl,rfl⟩⟩

/-- A staircase of earlier copies at generations 0,...,a-1,
  followed by the pivot at any generation g>=a, has a+1 elements. -/
def reservedStairWitness (a g : Nat) : Finset (Nat × Nat) :=
  (Finset.range (a+1)).image
    (fun b => (b, if b=a then g else b))

private theorem reservedStairWitness_card (a g : Nat) :
    (reservedStairWitness a g).card = a+1 := by
  unfold reservedStairWitness
  have hInj : Function.Injective
      (fun b : Nat => (b, if b=a then g else b)) := by
    intro b c heq
    exact congrArg Prod.fst heq
  rw [Finset.card_image_of_injective _ hInj, Finset.card_range]

private theorem reservedStairWitness_subset
    (k a g : Nat) (hag : a ≤ g) (hgk : g ≤ k) :
    reservedStairWitness a g ⊆ reservedPrefixPool k a g := by
  intro x hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
  have hbLe : b ≤ a := by have := Finset.mem_range.mp hb; omega
  by_cases hbA : b=a
  · subst b
    simp only [ite_true]
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega),
        Finset.mem_range.mpr (by omega)⟩,
      Or.inr ⟨rfl,le_refl _⟩⟩
  · have hbLt : b<a := by omega
    simp only [ite_eq_right hbA]
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega),
        Finset.mem_range.mpr (by omega)⟩,
      Or.inl hbLt⟩

private theorem stairLevel_strict
    (a g b c : Nat) (hbc : b<c) (hca : c≤a) (hag : a≤g) :
    (if b=a then g else b) < (if c=a then g else c) := by
  have hbA : b≠a := by omega
  by_cases hcA : c=a
  · simp only [ite_eq_right hbA, ite_eq_left hcA]
    omega
  · simp only [ite_eq_right hbA, ite_eq_right hcA]
    omega

private theorem reservedStairWitness_clique
    (k a g : Nat) (hag : a ≤ g) :
    IsReservedCopyClique k (reservedStairWitness a g) := by
  intro x hx y hy hxy
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hy
  have hbLe : b ≤ a := by have := Finset.mem_range.mp hb; omega
  have hcLe : c ≤ a := by have := Finset.mem_range.mp hc; omega
  have hNe : b ≠ c := by
    intro hbc
    subst c
    exact hxy rfl
  by_cases hbc : b < c
  · exact Or.inl ⟨hbc, Or.inl (stairLevel_strict a g b c hbc hcLe hag)⟩
  · have hcb : c < b := by omega
    exact Or.inr ⟨hcb, Or.inl (stairLevel_strict a g c b hcb hbLe hag)⟩

/-- Exact finite directed-clique capacity over all real H copies
  in the designated single-block prefix, using the actual generation gate. -/
noncomputable def reservedPrefixCapacity (k a g : Nat) : Nat := by
  classical
  exact ((reservedPrefixPool k a g).powerset.filter
    (IsReservedCopyClique k)).sup Finset.card

theorem reservedPrefixCapacity_eq (k a g : Nat)
    (hka : a ≤ k) (hgk : g ≤ k) :
    reservedPrefixCapacity k a g = if g < a then a else a+1 := by
  classical
  by_cases hga : g < a
  · rw [ite_eq_left hga]
    apply Nat.le_antisymm
    · unfold reservedPrefixCapacity
      apply Finset.sup_le
      intro s hs
      obtain ⟨hsSub,hc⟩ := Finset.mem_filter.mp hs
      exact reservedPrefixClique_card_le_label_of_generation_lt
        k a g hka hga s (Finset.mem_powerset.mp hsSub) hc
    · have hw : reservedTopWitness k a ∈
        ((reservedPrefixPool k a g).powerset.filter
          (IsReservedCopyClique k)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
          (reservedTopWitness_subset k a g), reservedTopWitness_clique k a⟩
      have hle := Finset.le_sup (f:=Finset.card) hw
      rw [reservedTopWitness_card] at hle
      exact hle
  · have hag : a ≤ g := by omega
    rw [ite_eq_right hga]
    apply Nat.le_antisymm
    · unfold reservedPrefixCapacity
      apply Finset.sup_le
      intro s hs
      obtain ⟨hsSub,hc⟩ := Finset.mem_filter.mp hs
      exact reservedPrefixClique_card_le_succ
        k a g s (Finset.mem_powerset.mp hsSub) hc
    · have hw : reservedStairWitness a g ∈
        ((reservedPrefixPool k a g).powerset.filter
          (IsReservedCopyClique k)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
          (reservedStairWitness_subset k a g hag hgk),
          reservedStairWitness_clique k a g hag⟩
      have hle := Finset.le_sup (f:=Finset.card) hw
      rw [reservedStairWitness_card] at hle
      exact hle

/-- Original formulation: every pivot in a block of length
  r <= k+1 satisfies the sharp height condition a <= k. -/
theorem reservedPrefixCapacity_eq_of_height
    (k r a g : Nat) (ha : a < r) (hr : r ≤ k+1) (hgk : g ≤ k) :
    reservedPrefixCapacity k a g = if g < a then a else a+1 := by
  have hka : a ≤ k := by omega
  exact reservedPrefixCapacity_eq k a g hka hgk

#print axioms reservedPrefixClique_card_le_label_of_generation_lt
#print axioms reservedPrefixCapacity_eq
#print axioms reservedPrefixCapacity_eq_of_height

end Kk
