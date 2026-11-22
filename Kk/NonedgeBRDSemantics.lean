import Kk.HensonEncoding
import Kk.HensonLeftDensityBridge
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Tactic

/-!
# Ordinary graph semantics for the big Ramsey degree of a nonedge

This file fixes the objects and quantifiers independently of any proposed
diary count. A nonedge copy is an unordered two-element set. Copies of the
ambient graph are images of arbitrary induced graph embeddings; their vertex
maps are not required to preserve the enumeration of `Nat`.

The ordinary Henson property is `CliqueFree 4` together with the full finite
one-point extension property. The stronger enumeration hypothesis
`Kk.OnePointLeftDense` implies that property, but is not its definition.

The final exactness criterion separates the two actual Ramsey obligations:
an upper bound for every finite colouring, and one unavoidable colouring.
No value of the degree, graph existence, diary canonization, or diary
unavoidability is assumed or asserted by this file.
-/

namespace Kk.NonedgeBRD

/-! ## Compatibility with ordinary simple graphs -/

/-- A loopless symmetric Boolean table defines an ordinary simple graph. -/
def graphOfBool (E : Nat → Nat → Bool)
    (hLoop : ∀ x, E x x = false) (hSymm : ∀ x y, E x y = E y x) :
    SimpleGraph Nat where
  Adj x y := E x y = true
  symm := ⟨by
    intro x y h
    rw [← hSymm x y]
    exact h⟩
  loopless := ⟨by
    intro x h
    simp [hLoop x] at h⟩

/-- The Boolean adjacency table of an ordinary simple graph. -/
noncomputable def boolAdj (G : SimpleGraph Nat) (x y : Nat) : Bool := by
  classical
  exact decide (G.Adj x y)

@[simp] theorem boolAdj_eq_true (G : SimpleGraph Nat) (x y : Nat) :
    boolAdj G x y = true ↔ G.Adj x y := by
  classical
  simp [boolAdj]

@[simp] theorem boolAdj_graphOfBool (E : Nat → Nat → Bool)
    (hLoop : ∀ x, E x x = false) (hSymm : ∀ x y, E x y = E y x) :
    boolAdj (graphOfBool E hLoop hSymm) = E := by
  funext x y
  cases h : E x y <;> simp [boolAdj, graphOfBool, h]

@[simp] theorem boolAdj_eq_false (G : SimpleGraph Nat) (x y : Nat) :
    boolAdj G x y = false ↔ ¬ G.Adj x y := by
  classical
  simp [boolAdj]

/-- Ordering a finite clique does not change which ordinary cliques exist. -/
theorem no_increasing_clique_iff_cliqueFree (G : SimpleGraph Nat) (n : Nat) :
    (¬ ∃ f : Fin n → Nat, StrictMono f ∧
      ∀ a b : Fin n, a ≠ b → G.Adj (f a) (f b)) ↔ G.CliqueFree n := by
  classical
  constructor
  · intro h s hs
    let f : Fin n ↪o Nat := s.orderEmbOfFin hs.card_eq
    apply h
    refine ⟨f, f.strictMono, ?_⟩
    intro a b hab
    exact hs.isClique (s.orderEmbOfFin_mem hs.card_eq a)
      (s.orderEmbOfFin_mem hs.card_eq b)
      (fun heq => hab (f.injective heq))
  · intro h
    rintro ⟨f, hf, hEdges⟩
    let e : Fin n ↪ Nat := ⟨f, hf.injective⟩
    apply h (Finset.univ.map e)
    refine ⟨?_, by simp⟩
    intro x hx y hy hxy
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hy
    exact hEdges a b (fun hab => hxy (congrArg e hab))

/-- The existing normalized forbidden family means exactly ordinary
`K_n`-freeness when supplied an ordinary simple graph's adjacency table.
Looplessness and symmetry are supplied by `SimpleGraph`, not extra axioms. -/
theorem normalized_avoidance_iff_cliqueFree
    (G : SimpleGraph Nat) (n : Nat) (hn : 2 ≤ n) :
    (∀ bad, bad ∈ Kk.hensonForbiddenFamily n hn →
      bad.Avoids (Kk.normalizedGraphModel (boolAdj G))) ↔ G.CliqueFree n := by
  classical
  rw [Kk.hensonForbiddenFamily_avoids_iff]
  have hLoop : ∀ i, boolAdj G i i = false := by simp
  have hSymm : ∀ x y, boolAdj G x y = boolAdj G y x := by
    intro x y
    simp only [boolAdj, G.adj_comm]
  simp only [hLoop, hSymm, implies_true, true_and, boolAdj_eq_true]
  exact no_increasing_clique_iff_cliqueFree G n

/-- In the opposite direction, the repository's Boolean forbidden-family
predicate is exactly ordinary clique-freeness of the resulting graph. -/
theorem graphOfBool_cliqueFree_iff (E : Nat → Nat → Bool)
    (hLoop : ∀ x, E x x = false) (hSymm : ∀ x y, E x y = E y x)
    (n : Nat) (hn : 2 ≤ n) :
    (graphOfBool E hLoop hSymm).CliqueFree n ↔
      ∀ bad, bad ∈ Kk.hensonForbiddenFamily n hn →
        bad.Avoids (Kk.normalizedGraphModel E) := by
  simpa using
    (normalized_avoidance_iff_cliqueFree (graphOfBool E hLoop hSymm) n hn).symm

/-! ## Full finite extension property, separate from an enumeration -/

/-- Every finite disjoint positive/negative adjacency request is realized,
provided its positive set contains no triangle. The new vertex is outside
both prescribed sets. No restriction is imposed on its enumeration index. -/
def HensonExtension (G : SimpleGraph Nat) : Prop :=
  ∀ U V : Finset Nat, Disjoint U V →
    (∀ s : Finset Nat, s ⊆ U → ¬ G.IsNClique 3 s) →
    ∃ x : Nat, x ∉ U ∪ V ∧
      (∀ u ∈ U, G.Adj x u) ∧ (∀ v ∈ V, ¬ G.Adj x v)

/-- A countably infinite `K_4`-free graph with the full Henson extension
property. The carrier `Nat` fixes countable infinitude. -/
def IsHenson4 (G : SimpleGraph Nat) : Prop :=
  G.CliqueFree 4 ∧ HensonExtension G

/-- The stronger left-dense enumeration assumption used in the construction
does imply the ordinary finite extension property. Its extra prescriptions
on all intervening vertices are not part of `HensonExtension`. -/
theorem hensonExtension_of_onePointLeftDense
    (G : SimpleGraph Nat) (hFree : G.CliqueFree 4)
    (hDense : Kk.OnePointLeftDense (boolAdj G) 4) : HensonExtension G := by
  classical
  intro U V hDisjoint hSafeU
  let front : Nat := (U ∪ V).sup id + 1
  let neighbour : Nat → Bool := fun x => decide (x ∈ U)
  have hBound : ∀ x ∈ U ∪ V, x < front := by
    intro x hx
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hx)
  have hOld : ¬ Kk.HasCliqueBelow (boolAdj G) front 4 := by
    rintro ⟨s, hCard, _, hClique⟩
    apply hFree s
    refine ⟨?_, hCard⟩
    intro x hx y hy hxy
    exact (boolAdj_eq_true G x y).mp (hClique x hx y hy hxy)
  have hNeighbours :
      ¬ Kk.HasNeighbourCliqueBelow (boolAdj G) front (4 - 1) neighbour := by
    rintro ⟨s, hCard, hMember, hClique⟩
    apply hSafeU s
    · intro x hx
      simpa [neighbour] using (hMember x hx).2
    · refine ⟨?_, by simpa using hCard⟩
      intro x hx y hy hxy
      exact (boolAdj_eq_true G x y).mp (hClique x hx y hy hxy)
  have hExtensionSafe :=
    (Kk.onePointGraph_cliqueFree_iff (boolAdj G) front 4 neighbour
      (by omega) hOld).2 hNeighbours
  obtain ⟨x, hx, hColumn⟩ := hDense front neighbour hExtensionSafe
  refine ⟨x, ?_, ?_, ?_⟩
  · intro hMember
    have := hBound x hMember
    omega
  · intro u hu
    have huFront := hBound u (Finset.mem_union_left V hu)
    have huX : u < x := by omega
    apply (boolAdj_eq_true G x u).mp
    simpa [huFront, neighbour, hu] using (hColumn u huX).2
  · intro v hv
    have hvFront := hBound v (Finset.mem_union_right U hv)
    have hvX : v < x := by omega
    have hvU : v ∉ U := by
      intro hvU
      exact Finset.disjoint_left.mp hDisjoint hvU hv
    apply (boolAdj_eq_false G x v).mp
    simpa [hvFront, neighbour, hvU] using (hColumn v hvX).2

theorem isHenson4_of_onePointLeftDense
    (G : SimpleGraph Nat) (hFree : G.CliqueFree 4)
    (hDense : Kk.OnePointLeftDense (boolAdj G) 4) : IsHenson4 G :=
  ⟨hFree, hensonExtension_of_onePointLeftDense G hFree hDense⟩

/-- The extension property ensures that the nonedge problem is nonvacuous. -/
theorem exists_nonedge_of_hensonExtension
    (G : SimpleGraph Nat) (hExtension : HensonExtension G) :
    ∃ a b : Nat, a ≠ b ∧ ¬ G.Adj a b := by
  have hSafe : ∀ s : Finset Nat, s ⊆ (∅ : Finset Nat) →
      ¬ G.IsNClique 3 s := by
    intro s hs hClique
    have hsEmpty := Finset.subset_empty.mp hs
    have hCard := hClique.card_eq
    simp [hsEmpty] at hCard
  obtain ⟨x, hx, _, hNonadj⟩ :=
    hExtension ∅ {0} (by simp) hSafe
  refine ⟨x, 0, ?_, hNonadj 0 (by simp)⟩
  simpa using hx

/-! ## Unordered copies and induced embeddings -/

/-- A copy of the two-vertex empty graph is an unordered two-element set
with no adjacency between any of its vertices. -/
def NonedgeCopy (G : SimpleGraph Nat) :=
  {s : Finset Nat // s.card = 2 ∧
    ∀ x ∈ s, ∀ y ∈ s, ¬ G.Adj x y}

namespace NonedgeCopy

variable {G H : SimpleGraph Nat}

/-- The unordered nonedge with specified distinct endpoints. -/
def pair (a b : Nat) (hNe : a ≠ b) (hNonadj : ¬ G.Adj a b) :
    NonedgeCopy G := by
  refine ⟨{a, b}, ?_, ?_⟩
  · simp [hNe]
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact G.irrefl
    · exact hNonadj
    · exact fun h => hNonadj h.symm
    · exact G.irrefl

/-- Swapping the two labels leaves the copy unchanged. -/
theorem pair_swap (a b : Nat) (hNe : a ≠ b) (hNonadj : ¬ G.Adj a b) :
    pair a b hNe hNonadj =
      pair b a hNe.symm (fun h => hNonadj h.symm) := by
  apply Subtype.ext
  exact Finset.pair_comm a b

/-- A labelled embedding of the actual two-vertex empty graph. -/
def pairEmbedding (a b : Nat) (hNe : a ≠ b) (hNonadj : ¬ G.Adj a b) :
    (⊥ : SimpleGraph (Fin 2)) ↪g G where
  toFun i := if i = 0 then a else b
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  map_rel_iff' := by
    have hNonadj' : ¬ G.Adj b a := fun h => hNonadj h.symm
    intro i j
    change G.Adj (if i = 0 then a else b) (if j = 0 then a else b) ↔ False
    fin_cases i <;> fin_cases j <;> simp [hNonadj, hNonadj']

@[simp] theorem pairEmbedding_zero
    (a b : Nat) (hNe : a ≠ b) (hNonadj : ¬ G.Adj a b) :
    pairEmbedding a b hNe hNonadj 0 = a := rfl

@[simp] theorem pairEmbedding_one
    (a b : Nat) (hNe : a ≠ b) (hNonadj : ¬ G.Adj a b) :
    pairEmbedding a b hNe hNonadj 1 = b := rfl

/-- Forget the labels of an embedding of the empty graph on `Fin 2`. -/
def ofEmbedding (e : (⊥ : SimpleGraph (Fin 2)) ↪g G) : NonedgeCopy G :=
  pair (e 0) (e 1) (fun h => by
    have := e.injective h
    norm_num at this) (fun h => e.map_adj_iff.mp h)

@[simp] theorem ofEmbedding_pairEmbedding
    (a b : Nat) (hNe : a ≠ b) (hNonadj : ¬ G.Adj a b) :
    ofEmbedding (pairEmbedding a b hNe hNonadj) = pair a b hNe hNonadj := by
  apply Subtype.ext
  rfl

theorem ofEmbedding_eq_pair_iff
    (a b : Nat) (hNe : a ≠ b) (hNonadj : ¬ G.Adj a b)
    (e : (⊥ : SimpleGraph (Fin 2)) ↪g G) :
    ofEmbedding e = pair a b hNe hNonadj ↔
      e = pairEmbedding a b hNe hNonadj ∨
      e = pairEmbedding b a hNe.symm (fun h => hNonadj h.symm) := by
  constructor
  · intro h
    have hFinsets : ({e 0, e 1} : Finset Nat) = {a, b} :=
      congrArg Subtype.val h
    have hSets : ({e 0, e 1} : Set Nat) = {a, b} := by
      simpa only [Finset.coe_pair] using
        congrArg (fun s : Finset Nat => (s : Set Nat)) hFinsets
    rcases Set.pair_eq_pair_iff.mp hSets with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · left
      ext i
      fin_cases i
      · simpa using ha
      · simpa using hb
    · right
      ext i
      fin_cases i
      · simpa using hb
      · simpa using ha
  · rintro (rfl | rfl)
    · exact ofEmbedding_pairEmbedding a b hNe hNonadj
    · rw [ofEmbedding_pairEmbedding]
      exact (pair_swap a b hNe hNonadj).symm

/-- Every unordered nonedge has exactly two distinct labelled embeddings
of `Fin 2`. Thus the public copy convention does not count both labels. -/
theorem exactly_two_labelled_realizations (B : NonedgeCopy G) :
    ∃ e₀ e₁ : (⊥ : SimpleGraph (Fin 2)) ↪g G, e₀ ≠ e₁ ∧
      ∀ e : (⊥ : SimpleGraph (Fin 2)) ↪g G,
        ofEmbedding e = B ↔ e = e₀ ∨ e = e₁ := by
  obtain ⟨a, b, hab, hB⟩ := Finset.card_eq_two.mp B.property.1
  have ha : a ∈ B.val := by simp [hB]
  have hb : b ∈ B.val := by simp [hB]
  have hNonadj := B.property.2 a ha b hb
  have hPair : pair a b hab hNonadj = B := by
    apply Subtype.ext
    exact hB.symm
  refine ⟨pairEmbedding a b hab hNonadj,
    pairEmbedding b a hab.symm (fun h => hNonadj h.symm), ?_, ?_⟩
  · intro h
    have hZero := congrArg
      (fun e : (⊥ : SimpleGraph (Fin 2)) ↪g G => e 0) h
    exact hab (by simpa using hZero)
  · intro e
    rw [← hPair]
    exact ofEmbedding_eq_pair_iff a b hab hNonadj e

/-- Images of nonedges under an induced graph embedding are nonedges.
The reverse implication in `map_adj_iff` is essential here. -/
def map (f : G ↪g H) (A : NonedgeCopy G) : NonedgeCopy H := by
  refine ⟨A.val.map f.toEmbedding, ?_, ?_⟩
  · simpa using A.property.1
  · intro x hx y hy hAdj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    exact A.property.2 a ha b hb (f.map_adj_iff.mp hAdj)

@[simp] theorem map_comp {J : SimpleGraph Nat}
    (f : G ↪g H) (g : H ↪g J) (A : NonedgeCopy G) :
    map g (map f A) = map (g.comp f) A := by
  apply Subtype.ext
  simp only [map, Finset.map_map]
  rfl

@[simp] theorem map_pair (f : G ↪g H)
    (a b : Nat) (hNe : a ≠ b) (hNonadj : ¬ G.Adj a b) :
    map f (pair a b hNe hNonadj) =
      pair (f a) (f b) (fun h => hNe (f.injective h))
        (fun h => hNonadj (f.map_adj_iff.mp h)) := by
  apply Subtype.ext
  simp [map, pair]

/-- All vertices of this copy lie in the embedding's range. -/
def InRange (f : G ↪g H) (A : NonedgeCopy H) : Prop :=
  ∀ x ∈ A.val, ∃ y, f y = x

theorem map_inRange (f : G ↪g H) (A : NonedgeCopy G) :
    InRange f (map f A) := by
  intro x hx
  obtain ⟨y, _, hy⟩ := Finset.mem_map.mp hx
  exact ⟨y, hy⟩

/-- Parameterizing copies by their preimages misses no nonedge contained
in an induced self-copy's vertex set. -/
theorem exists_map_iff_inRange (f : G ↪g H) (B : NonedgeCopy H) :
    (∃ A : NonedgeCopy G, map f A = B) ↔ InRange f B := by
  constructor
  · rintro ⟨A, rfl⟩
    exact map_inRange f A
  · intro hRange
    obtain ⟨x, y, hxy, hB⟩ := Finset.card_eq_two.mp B.property.1
    have hx : x ∈ B.val := by simp [hB]
    have hy : y ∈ B.val := by simp [hB]
    obtain ⟨a, ha⟩ := hRange x hx
    obtain ⟨b, hb⟩ := hRange y hy
    have hab : a ≠ b := by
      intro h
      apply hxy
      rw [← ha, ← hb, h]
    have hNonadj : ¬ G.Adj a b := by
      intro h
      apply B.property.2 x hx y hy
      simpa [ha, hb] using f.map_adj_iff.mpr h
    refine ⟨pair a b hab hNonadj, ?_⟩
    apply Subtype.ext
    simp [map, pair, ha, hb, hB]

end NonedgeCopy

theorem nonempty_nonedgeCopy_of_hensonExtension
    (G : SimpleGraph Nat) (hExtension : HensonExtension G) :
    Nonempty (NonedgeCopy G) := by
  obtain ⟨a, b, hab, hNonadj⟩ :=
    exists_nonedge_of_hensonExtension G hExtension
  exact ⟨NonedgeCopy.pair a b hab hNonadj⟩

/-! ## Exact big Ramsey quantifiers -/

/-- At most `t` colours remain on some induced copy of the whole ambient
graph, for every finite colouring of all unordered nonedges.

The variable `k` is universally quantified and is not a proposed type count.
`G ↪g G` preserves and reflects adjacency; no monotonicity is assumed. -/
def DegreeLE (G : SimpleGraph Nat) (t : Nat) : Prop :=
  ∀ k : Nat, ∀ c : NonedgeCopy G → Fin k,
    ∃ f : G ↪g G, ∃ palette : Finset (Fin k),
      palette.card ≤ t ∧
      ∀ A : NonedgeCopy G, c (NonedgeCopy.map f A) ∈ palette

/-- Equivalent formulation that explicitly considers every nonedge
contained in the range of the embedding. -/
def DegreeLEOnRanges (G : SimpleGraph Nat) (t : Nat) : Prop :=
  ∀ k : Nat, ∀ c : NonedgeCopy G → Fin k,
    ∃ f : G ↪g G, ∃ palette : Finset (Fin k),
      palette.card ≤ t ∧
      ∀ B : NonedgeCopy G, NonedgeCopy.InRange f B → c B ∈ palette

theorem degreeLE_iff_onRanges (G : SimpleGraph Nat) (t : Nat) :
    DegreeLE G t ↔ DegreeLEOnRanges G t := by
  constructor
  · intro h k c
    obtain ⟨f, palette, hCard, hColours⟩ := h k c
    refine ⟨f, palette, hCard, ?_⟩
    intro B hB
    obtain ⟨A, rfl⟩ := (NonedgeCopy.exists_map_iff_inRange f B).mpr hB
    exact hColours A
  · intro h k c
    obtain ⟨f, palette, hCard, hColours⟩ := h k c
    exact ⟨f, palette, hCard,
      fun A => hColours _ (NonedgeCopy.map_inRange f A)⟩

/-- The usual substructure formulation: an induced subgraph isomorphic
to `G`, and all unordered nonedges inside its vertex set. -/
def DegreeLEOnSubcopies (G : SimpleGraph Nat) (t : Nat) : Prop :=
  ∀ k : Nat, ∀ c : NonedgeCopy G → Fin k,
    ∃ S : Set Nat, Nonempty (G ≃g G.induce S) ∧
      ∃ palette : Finset (Fin k), palette.card ≤ t ∧
        ∀ B : NonedgeCopy G, (∀ x ∈ B.val, x ∈ S) → c B ∈ palette

theorem degreeLE_iff_onSubcopies (G : SimpleGraph Nat) (t : Nat) :
    DegreeLE G t ↔ DegreeLEOnSubcopies G t := by
  constructor
  · intro h k c
    obtain ⟨f, palette, hCard, hColours⟩ :=
      (degreeLE_iff_onRanges G t).mp h k c
    exact ⟨Set.range f, ⟨f.isoInduceRange⟩, palette, hCard, hColours⟩
  · intro h k c
    obtain ⟨S, ⟨e⟩, palette, hCard, hColours⟩ := h k c
    let f : G ↪g G := (SimpleGraph.Embedding.induce S).comp e.toEmbedding
    refine ⟨f, palette, hCard, ?_⟩
    intro A
    apply hColours
    intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
    exact (e a).property

/-- Mutual induced embeddability transports this degree bound. In
particular no choice of enumeration can alter the bound. -/
theorem degreeLE_of_mutual_embeddings
    {G H : SimpleGraph Nat} (i : G ↪g H) (j : H ↪g G) (t : Nat)
    (h : DegreeLE G t) : DegreeLE H t := by
  intro k c
  obtain ⟨f, palette, hCard, hColours⟩ :=
    h k (fun A => c (NonedgeCopy.map i A))
  refine ⟨i.comp (f.comp j), palette, hCard, ?_⟩
  intro A
  simpa only [NonedgeCopy.map_comp] using hColours (NonedgeCopy.map j A)

theorem degreeLE_iso_iff {G H : SimpleGraph Nat}
    (e : G ≃g H) (t : Nat) : DegreeLE G t ↔ DegreeLE H t := by
  constructor
  · exact degreeLE_of_mutual_embeddings e.toEmbedding e.symm.toEmbedding t
  · exact degreeLE_of_mutual_embeddings e.symm.toEmbedding e.toEmbedding t

/-- `t` is the least nonedge big Ramsey bound. No numeric answer is
built into this definition. -/
def DegreeEq (G : SimpleGraph Nat) (t : Nat) : Prop :=
  DegreeLE G t ∧ ∀ s : Nat, s < t → ¬ DegreeLE G s

theorem degreeEq_iso_iff {G H : SimpleGraph Nat}
    (e : G ≃g H) (t : Nat) : DegreeEq G t ↔ DegreeEq H t := by
  constructor
  · intro h
    refine ⟨(degreeLE_iso_iff e t).mp h.1, ?_⟩
    intro s hs hBound
    exact h.2 s hs ((degreeLE_iso_iff e s).mpr hBound)
  · intro h
    refine ⟨(degreeLE_iso_iff e t).mpr h.1, ?_⟩
    intro s hs hBound
    exact h.2 s hs ((degreeLE_iso_iff e s).mp hBound)

/-- Every one of the `t` colours occurs inside every induced self-copy.
This is an infinite unavoidability assertion, not a finite type count. -/
def Unavoidable (G : SimpleGraph Nat) (t : Nat)
    (c : NonedgeCopy G → Fin t) : Prop :=
  ∀ f : G ↪g G,
    Function.Surjective (fun A : NonedgeCopy G => c (NonedgeCopy.map f A))

theorem degreeLE_mono (G : SimpleGraph Nat) {s t : Nat}
    (h : DegreeLE G s) (hst : s ≤ t) : DegreeLE G t := by
  intro k c
  obtain ⟨f, palette, hCard, hColours⟩ := h k c
  exact ⟨f, palette, hCard.trans hst, hColours⟩

/-- An unavoidable finite colouring gives an actual lower bound on every
Ramsey bound. Merely counting its possible values would not suffice. -/
theorem unavoidable_le_degree_bound
    (G : SimpleGraph Nat) {t s : Nat}
    (c : NonedgeCopy G → Fin t) (hUnavoidable : Unavoidable G t c)
    (hBound : DegreeLE G s) : t ≤ s := by
  obtain ⟨f, palette, hCard, hColours⟩ := hBound t c
  have hAll : Finset.univ ⊆ palette := by
    intro colour _
    obtain ⟨A, hA⟩ := hUnavoidable f colour
    rw [← hA]
    exact hColours A
  have hCount := Finset.card_le_card hAll
  simpa using hCount.trans hCard

/-- Honest exactness interface. A numerical enumeration can be connected
to this theorem only after supplying both infinite Ramsey obligations. -/
theorem degreeEq_of_upper_and_unavoidable
    (G : SimpleGraph Nat) (t : Nat)
    (hUpper : DegreeLE G t)
    (c : NonedgeCopy G → Fin t) (hUnavoidable : Unavoidable G t c) :
    DegreeEq G t := by
  refine ⟨hUpper, ?_⟩
  intro s hs hBound
  have := unavoidable_le_degree_bound G c hUnavoidable hBound
  omega

theorem degreeEq_unique (G : SimpleGraph Nat) {s t : Nat}
    (hs : DegreeEq G s) (ht : DegreeEq G t) : s = t := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ht.2 s hlt hs.1
  · exact hs.2 t hgt ht.1

end Kk.NonedgeBRD
