import Kk.NonedgeBRDSemantics

/-!
# Universality from the ordinary Henson extension property

Every `K_4`-free graph on `Nat` embeds as an induced subgraph of every
graph on `Nat` with the ordinary Henson finite extension property.
No source extension property, target left-density, or monotonicity of
the embedding is used. Mutual embeddability then identifies the nonedge
degree predicates of all graphs satisfying `IsHenson4`.

English proof and prior audit: `docs/henson_universality_20261122.md`.
-/

namespace Kk.HensonUniversality

open Kk.NonedgeBRD

/-- An induced embedding of the finite source prefix. Values outside
the prefix are ignored until they are assigned at a later stage. -/
structure PrefixEmbedding (G H : SimpleGraph Nat) (n : Nat) where
  value : Nat → Nat
  injective : ∀ i, i < n → ∀ j, j < n → value i = value j → i = j
  adj_iff : ∀ i, i < n → ∀ j, j < n →
    (H.Adj (value i) (value j) ↔ G.Adj i j)

namespace PrefixEmbedding

variable {G H : SimpleGraph Nat} {n : Nat}

/-- All old vertices, including every prescribed nonneighbour, are
included when invoking the target extension property. -/
theorem next_vertex (p : PrefixEmbedding G H n)
    (hFree : G.CliqueFree 4) (hExtension : HensonExtension H) :
    ∃ x : Nat, (∀ i, i < n → x ≠ p.value i) ∧
      ∀ i, i < n → (H.Adj x (p.value i) ↔ G.Adj n i) := by
  classical
  let U := ((Finset.range n).filter fun i => G.Adj n i).image p.value
  let V := ((Finset.range n).filter fun i => ¬ G.Adj n i).image p.value
  have hMemU : ∀ y, y ∈ U ↔
      ∃ i, i < n ∧ G.Adj n i ∧ p.value i = y := by
    intro y
    simp [U, and_assoc]
  have hMemV : ∀ y, y ∈ V ↔
      ∃ i, i < n ∧ ¬ G.Adj n i ∧ p.value i = y := by
    intro y
    simp [V, and_assoc]
  have hDisjoint : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro y hyU hyV
    obtain ⟨i, hi, hPos, hI⟩ := (hMemU y).mp hyU
    obtain ⟨j, hj, hNeg, hJ⟩ := (hMemV y).mp hyV
    have hij := p.injective i hi j hj (hI.trans hJ.symm)
    exact hNeg (hij ▸ hPos)
  have hSafe : ∀ T : Finset Nat, T ⊆ U → ¬ H.IsNClique 3 T := by
    intro T hTU hTriangle
    obtain ⟨a, b, c, hab, hac, hbc, hT⟩ := H.is3Clique_iff.mp hTriangle
    have ha : a ∈ U := hTU (by simp [hT])
    have hb : b ∈ U := hTU (by simp [hT])
    have hc : c ∈ U := hTU (by simp [hT])
    obtain ⟨i, hi, hNi, hI⟩ := (hMemU a).mp ha
    obtain ⟨j, hj, hNj, hJ⟩ := (hMemU b).mp hb
    obtain ⟨k, hk, hNk, hK⟩ := (hMemU c).mp hc
    have hIJ : G.Adj i j := (p.adj_iff i hi j hj).mp
      (by simpa [hI, hJ] using hab)
    have hIK : G.Adj i k := (p.adj_iff i hi k hk).mp
      (by simpa [hI, hK] using hac)
    have hJK : G.Adj j k := (p.adj_iff j hj k hk).mp
      (by simpa [hJ, hK] using hbc)
    have hSourceTriangle : G.IsNClique 3 {i, j, k} :=
      G.is3Clique_triple_iff.mpr ⟨hIJ, hIK, hJK⟩
    have hAdjacent : ∀ v ∈ ({i, j, k} : Finset Nat), G.Adj n v := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> assumption
    exact hFree (insert n {i, j, k}) (hSourceTriangle.insert hAdjacent)
  obtain ⟨x, hFresh, hPos, hNeg⟩ := hExtension U V hDisjoint hSafe
  have hOldMember : ∀ i, i < n → p.value i ∈ U ∪ V := by
    intro i hi
    by_cases hAdj : G.Adj n i
    · exact Finset.mem_union_left V ((hMemU _).mpr ⟨i, hi, hAdj, rfl⟩)
    · exact Finset.mem_union_right U ((hMemV _).mpr ⟨i, hi, hAdj, rfl⟩)
  refine ⟨x, ?_, ?_⟩
  · intro i hi hEq
    apply hFresh
    rw [hEq]
    exact hOldMember i hi
  · intro i hi
    by_cases hAdj : G.Adj n i
    · have hTarget := hPos _ ((hMemU _).mpr ⟨i, hi, hAdj, rfl⟩)
      exact ⟨fun _ => hAdj, fun _ => hTarget⟩
    · have hTarget := hNeg _ ((hMemV _).mpr ⟨i, hi, hAdj, rfl⟩)
      exact ⟨fun h => (hTarget h).elim, fun h => (hAdj h).elim⟩

/-- Extend the finite prefix by one fresh vertex with the exact prescribed
positive and negative adjacency relations. -/
def extend (p : PrefixEmbedding G H n) (x : Nat)
    (hFresh : ∀ i, i < n → x ≠ p.value i)
    (hAdj : ∀ i, i < n → (H.Adj x (p.value i) ↔ G.Adj n i)) :
    PrefixEmbedding G H (n + 1) where
  value := Function.update p.value n x
  injective := by
    intro i hi j hj hEq
    by_cases hin : i = n
    · subst i
      by_cases hjn : j = n
      · exact hjn.symm
      · have hjOld : j < n := by omega
        have hBad : x = p.value j := by simpa [hjn] using hEq
        exact (hFresh j hjOld hBad).elim
    · have hiOld : i < n := by omega
      by_cases hjn : j = n
      · subst j
        have hBad : x = p.value i := by simpa [hin] using hEq.symm
        exact (hFresh i hiOld hBad).elim
      · have hjOld : j < n := by omega
        apply p.injective i hiOld j hjOld
        simpa [hin, hjn] using hEq
  adj_iff := by
    intro i hi j hj
    by_cases hin : i = n
    · subst i
      by_cases hjn : j = n
      · subst j
        simp
      · have hjOld : j < n := by omega
        simpa [hjn] using hAdj j hjOld
    · have hiOld : i < n := by omega
      by_cases hjn : j = n
      · subst j
        simpa [hin, H.adj_comm (p.value i) x, G.adj_comm i n] using hAdj i hiOld
      · have hjOld : j < n := by omega
        simpa [hin, hjn] using p.adj_iff i hiOld j hjOld

theorem extend_agrees (p : PrefixEmbedding G H n) (x : Nat)
    (hFresh : ∀ i, i < n → x ≠ p.value i)
    (hAdj : ∀ i, i < n → (H.Adj x (p.value i) ↔ G.Adj n i))
    (i : Nat) (hi : i < n) :
    (extend p x hFresh hAdj).value i = p.value i := by
  simp [extend, Nat.ne_of_lt hi]

end PrefixEmbedding

/-- The unique obligation at stage zero is vacuous. -/
def emptyPrefix (G H : SimpleGraph Nat) : PrefixEmbedding G H 0 where
  value := fun _ => 0
  injective := by intros; omega
  adj_iff := by intros; omega

/-- Choose successive finite extensions using only the ordinary target
extension property. -/
noncomputable def prefixes (G H : SimpleGraph Nat)
    (hFree : G.CliqueFree 4) (hExtension : HensonExtension H) :
    (n : Nat) → PrefixEmbedding G H n
  | 0 => emptyPrefix G H
  | n + 1 =>
    let p := prefixes G H hFree hExtension n
    let h := p.next_vertex hFree hExtension
    p.extend (Classical.choose h) (Classical.choose_spec h).1 (Classical.choose_spec h).2

theorem prefixes_succ_agrees (G H : SimpleGraph Nat)
    (hFree : G.CliqueFree 4) (hExtension : HensonExtension H)
    (n i : Nat) (hi : i < n) :
    (prefixes G H hFree hExtension (n + 1)).value i =
      (prefixes G H hFree hExtension n).value i := by
  simp [prefixes, PrefixEmbedding.extend, Nat.ne_of_lt hi]

theorem prefixes_agree (G H : SimpleGraph Nat)
    (hFree : G.CliqueFree 4) (hExtension : HensonExtension H)
    (n m i : Nat) (hnm : n ≤ m) (hi : i < n) :
    (prefixes G H hFree hExtension m).value i =
      (prefixes G H hFree hExtension n).value i := by
  induction m with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    rfl
  | succ m ih =>
    by_cases hn : n = m + 1
    · subst n
      rfl
    · have hnm' : n ≤ m := by omega
      rw [prefixes_succ_agrees G H hFree hExtension m i (by omega)]
      exact ih hnm'

/-- The value assigned to a source vertex when it is first inserted. -/
noncomputable def limitValue (G H : SimpleGraph Nat)
    (hFree : G.CliqueFree 4) (hExtension : HensonExtension H) (i : Nat) : Nat :=
  (prefixes G H hFree hExtension (i + 1)).value i

theorem limitValue_eq_prefix (G H : SimpleGraph Nat)
    (hFree : G.CliqueFree 4) (hExtension : HensonExtension H)
    (n i : Nat) (hi : i < n) :
    limitValue G H hFree hExtension i =
      (prefixes G H hFree hExtension n).value i := by
  exact (prefixes_agree G H hFree hExtension (i + 1) n i (by omega) (by omega)).symm

/-- Every countable `K_4`-free graph embeds inducedly into every target
with the ordinary Henson extension property. The map need not be increasing. -/
noncomputable def inducedEmbedding (G H : SimpleGraph Nat)
    (hFree : G.CliqueFree 4) (hExtension : HensonExtension H) : G ↪g H where
  toFun := limitValue G H hFree hExtension
  inj' := by
    intro i j hEq
    let n := max i j + 1
    have hi : i < n := by dsimp [n]; omega
    have hj : j < n := by dsimp [n]; omega
    apply (prefixes G H hFree hExtension n).injective i hi j hj
    rw [← limitValue_eq_prefix G H hFree hExtension n i hi,
      ← limitValue_eq_prefix G H hFree hExtension n j hj]
    exact hEq
  map_rel_iff' := by
    intro i j
    change H.Adj (limitValue G H hFree hExtension i)
      (limitValue G H hFree hExtension j) ↔ G.Adj i j
    let n := max i j + 1
    have hi : i < n := by dsimp [n]; omega
    have hj : j < n := by dsimp [n]; omega
    rw [limitValue_eq_prefix G H hFree hExtension n i hi,
      limitValue_eq_prefix G H hFree hExtension n j hj]
    exact (prefixes G H hFree hExtension n).adj_iff i hi j hj

theorem exists_inducedEmbedding (G H : SimpleGraph Nat)
    (hFree : G.CliqueFree 4) (hExtension : HensonExtension H) :
    Nonempty (G ↪g H) :=
  ⟨inducedEmbedding G H hFree hExtension⟩

theorem isHenson4_mutually_embeddable (G H : SimpleGraph Nat)
    (hG : IsHenson4 G) (hH : IsHenson4 H) :
    Nonempty (G ↪g H) ∧ Nonempty (H ↪g G) :=
  ⟨exists_inducedEmbedding G H hG.1 hH.2,
    exists_inducedEmbedding H G hH.1 hG.2⟩

/-- The unordered-nonedge degree bound is independent of the chosen
countable model satisfying the ordinary Henson characterization. -/
theorem degreeLE_iff_of_isHenson4 (G H : SimpleGraph Nat)
    (hG : IsHenson4 G) (hH : IsHenson4 H) (t : Nat) :
    DegreeLE G t ↔ DegreeLE H t := by
  let i := inducedEmbedding G H hG.1 hH.2
  let j := inducedEmbedding H G hH.1 hG.2
  exact ⟨degreeLE_of_mutual_embeddings i j t,
    degreeLE_of_mutual_embeddings j i t⟩

theorem degreeEq_iff_of_isHenson4 (G H : SimpleGraph Nat)
    (hG : IsHenson4 G) (hH : IsHenson4 H) (t : Nat) :
    DegreeEq G t ↔ DegreeEq H t := by
  constructor
  · intro h
    refine ⟨(degreeLE_iff_of_isHenson4 G H hG hH t).mp h.1, ?_⟩
    intro s hs hBound
    exact h.2 s hs ((degreeLE_iff_of_isHenson4 G H hG hH s).mpr hBound)
  · intro h
    refine ⟨(degreeLE_iff_of_isHenson4 G H hG hH t).mpr h.1, ?_⟩
    intro s hs hBound
    exact h.2 s hs ((degreeLE_iff_of_isHenson4 G H hG hH s).mp hBound)

end Kk.HensonUniversality
