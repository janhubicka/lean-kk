import Mathlib.Tactic

/-!
# Rank-large sets: an independent finite-partition lemma for the Henson lower bound

This is the abstract combinatorial step of the graph-specific one-diary
unavoidability route. It is proved directly, WITHOUT assuming the
published diary characterization or any BRD lower-bound theorem.

Ranks are zero-based here: rank 0 corresponds to singleton graph-age 1.
The actual Henson coding-tree instantiation, clique certificates,
compatible-pair synchronization and one-diary occurrence theorem
are separate OPEN applications.
-/

namespace Kk.RankLargeness

universe u v

variable {Node : Type u} [Preorder Node]

/-- Recursive largeness in a ranked extension preorder.
At rank 0 this is density; at successor rank every same-rank extension
has a lower-rank extension supporting recursive largeness.
The source rank equality is deliberately NOT part of this definition. -/
def Large (rank : Node → Nat) (S : Set Node) : Nat → Node → Prop
  | 0, u => ∀ v, u ≤ v → ∃ w, v ≤ w ∧ w ∈ S
  | n + 1, u =>
      ∀ v, u ≤ v → rank v = n + 1 →
        ∃ w, v ≤ w ∧ rank w = n ∧ Large rank S n w

/-- A rank-large set contains a genuine descendant of the source node.
The explicit source-rank equality is necessary. -/
theorem large_has_member (rank : Node → Nat) (S : Set Node) :
    ∀ n (u : Node), rank u = n → Large rank S n u →
      ∃ w, u ≤ w ∧ w ∈ S := by
  intro n
  induction n with
  | zero =>
      intro u _ hLarge
      exact hLarge u (le_refl u)
  | succ n ih =>
      intro u hu hLarge
      obtain ⟨w, huw, hw, hSmall⟩ :=
        hLarge u (le_refl u) hu
      obtain ⟨z, hwz, hz⟩ := ih w hw hSmall
      exact ⟨z, le_trans huw hwz, hz⟩

/-- Rank largeness survives moving further into the same cone;
the rank of the new source is not required for this basic implication. -/
theorem large_mono_cone (rank : Node → Nat) (S : Set Node) :
    ∀ n (u v : Node), u ≤ v → Large rank S n u →
      Large rank S n v := by
  intro n
  cases n with
  | zero =>
      intro u v huv hLarge w hvw
      exact hLarge w (le_trans huv hvw)
  | succ n =>
      intro u v huv hLarge w hvw hw
      exact hLarge w (le_trans huv hvw) hw

/-- Enlarging the set of available coding nodes preserves rank
largeness, at every rank and node. -/
theorem large_mono_set (rank : Node → Nat) {S T : Set Node}
    (hST : S ⊆ T) :
    ∀ n (u : Node), Large rank S n u → Large rank T n u := by
  intro n
  induction n with
  | zero =>
      intro u hLarge v huv
      obtain ⟨w, hvw, hw⟩ := hLarge v huv
      exact ⟨w, hvw, hST hw⟩
  | succ n ih =>
      intro u hLarge v huv hv
      obtain ⟨w, hvw, hw, hwLarge⟩ := hLarge v huv hv
      exact ⟨w, hvw, hw, ih w hwLarge⟩

/-- Density above a source of rank n implies n-largeness whenever
EVERY positive-rank node has a genuine one-step rank-lowering
extension. In the Henson application this premise requires REAL
clique-certificate constructions; it is not a diary axiom. -/
theorem dense_implies_large (rank : Node → Nat)
    (hDrop : ∀ n (v : Node), rank v = n + 1 →
      ∃ w, v ≤ w ∧ rank w = n)
    (S : Set Node) :
    ∀ n (u : Node), rank u = n → Large rank S 0 u →
      Large rank S n u := by
  intro n
  induction n with
  | zero =>
      intro u _ hDense
      exact hDense
  | succ n ih =>
      intro u _ hDense v huv hv
      obtain ⟨w, hvw, hw⟩ := hDrop n v hv
      have hDenseW : Large rank S 0 w :=
        large_mono_cone rank S 0 u w (le_trans huv hvw) hDense
      exact ⟨w, hvw, hw, ih w hw hDenseW⟩

/-- Every genuine rank-large union has a colour-large cone of
the SAME original rank. Antitonicity is needed already at rank zero.
This proof uses no diary type as a primitive assumption. -/
theorem large_union_partition (rank : Node → Nat)
    (hAnti : Antitone rank) (A B : Set Node) :
    ∀ n (u : Node), rank u = n → Large rank (A ∪ B) n u →
      (∃ v, u ≤ v ∧ rank v = n ∧ Large rank A n v) ∨
      (∃ v, u ≤ v ∧ rank v = n ∧ Large rank B n v) := by
  intro n
  induction n with
  | zero =>
      intro u hu hLarge
      by_cases hSomeA :
          ∃ v, u ≤ v ∧ rank v = 0 ∧ Large rank A 0 v
      · exact Or.inl hSomeA
      · right
        have hNotA : ¬ Large rank A 0 u := by
          intro ha
          exact hSomeA ⟨u, le_refl u, hu, ha⟩
        change ¬ (∀ v : Node, u ≤ v →
          ∃ w : Node, v ≤ w ∧ w ∈ A) at hNotA
        push_neg at hNotA
        obtain ⟨v, huv, hNoA⟩ := hNotA
        have hv : rank v = 0 := by
          have hle := hAnti huv
          omega
        refine ⟨v, huv, hv, ?_⟩
        intro t hvt
        obtain ⟨w, htw, hw⟩ :=
          hLarge t (le_trans huv hvt)
        have hwB : w ∈ B := by
          rcases Set.mem_union.mp hw with hwA | hwB
          · exact False.elim
              ((hNoA w (le_trans hvt htw)) hwA)
          · exact hwB
        exact ⟨w, htw, hwB⟩
  | succ n ih =>
      intro u hu hLarge
      by_cases hSomeA :
          ∃ v, u ≤ v ∧ rank v = n + 1 ∧ Large rank A (n + 1) v
      · exact Or.inl hSomeA
      · right
        have hNotA : ¬ Large rank A (n + 1) u := by
          intro ha
          exact hSomeA ⟨u, le_refl u, hu, ha⟩
        change ¬ (∀ v : Node, u ≤ v → rank v = n + 1 →
          ∃ w : Node, v ≤ w ∧ rank w = n ∧
            Large rank A n w) at hNotA
        push_neg at hNotA
        obtain ⟨v, huv, hv, hNoA⟩ := hNotA
        refine ⟨v, huv, hv, ?_⟩
        intro t hvt ht
        obtain ⟨w, htw, hwRank, hwLarge⟩ :=
          hLarge t (le_trans huv hvt) ht
        rcases ih w hwRank hwLarge with hFirst | hSecond
        · obtain ⟨z, hwz, hzRank, hzLarge⟩ := hFirst
          have hvz : v ≤ z :=
            le_trans hvt (le_trans htw hwz)
          exact False.elim ((hNoA z hvz hzRank) hzLarge)
        · obtain ⟨z, hwz, hzRank, hzLarge⟩ := hSecond
          exact ⟨z, le_trans htw hwz, hzRank, hzLarge⟩

/-- A genuinely finite colouring of a rank-large set has one
rank-large colour class above some same-rank descendant.

The colour type may be empty: in that case the hypotheses are
inconsistent, as witnessed by `large_has_member`.
No Henson-extension or diary-embedding theorem is assumed. -/
theorem large_finite_colour_partition
    {Colour : Type v} [Fintype Colour]
    (rank : Node → Nat) (hAnti : Antitone rank)
    (S : Set Node) (colour : Node → Colour)
    (n : Nat) (u : Node)
    (hu : rank u = n) (hLarge : Large rank S n u) :
    ∃ j : Colour, ∃ w : Node,
      u ≤ w ∧ rank w = n ∧
        Large rank {x | x ∈ S ∧ colour x = j} n w := by
  classical
  let fibre (j : Colour) : Set Node :=
    {x | x ∈ S ∧ colour x = j}
  let cover (C : Finset Colour) : Set Node :=
    {x | x ∈ S ∧ colour x ∈ C}
  have hFind :
      ∀ C : Finset Colour, ∀ v : Node,
        rank v = n → Large rank (cover C) n v →
          ∃ j, j ∈ C ∧ ∃ w : Node,
            v ≤ w ∧ rank w = n ∧ Large rank (fibre j) n w := by
    intro C
    induction C using Finset.induction_on with
    | empty =>
        intro v hv h
        obtain ⟨w, _, hw⟩ :=
          large_has_member rank (cover (∅ : Finset Colour)) n v hv h
        simp [cover] at hw
    | @insert j C hj ih =>
        intro v hv h
        have hEq : cover (insert j C) = fibre j ∪ cover C := by
          ext x
          change (x ∈ S ∧ colour x ∈ insert j C) ↔
            (x ∈ S ∧ colour x = j) ∨
              (x ∈ S ∧ colour x ∈ C)
          constructor
          · rintro ⟨hxS, hxC⟩
            rcases Finset.mem_insert.mp hxC with h | h
            · exact Or.inl ⟨hxS, h⟩
            · exact Or.inr ⟨hxS, h⟩
          · intro hx
            rcases hx with ⟨hxS, hxj⟩ | ⟨hxS, hxC⟩
            · exact ⟨hxS, Finset.mem_insert.mpr (Or.inl hxj)⟩
            · exact ⟨hxS, Finset.mem_insert.mpr (Or.inr hxC)⟩
        rw [hEq] at h
        rcases large_union_partition rank hAnti (fibre j) (cover C)
            n v hv h with hLeft | hRight
        · obtain ⟨w, hvw, hw, hLargeW⟩ := hLeft
          exact ⟨j, Finset.mem_insert_self j C, w, hvw, hw, hLargeW⟩
        · obtain ⟨w, hvw, hw, hLargeW⟩ := hRight
          obtain ⟨j', hj', z, hwz, hz, hzLarge⟩ :=
            ih w hw hLargeW
          exact ⟨j', Finset.mem_insert_of_mem hj',
            z, le_trans hvw hwz, hz, hzLarge⟩
  have hCover : cover (Finset.univ : Finset Colour) = S := by
    ext x
    simp [cover]
  obtain ⟨j, _, w, huw, hw, hFibre⟩ :=
    hFind Finset.univ u hu (by simpa only [hCover] using hLarge)
  exact ⟨j, w, huw, hw, hFibre⟩

end Kk.RankLargeness
