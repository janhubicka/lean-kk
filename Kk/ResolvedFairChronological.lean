import Kk.ResolvedFairLimit
import Kk.OneGapCountableSchedule
import Mathlib.Data.Finset.Sort

/-!
# The actual fair limit in chronological round order

English proof: `docs/resolved_fair_chronological_english_20261126.md`.
Enumerate each finite round's new names, with the coded even original
last. Initial segments are exactly the actual old pools. This orders
rounds; the separate marker/cover event order inside each round is
not asserted by this module.
-/

namespace Kk

noncomputable def resolvedFairRoundNew
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) : Finset Nat :=
  (resolvedFairStages s0 (n+1)).old \ (resolvedFairStages s0 n).old

theorem resolvedFairRoundNew_coded
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) :
    2*n ∈ resolvedFairRoundNew s0 n := by
  refine Finset.mem_sdiff.mpr ⟨(resolvedFairStages_step s0 n).coded,?_⟩
  intro hOld
  exact (resolvedFairStages s0 n).separated _ hOld (resolvedEvenTail_coding n)

noncomputable def resolvedFairRoundList
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) : List Nat :=
  ((resolvedFairRoundNew s0 n).erase (2*n)).sort ++ [2*n]

theorem resolvedFairRoundList_mem
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n x : Nat) :
    x ∈ resolvedFairRoundList s0 n ↔ x ∈ resolvedFairRoundNew s0 n := by
  simp only [resolvedFairRoundList,List.mem_append,Finset.mem_sort,
    Finset.mem_erase,List.mem_singleton]
  constructor
  · rintro (⟨_,hx⟩ | rfl)
    · exact hx
    · exact resolvedFairRoundNew_coded s0 n
  · intro hx
    by_cases h : x = 2*n
    · exact Or.inr h
    · exact Or.inl ⟨h,hx⟩

theorem resolvedFairRoundList_positive
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) :
    0 < (resolvedFairRoundList s0 n).length := by
  simp [resolvedFairRoundList]

theorem resolvedFairRoundList_nodup
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) :
    (resolvedFairRoundList s0 n).Nodup := by
  apply List.nodup_append'.mpr
  refine ⟨Finset.sort_nodup _ _,by simp,?_⟩
  intro x hx hy
  have he : x = 2*n := by simpa using hy
  have hMem : x ∈ (resolvedFairRoundNew s0 n).erase (2*n) :=
    by simpa only [Finset.mem_sort] using hx
  exact (Finset.mem_erase.mp hMem).1 he

theorem resolvedFairRoundList_disjoint
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n m : Nat) (hnm : n ≠ m) :
    List.Disjoint (resolvedFairRoundList s0 n) (resolvedFairRoundList s0 m) := by
  intro x hx hy
  have hx' := Finset.mem_sdiff.mp ((resolvedFairRoundList_mem s0 n x).mp hx)
  have hy' := Finset.mem_sdiff.mp ((resolvedFairRoundList_mem s0 m x).mp hy)
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · exact hy'.2 (resolvedFairStages_old_mono s0 (by omega) hx'.1)
  · exact hx'.2 (resolvedFairStages_old_mono s0 (by omega) hy'.1)

/-- At a round boundary, every old vertex has entered in one earlier
round. The empty initial pool is necessary here. -/
theorem resolvedFairRoundNew_prefix
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (n x : Nat) :
    (∃ m, m < n ∧ x ∈ resolvedFairRoundNew s0 m) ↔
      x ∈ (resolvedFairStages s0 n).old := by
  induction n with
  | zero => simp [resolvedFairStages,hEmpty]
  | succ n ih =>
      constructor
      · rintro ⟨m,hm,hx⟩
        exact resolvedFairStages_old_mono s0 (by omega) (Finset.mem_sdiff.mp hx).1
      · intro hx
        by_cases hOld : x ∈ (resolvedFairStages s0 n).old
        · obtain ⟨m,hm,hMem⟩ := ih.mpr hOld
          exact ⟨m,by omega,hMem⟩
        · exact ⟨n,by omega,Finset.mem_sdiff.mpr ⟨hx,hOld⟩⟩

noncomputable def resolvedFairBoundary
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) : Nat → Nat :=
  oneGapBatchBoundary (fun n => (resolvedFairRoundList s0 n).length)

noncomputable def resolvedFairChronological
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) : Nat → Nat :=
  oneGapChronologicalVertex (resolvedFairRoundList s0) (resolvedFairRoundList_positive s0)

theorem resolvedFairChronological_injective
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) :
    Function.Injective (resolvedFairChronological s0) :=
  oneGapChronologicalVertex_injective _ (resolvedFairRoundList_positive s0)
    (resolvedFairRoundList_nodup s0) (resolvedFairRoundList_disjoint s0)

/-- Exact actual old-prefix sets in the constructed enumeration. -/
theorem resolvedFairChronological_prefix
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (n x : Nat) :
    (∃ k, k < resolvedFairBoundary s0 n ∧ resolvedFairChronological s0 k = x) ↔
      x ∈ (resolvedFairStages s0 n).old := by
  change (∃ k, k < oneGapBatchBoundary _ n ∧
    oneGapChronologicalVertex _ _ k = x) ↔ _
  rw [oneGapChronologicalVertex_prefix]
  simpa only [resolvedFairRoundList_mem] using resolvedFairRoundNew_prefix s0 hEmpty n x

/-- Every actual limit vertex occurs, with no unused names inserted. -/
theorem resolvedFairChronological_range
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (x : Nat) :
    (∃ k, resolvedFairChronological s0 k = x) ↔ x ∈ resolvedFairDomain s0 := by
  constructor
  · rintro ⟨k,hk⟩
    have hMem := oneGapChronologicalVertex_mem (resolvedFairRoundList s0)
      (resolvedFairRoundList_positive s0) k
    have hNew := (resolvedFairRoundList_mem s0 _ _).mp hMem
    have hOld := (Finset.mem_sdiff.mp hNew).1
    change resolvedFairChronological s0 k ∈ _ at hOld
    exact ⟨_,hk ▸ hOld⟩
  · rintro ⟨n,hx⟩
    obtain ⟨k,_hk,hEq⟩ := (resolvedFairChronological_prefix s0 hEmpty n x).mpr hx
    exact ⟨k,hEq⟩

noncomputable def resolvedFairCodeTag
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) :
    (m : Nat) × Fin (resolvedFairRoundList s0 m).length :=
  ⟨n,⟨(((resolvedFairRoundNew s0 n).erase (2*n)).sort).length,
    by simp [resolvedFairRoundList]⟩⟩

noncomputable def resolvedFairCodePosition
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) : Nat :=
  oneGapBatchPosition (fun m => (resolvedFairRoundList s0 m).length)
    (resolvedFairCodeTag s0 n)

theorem resolvedFairChronological_coded
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) :
    resolvedFairChronological s0 (resolvedFairCodePosition s0 n) = 2*n := by
  unfold resolvedFairChronological resolvedFairCodePosition
  rw [oneGapChronologicalVertex_at_position]
  simp [resolvedFairCodeTag,resolvedFairRoundList]

theorem resolvedFairCodePosition_bounds
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) :
    resolvedFairBoundary s0 n ≤ resolvedFairCodePosition s0 n ∧
      resolvedFairCodePosition s0 n < resolvedFairBoundary s0 (n+1) :=
  oneGapBatchPosition_bounds _ (resolvedFairCodeTag s0 n)

/-- The coding vertex is exactly the final position of its round. -/
theorem resolvedFairCodePosition_last
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) :
    resolvedFairCodePosition s0 n + 1 = resolvedFairBoundary s0 (n+1) := by
  change oneGapBatchBoundary (fun m => (resolvedFairRoundList s0 m).length) n +
    (((resolvedFairRoundNew s0 n).erase (2*n)).sort).length + 1 =
      oneGapBatchBoundary (fun m => (resolvedFairRoundList s0 m).length) (n+1)
  rw [oneGapBatchBoundary_succ]
  simp [resolvedFairRoundList,Nat.add_assoc]

/-- Coding positions increase in the actual round enumeration. -/
theorem resolvedFairCodePosition_strictMono
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) :
    StrictMono (resolvedFairCodePosition s0) := by
  intro n m hnm
  have hn := resolvedFairCodePosition_bounds s0 n
  have hm := resolvedFairCodePosition_bounds s0 m
  have hB := (oneGapBatchBoundary_strictMono _
    (resolvedFairRoundList_positive s0)).monotone (show n+1 ≤ m by omega)
  change resolvedFairBoundary s0 (n+1) ≤ resolvedFairBoundary s0 m at hB
  omega

noncomputable def resolvedFairChronologicalEdge
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (u v : Nat) : Bool :=
  resolvedFairEdge s0 (resolvedFairChronological s0 u) (resolvedFairChronological s0 v)

theorem resolvedFairChronologicalEdge_sym
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (u v : Nat) :
    resolvedFairChronologicalEdge s0 u v = resolvedFairChronologicalEdge s0 v u :=
  resolvedFairEdge_sym s0 _ _

theorem resolvedFairChronologicalEdge_loops
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (u : Nat) :
    resolvedFairChronologicalEdge s0 u u = false :=
  resolvedFairEdge_loops s0 _

theorem resolvedFairChronologicalEdge_free
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) :
    ∀ C : Finset Nat, IsDirectedCliqueOn (resolvedFairChronologicalEdge s0) C →
      C.card < 4 := by
  classical
  intro C hC
  let e := resolvedFairChronological s0
  have hImage : IsDirectedCliqueOn (resolvedFairEdge s0) (C.image e) := by
    intro x hx y hy hxy
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
    exact hC a ha b hb (fun h => hxy (congrArg e h))
  have hFree := resolvedFairEdge_free s0 (C.image e) hImage
  have hCard := Finset.card_image_of_injective C (resolvedFairChronological_injective s0)
  rwa [hCard] at hFree

theorem resolvedFairChronologicalEdge_originals
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (i j : Nat) :
    resolvedFairChronologicalEdge s0 (resolvedFairCodePosition s0 i)
      (resolvedFairCodePosition s0 j) = s0.edge (2*i) (2*j) := by
  unfold resolvedFairChronologicalEdge
  rw [resolvedFairChronological_coded,resolvedFairChronological_coded]
  exact resolvedFairEdge_even_eq s0 i j

/-- The explicitly constructed chronological graph contains the
prescribed graph at its increasing, coding-last positions. -/
theorem resolvedInitialChronological_originals
    (E : Nat → Nat → Bool)
    (hFree : ∀ C : Finset Nat, IsDirectedCliqueOn E C → C.card < 4)
    (hSym : ∀ x y, E x y = E y x) (hLoops : ∀ x, E x x = false)
    (i j : Nat) :
    let s0 := resolvedInitialStage E hFree hSym hLoops
    resolvedFairChronologicalEdge s0 (resolvedFairCodePosition s0 i)
      (resolvedFairCodePosition s0 j) = E i j := by
  dsimp only
  rw [resolvedFairChronologicalEdge_originals]
  change E (2*i/2) (2*j/2) = E i j
  congr 1 <;> omega

end Kk
