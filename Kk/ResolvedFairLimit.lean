import Kk.ResolvedLiveRound
import Mathlib.Tactic

/-!
# Fair coherent infinite resolved graph
English proof: docs/resolved_fair_rounds_english_20261126.md.
Construct the actual successive live states and their finite round
traces on even original names, then take the union of the old domains.
Chronological reindexing and dummy insertion remain separate.
-/

namespace Kk

def resolvedEvenTail (n : Nat) : Set Nat :=
  {v | v % 2 = 0 ∧ 2*n ≤ v}

theorem resolvedEvenTail_next (n : Nat) :
    resolvedEvenTail (n+1) = resolvedEvenTail n \ {2*n} := by
  ext v
  change (v % 2 = 0 ∧ 2*(n+1) ≤ v) ↔
    (v % 2 = 0 ∧ 2*n ≤ v) ∧ v ≠ 2*n
  omega

theorem resolvedEvenTail_coding (n : Nat) : 2*n ∈ resolvedEvenTail n := by
  change (2*n) % 2 = 0 ∧ 2*n ≤ 2*n
  omega

/-- The initial stage has only the prescribed even original graph.
Its unused odd edges are arbitrary and are overwritten only on fresh names. -/
def resolvedInitialStage (E : Nat → Nat → Bool)
    (hFree : ∀ C : Finset Nat, IsDirectedCliqueOn E C → C.card < 4)
    (hSym : ∀ x y, E x y = E y x) (hLoops : ∀ x, E x x = false) :
    ResolvedBareStage 4 (resolvedEvenTail 0) where
  edge x y := E (x/2) (y/2)
  old := ∅
  separated := by simp
  free := by
    classical
    intro C hC hc
    let D := C.image (fun x => x/2)
    have hEven : ∀ x ∈ C, x % 2 = 0 := by
      intro x hx
      rcases hC x hx with hEmpty | hw
      · simp at hEmpty
      · exact hw.1
    have hInj : Set.InjOn (fun x : Nat => x/2) (↑C : Set Nat) := by
      intro x hx y hy he
      change x/2 = y/2 at he
      have hx' := hEven x hx
      have hy' := hEven y hy
      omega
    have hCard : D.card = C.card := Finset.card_image_of_injOn hInj
    have hClique : IsDirectedCliqueOn E D := by
      intro x hx y hy hxy
      obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hx
      obtain ⟨b,hb,hf⟩ := Finset.mem_image.mp hy
      have hab : a ≠ b := by
        intro h
        apply hxy
        rw [← he,← hf,h]
      have hEdge := hc a ha b hb hab
      change E (a/2) (b/2) = true at hEdge
      rwa [he,hf] at hEdge
    have hBound := hFree D hClique
    rwa [hCard] at hBound
  sym x y := hSym (x/2) (y/2)
  loops x := hLoops (x/2)

/-- The next state is chosen with all finite round certificates. -/
noncomputable def resolvedFairNext (n : Nat)
    (s : ResolvedBareStage 4 (resolvedEvenTail n)) :
    ResolvedBareStage 4 (resolvedEvenTail (n+1)) :=
  Classical.choose (resolvedBare_exists_round s (2*n) (resolvedEvenTail_coding n)
    (fun v hv => hv.1) (resolvedEvenTail_next n))

theorem resolvedFairNext_result (n : Nat)
    (s : ResolvedBareStage 4 (resolvedEvenTail n)) :
    ResolvedRoundResult s (2*n) (resolvedFairNext n s) :=
  Classical.choose_spec (resolvedBare_exists_round s (2*n) (resolvedEvenTail_coding n)
    (fun v hv => hv.1) (resolvedEvenTail_next n))

noncomputable def resolvedFairStages
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) :
    (n : Nat) → ResolvedBareStage 4 (resolvedEvenTail n)
  | 0 => s0
  | n+1 => resolvedFairNext n (resolvedFairStages s0 n)

theorem resolvedFairStages_step
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) :
    ResolvedRoundResult (resolvedFairStages s0 n) (2*n) (resolvedFairStages s0 (n+1)) :=
  resolvedFairNext_result n (resolvedFairStages s0 n)

theorem resolvedFairStages_old_mono
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) {m n : Nat} (hmn : m ≤ n) :
    (resolvedFairStages s0 m).old ⊆ (resolvedFairStages s0 n).old := by
  induction n with
  | zero =>
      have hm : m = 0 := by omega
      subst m
      exact Finset.Subset.refl _
  | succ n ih =>
      by_cases he : m = n+1
      · subst m; exact Finset.Subset.refl _
      · exact (ih (by omega)).trans (resolvedFairStages_step s0 n).old_mono

/-- Once a name belongs to the actual old-or-live domain, it remains
there. Every even vertex is eventually moved to the old domain. -/
theorem resolvedFairStages_live_mono_step
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n x : Nat)
    (hx : x ∈ (resolvedFairStages s0 n).old ∨ x ∈ resolvedEvenTail n) :
    x ∈ (resolvedFairStages s0 (n+1)).old ∨ x ∈ resolvedEvenTail (n+1) := by
  rcases hx with ho | hl
  · exact Or.inl ((resolvedFairStages_step s0 n).old_mono ho)
  · by_cases he : x = 2*n
    · subst x
      exact Or.inl (resolvedFairStages_step s0 n).coded
    · apply Or.inr
      rw [resolvedEvenTail_next]
      exact ⟨hl,by simpa using he⟩

theorem resolvedFairStages_live_mono
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) {m n : Nat} (hmn : m ≤ n)
    (x : Nat) (hx : x ∈ (resolvedFairStages s0 m).old ∨ x ∈ resolvedEvenTail m) :
    x ∈ (resolvedFairStages s0 n).old ∨ x ∈ resolvedEvenTail n := by
  induction n with
  | zero =>
      have hm : m = 0 := by omega
      subst m
      exact hx
  | succ n ih =>
      by_cases he : m = n+1
      · subst m; exact hx
      · exact resolvedFairStages_live_mono_step s0 n x (ih (by omega))

theorem resolvedFairStages_preserve
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) {m n : Nat} (hmn : m ≤ n)
    (x y : Nat)
    (hx : x ∈ (resolvedFairStages s0 m).old ∨ x ∈ resolvedEvenTail m)
    (hy : y ∈ (resolvedFairStages s0 m).old ∨ y ∈ resolvedEvenTail m) :
    (resolvedFairStages s0 n).edge x y = (resolvedFairStages s0 m).edge x y := by
  induction n with
  | zero =>
      have hm : m = 0 := by omega
      subst m; rfl
  | succ n ih =>
      by_cases he : m = n+1
      · subst m; rfl
      · have hmn' : m ≤ n := by omega
        exact ((resolvedFairStages_step s0 n).preserve x y
          (resolvedFairStages_live_mono s0 hmn' x hx)
          (resolvedFairStages_live_mono s0 hmn' y hy)).trans (ih hmn')

def resolvedFairDomain (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) : Set Nat :=
  {x | ∃ n, x ∈ (resolvedFairStages s0 n).old}

theorem resolvedFairDomain_even
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) :
    2*n ∈ resolvedFairDomain s0 :=
  ⟨n+1,(resolvedFairStages_step s0 n).coded⟩

/-- Use an arbitrary witnessing old stage. Preservation proves
independence of the choice, so the limit graph is literal.
Outside the actual domain use zero. -/
noncomputable def resolvedFairEdge
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (x y : Nat) : Bool := by
  classical
  exact if h : ∃ n, x ∈ (resolvedFairStages s0 n).old ∧
      y ∈ (resolvedFairStages s0 n).old then
    (resolvedFairStages s0 (Classical.choose h)).edge x y
  else false

theorem resolvedFairEdge_eq_at
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n x y : Nat)
    (hx : x ∈ (resolvedFairStages s0 n).old)
    (hy : y ∈ (resolvedFairStages s0 n).old) :
    resolvedFairEdge s0 x y = (resolvedFairStages s0 n).edge x y := by
  classical
  have h : ∃ m, x ∈ (resolvedFairStages s0 m).old ∧
      y ∈ (resolvedFairStages s0 m).old := ⟨n,hx,hy⟩
  unfold resolvedFairEdge
  rw [dif_pos h]
  have hM := Classical.choose_spec h
  rcases le_total n (Classical.choose h) with hle | hle
  · exact resolvedFairStages_preserve s0 hle x y (Or.inl hx) (Or.inl hy)
  · exact (resolvedFairStages_preserve s0 hle x y (Or.inl hM.1) (Or.inl hM.2)).symm

theorem resolvedFairEdge_sym
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (x y : Nat) :
    resolvedFairEdge s0 x y = resolvedFairEdge s0 y x := by
  classical
  by_cases h : ∃ n, x ∈ (resolvedFairStages s0 n).old ∧
      y ∈ (resolvedFairStages s0 n).old
  · obtain ⟨n,hx,hy⟩ := h
    rw [resolvedFairEdge_eq_at s0 n x y hx hy, resolvedFairEdge_eq_at s0 n y x hy hx]
    exact (resolvedFairStages s0 n).sym x y
  · have h' : ¬ ∃ n, y ∈ (resolvedFairStages s0 n).old ∧
        x ∈ (resolvedFairStages s0 n).old := by
      rintro ⟨n,hy,hx⟩
      exact h ⟨n,hx,hy⟩
    simp [resolvedFairEdge,h,h']

theorem resolvedFairEdge_loops
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (x : Nat) :
    resolvedFairEdge s0 x x = false := by
  classical
  by_cases h : ∃ n, x ∈ (resolvedFairStages s0 n).old
  · obtain ⟨n,hx⟩ := h
    rw [resolvedFairEdge_eq_at s0 n x x hx hx]
    exact (resolvedFairStages s0 n).loops x
  · simp [resolvedFairEdge,h]

/-- Any finite subset of the limit domain is inside one actual old stage. -/
theorem resolvedFairDomain_finite_stage
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (C : Finset Nat)
    (hC : ∀ x ∈ C, x ∈ resolvedFairDomain s0) :
    ∃ n, C ⊆ (resolvedFairStages s0 n).old := by
  classical
  induction C using Finset.induction_on with
  | empty => exact ⟨0,by simp⟩
  | @insert x C hx ih =>
      obtain ⟨n,hn⟩ := ih (fun y hy => hC y (Finset.mem_insert_of_mem hy))
      obtain ⟨m,hm⟩ := hC x (Finset.mem_insert_self x C)
      refine ⟨max m n,?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with he | hy
      · subst y
        exact resolvedFairStages_old_mono s0 (le_max_left _ _) hm
      · exact resolvedFairStages_old_mono s0 (le_max_right _ _) (hn hy)

/-- The countable coherent limit is genuinely K4-free on all names;
vertices outside the used domain are isolated. -/
theorem resolvedFairEdge_free
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) :
    ∀ C : Finset Nat, IsDirectedCliqueOn (resolvedFairEdge s0) C → C.card < 4 := by
  classical
  intro C hc
  by_contra hNot
  have hSize : 4 ≤ C.card := by omega
  have hC : ∀ x ∈ C, x ∈ resolvedFairDomain s0 := by
    intro x hx
    have hErase : (C.erase x).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem hx]
      omega
    obtain ⟨y,hy⟩ := hErase
    obtain ⟨hyx,hyC⟩ := Finset.mem_erase.mp hy
    have hEdge := hc x hx y hyC hyx.symm
    by_contra hDom
    have hNo : ¬ ∃ n, x ∈ (resolvedFairStages s0 n).old ∧
        y ∈ (resolvedFairStages s0 n).old := by
      rintro ⟨n,hx',_⟩
      exact hDom ⟨n,hx'⟩
    simp [resolvedFairEdge,hNo] at hEdge
  obtain ⟨n,hn⟩ := resolvedFairDomain_finite_stage s0 C hC
  have hClique : IsDirectedCliqueOn (resolvedFairStages s0 n).edge C := by
    intro x hx y hy hxy
    rw [← resolvedFairEdge_eq_at s0 n x y (hn hx) (hn hy)]
    exact hc x hx y hy hxy
  exact hNot ((resolvedFairStages s0 n).free C
    (fun x hx => Or.inl (hn hx)) hClique)

/-- All even originals induce exactly the initial prescribed graph. -/
theorem resolvedFairEdge_even_eq
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (i j : Nat) :
    resolvedFairEdge s0 (2*i) (2*j) = s0.edge (2*i) (2*j) := by
  let n := max (i+1) (j+1)
  have hi : 2*i ∈ (resolvedFairStages s0 n).old :=
    resolvedFairStages_old_mono s0 (le_max_left _ _) (resolvedFairStages_step s0 i).coded
  have hj : 2*j ∈ (resolvedFairStages s0 n).old :=
    resolvedFairStages_old_mono s0 (le_max_right _ _) (resolvedFairStages_step s0 j).coded
  rw [resolvedFairEdge_eq_at s0 n _ _ hi hj]
  exact resolvedFairStages_preserve s0 (Nat.zero_le n) _ _
    (Or.inr (by change (2*i)%2=0 ∧ 0 ≤ 2*i; omega))
    (Or.inr (by change (2*j)%2=0 ∧ 0 ≤ 2*j; omega))

/-- Explicit existence of an induced copy in the constructed limit,
together with actual finite traces for every coded original. -/
theorem resolvedFair_exists_graph (E : Nat → Nat → Bool)
    (hFree : ∀ C : Finset Nat, IsDirectedCliqueOn E C → C.card < 4)
    (hSym : ∀ x y, E x y = E y x) (hLoops : ∀ x, E x x = false) :
    ∃ (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (Q : Nat → Nat → Bool),
      Q = resolvedFairEdge s0 ∧
      (∀ x y, Q x y = Q y x) ∧ (∀ x, Q x x = false) ∧
      (∀ C : Finset Nat, IsDirectedCliqueOn Q C → C.card < 4) ∧
      (∀ i j, Q (2*i) (2*j) = E i j) ∧
      (∀ n, ResolvedRoundTrace (resolvedFairStages s0 n) (2*n)
        (resolvedFairStages s0 (n+1))) := by
  let s0 := resolvedInitialStage E hFree hSym hLoops
  refine ⟨s0,resolvedFairEdge s0,rfl,resolvedFairEdge_sym s0,
    resolvedFairEdge_loops s0,resolvedFairEdge_free s0,?_,?_⟩
  · intro i j
    rw [resolvedFairEdge_even_eq]
    change E (2*i/2) (2*j/2) = E i j
    have hi : 2*i/2 = i := by omega
    have hj : 2*j/2 = j := by omega
    rw [hi,hj]
  · intro n
    exact (resolvedFairStages_step s0 n).trace

/-- Every name in a live domain eventually becomes an old name.
This allows transfer of the full columns into the actual future,
not merely equality of the currently old induced subgraph. -/
theorem resolvedFair_live_eventually_old
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n x : Nat)
    (hx : x ∈ (resolvedFairStages s0 n).old ∨ x ∈ resolvedEvenTail n) :
    ∃ m, n ≤ m ∧ x ∈ (resolvedFairStages s0 m).old := by
  rcases hx with ho | hl
  · exact ⟨n,le_rfl,ho⟩
  · change x % 2 = 0 ∧ 2*n ≤ x at hl
    have he : x = 2*(x/2) := by omega
    have hN : n ≤ x/2+1 := by omega
    refine ⟨x/2+1,hN,?_⟩
    have hc := (resolvedFairStages_step s0 (x/2)).coded
    rwa [← he] at hc

theorem resolvedFairEdge_eq_live_at
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n x y : Nat)
    (hx : x ∈ (resolvedFairStages s0 n).old ∨ x ∈ resolvedEvenTail n)
    (hy : y ∈ (resolvedFairStages s0 n).old ∨ y ∈ resolvedEvenTail n) :
    resolvedFairEdge s0 x y = (resolvedFairStages s0 n).edge x y := by
  obtain ⟨m,hnm,hxOld⟩ := resolvedFair_live_eventually_old s0 n x hx
  obtain ⟨l,hnl,hyOld⟩ := resolvedFair_live_eventually_old s0 n y hy
  let N := max m l
  have hxN : x ∈ (resolvedFairStages s0 N).old :=
    resolvedFairStages_old_mono s0 (le_max_left _ _) hxOld
  have hyN : y ∈ (resolvedFairStages s0 N).old :=
    resolvedFairStages_old_mono s0 (le_max_right _ _) hyOld
  rw [resolvedFairEdge_eq_at s0 N x y hxN hyN]
  exact resolvedFairStages_preserve s0 (hnm.trans (le_max_left _ _)) x y hx hy

/-- Exact canonical reference ages over a subset of a genuine old pool
agree between the round graph and its limit, including future columns. -/
theorem resolvedFair_referenceAge_eq_live
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat)
    (P : Finset Nat) (hP : P ⊆ (resolvedFairStages s0 n).old)
    {d : Nat} (target : Fin d → Nat)
    (hTarget : ∀ i, target i ∈ resolvedEvenTail n) :
    resolvedTargetAge (resolvedFairEdge s0) 4 P target =
      resolvedTargetAge (resolvedFairStages s0 n).edge 4 P target := by
  unfold resolvedTargetAge
  have hCol : ∀ p ∈ P, ∀ i,
      resolvedFairEdge s0 p (target i) =
        (resolvedFairStages s0 n).edge p (target i) :=
    fun p hp i => resolvedFairEdge_eq_live_at s0 n p (target i)
      (Or.inl (hP hp)) (Or.inr (hTarget i))
  rw [resolvedOldCanonical_congr_columns (ell := 4) (resolvedFairEdge s0) P
    (fun p i => (resolvedFairStages s0 n).edge p (target i))
    (fun p i => resolvedFairEdge s0 p (target i)) hCol]
  exact ResolvedLiveStage.oldCanonical_congr_edges (ell := 4)
    (resolvedFairStages s0 n).edge (resolvedFairEdge s0) P
    (fun p i => (resolvedFairStages s0 n).edge p (target i))
    (fun p hp q hq => resolvedFairEdge_eq_live_at s0 n p q
      (Or.inl (hP hp)) (Or.inl (hP hq)))

/-- In the single actual infinite graph, the completed coding round is
age-neutral on every fixed list of surviving original terminals. -/
theorem resolvedFair_coding_reference_neutral
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat)
    {d : Nat} (target : Fin d → Nat)
    (hTarget : ∀ i, target i ∈ resolvedEvenTail (n+1)) :
    resolvedTargetAge (resolvedFairEdge s0) 4
      ((resolvedFairStages s0 (n+1)).old.erase (2*n)) target =
    resolvedTargetAge (resolvedFairEdge s0) 4
      (resolvedFairStages s0 (n+1)).old target := by
  rw [resolvedFair_referenceAge_eq_live s0 (n+1) _
    (Finset.erase_subset _ _) target hTarget,
    resolvedFair_referenceAge_eq_live s0 (n+1) _
    (Finset.Subset.refl _) target hTarget]
  exact (resolvedFairStages_step s0 n).coding_neutral
    (resolvedEvenTail_coding n) target hTarget

/-- The code event in the actual limit creates no new split of two
surviving vertices with identical complete pre-code columns. -/
theorem resolvedFair_coding_no_split
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n v w : Nat)
    (hv : v ∈ resolvedEvenTail (n+1)) (hw : w ∈ resolvedEvenTail (n+1))
    (hBits : ∀ p ∈ (resolvedFairStages s0 (n+1)).old.erase (2*n),
      resolvedFairEdge s0 p v = resolvedFairEdge s0 p w) :
    resolvedFairEdge s0 (2*n) v = resolvedFairEdge s0 (2*n) w := by
  have hc := (resolvedFairStages_step s0 n).coded
  rw [resolvedFairEdge_eq_live_at s0 (n+1) (2*n) v (Or.inl hc) (Or.inr hv),
    resolvedFairEdge_eq_live_at s0 (n+1) (2*n) w (Or.inl hc) (Or.inr hw)]
  apply (resolvedFairStages_step s0 n).coding_no_split
    (resolvedEvenTail_coding n) v w hv hw
  intro p hp
  have hpOld := (Finset.mem_erase.mp hp).2
  rw [← resolvedFairEdge_eq_live_at s0 (n+1) p v (Or.inl hpOld) (Or.inr hv),
    ← resolvedFairEdge_eq_live_at s0 (n+1) p w (Or.inl hpOld) (Or.inr hw)]
  exact hBits p hp

end Kk
