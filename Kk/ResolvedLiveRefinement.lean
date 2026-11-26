import Kk.ResolvedLiveSelectedProjection
import Mathlib.Tactic

/-!
# Construct actual finite class refinements
English proof and audit: docs/resolved_fair_rounds_english_20261126.md.
A bare live state contains the actual entire old-plus-live graph.
Labels are obtained from the occupied finite old-column range.
Private markers for mixed classes can be inserted simultaneously:
every possible partial ordering reads as genuine single-class splits.
-/

namespace Kk

structure ResolvedBareStage (ell : Nat) (W : Set Nat) where
  edge : Nat → Nat → Bool
  old : Finset Nat
  separated : ∀ p ∈ old, p ∉ W
  free : ResolvedLiveFree edge ell old W
  sym : ∀ x y, edge x y = edge y x
  loops : ∀ x, edge x x = false

def ResolvedLiveStage.toBare {d ell : Nat} {W : Set Nat}
    {sort : Nat → Fin d} (s : ResolvedLiveStage d ell W sort) :
    ResolvedBareStage ell W :=
  ⟨s.edge, s.old, s.separated, s.free, s.sym, s.loops⟩

abbrev ResolvedColumnProfile (P : Finset Nat) := (↥P → Bool)

def resolvedColumnProfile (E : Nat → Nat → Bool) (P : Finset Nat)
    (v : Nat) : ResolvedColumnProfile P := fun p => E p.val v

abbrev ResolvedOccupiedProfile (E : Nat → Nat → Bool)
    (P : Finset Nat) (W : Set Nat) :=
  {a : ResolvedColumnProfile P // ∃ v ∈ W, resolvedColumnProfile E P v = a}

/-- Finite labels are constructed from the actual occupied old columns.
No distinctness or occupied-range premise about a proposed list is needed. -/
theorem ResolvedBareStage.exists_exact_labels {ell : Nat} {W : Set Nat}
    (s : ResolvedBareStage ell W) (hW : W.Nonempty) :
    ∃ (d : Nat) (sort : Nat → Fin d) (t : ResolvedLiveStage d ell W sort),
      t.toBare = s ∧ (∀ i, ∃ v ∈ W, sort v = i) ∧
      ResolvedClassExact t.edge t.old W sort := by
  classical
  obtain ⟨v0, hv0⟩ := hW
  let A := ResolvedOccupiedProfile s.edge s.old W
  letI : Fintype A := Fintype.ofFinite A
  let d := Fintype.card A
  let e : A ≃ Fin d := Fintype.equivFin A
  let a0 : A := ⟨resolvedColumnProfile s.edge s.old v0, v0, hv0, rfl⟩
  let a : Nat → A := fun v =>
    if hv : v ∈ W then
      ⟨resolvedColumnProfile s.edge s.old v, v, hv, rfl⟩
    else a0
  let sort : Nat → Fin d := fun v => e (a v)
  let c : Nat → Fin d → Bool := fun p i =>
    if hp : p ∈ s.old then (e.symm i).val ⟨p,hp⟩ else false
  have ha : ∀ v ∈ W, (a v).val = resolvedColumnProfile s.edge s.old v := by
    intro v hv
    simp [a, hv]
  have hColumns : ResolvedLiveColumns s.edge s.old W sort c := by
    intro p hp v hv
    have hBit : c p (sort v) = s.edge p v := by
      simp only [c, dif_pos hp, sort, Equiv.symm_apply_apply]
      rw [ha v hv]
      rfl
    exact ⟨hBit.symm, (s.sym v p).trans hBit.symm⟩
  let t : ResolvedLiveStage d ell W sort :=
    ⟨s.edge, s.old, c, s.separated, hColumns, s.free, s.sym, s.loops⟩
  refine ⟨d, sort, t, ?_, ?_, ?_⟩
  · cases s
    rfl
  · intro i
    obtain ⟨v,hv,hProfile⟩ := (e.symm i).property
    refine ⟨v,hv,?_⟩
    change e (a v) = i
    have heq : a v = e.symm i := Subtype.ext ((ha v hv).trans hProfile)
    rw [heq, Equiv.apply_symm_apply]
  · intro v hv w hw
    change sort v = sort w ↔ ∀ p ∈ s.old, s.edge p v = s.edge p w
    constructor
    · intro h p hp
      have hEq : a v = a w := e.injective h
      have hProfiles := congrArg Subtype.val hEq
      rw [ha v hv, ha w hw] at hProfiles
      exact congrFun hProfiles ⟨p,hp⟩
    · intro h
      apply congrArg e
      apply Subtype.ext
      rw [ha v hv, ha w hw]
      funext p
      exact h p.val p.property

def ResolvedMixedClass {d : Nat} (W : Set Nat) (sort : Nat → Fin d)
    (f : Nat → Bool) (i : Fin d) : Prop :=
  (∃ v ∈ W, sort v = i ∧ f v = true) ∧
    (∃ v ∈ W, sort v = i ∧ f v = false)

def resolvedMarkerName {d : Nat} (P : Finset Nat) (i : Fin d) : Nat :=
  2 * (P.sup (fun p => p) + i.val) + 1

theorem resolvedMarkerName_injective {d : Nat} (P : Finset Nat) :
    Function.Injective (resolvedMarkerName (d := d) P) := by
  intro i j h
  apply Fin.ext
  unfold resolvedMarkerName at h
  omega

noncomputable def resolvedMarkerNames {d : Nat} (P : Finset Nat)
    (W : Set Nat) (sort : Nat → Fin d) (f : Nat → Bool) : Finset Nat := by
  classical
  exact (Finset.univ.filter (ResolvedMixedClass W sort f)).image
    (resolvedMarkerName P)

theorem mem_resolvedMarkerNames {d : Nat} (P : Finset Nat) (W : Set Nat)
    (sort : Nat → Fin d) (f : Nat → Bool) (q : Nat) :
    q ∈ resolvedMarkerNames P W sort f ↔
      ∃ i, ResolvedMixedClass W sort f i ∧ resolvedMarkerName P i = q := by
  classical
  simp only [resolvedMarkerNames, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem resolvedMarkerName_not_old {d : Nat} (P : Finset Nat) (i : Fin d) :
    resolvedMarkerName P i ∉ P := by
  intro h
  have hMax := Finset.le_sup (f := fun p : Nat => p) h
  unfold resolvedMarkerName at hMax
  omega

theorem resolvedMarkerName_not_live {d : Nat} (P : Finset Nat)
    (W : Set Nat) (hEven : ∀ v ∈ W, v % 2 = 0) (i : Fin d) :
    resolvedMarkerName P i ∉ W := by
  intro h
  have hMod := hEven _ h
  unfold resolvedMarkerName at hMod
  omega

/-- The only new edges go from a mixed-class marker to its positive
child. The test is fixed on the entire live domain. -/
noncomputable def resolvedMarkerEdge {d : Nat} (E : Nat → Nat → Bool)
    (P : Finset Nat) (W : Set Nat) (sort : Nat → Fin d)
    (f : Nat → Bool) (x y : Nat) : Bool := by
  classical
  let Q := resolvedMarkerNames P W sort f
  let link := fun a b => decide (b ∈ W ∧
    ∃ i : Fin d, resolvedMarkerName P i = a ∧ sort b = i ∧ f b = true)
  exact if x ∈ Q then link x y else if y ∈ Q then link y x else E x y

theorem resolvedMarkerEdge_off {d : Nat} (E : Nat → Nat → Bool)
    (P : Finset Nat) (W : Set Nat) (sort : Nat → Fin d)
    (f : Nat → Bool) {x y : Nat}
    (hx : x ∉ resolvedMarkerNames P W sort f)
    (hy : y ∉ resolvedMarkerNames P W sort f) :
    resolvedMarkerEdge E P W sort f x y = E x y := by
  classical
  simp [resolvedMarkerEdge, hx, hy]

theorem resolvedMarkerEdge_positive_iff {d : Nat} (E : Nat → Nat → Bool)
    (P : Finset Nat) (W : Set Nat) (sort : Nat → Fin d) (f : Nat → Bool)
    (i : Fin d) (hm : ResolvedMixedClass W sort f i) (v : Nat) :
    resolvedMarkerEdge E P W sort f (resolvedMarkerName P i) v = true ↔
      v ∈ W ∧ sort v = i ∧ f v = true := by
  classical
  have hq := (mem_resolvedMarkerNames P W sort f (resolvedMarkerName P i)).2
    ⟨i, hm, rfl⟩
  simp only [resolvedMarkerEdge, if_pos hq, decide_eq_true_eq]
  constructor
  · rintro ⟨hv,j,hName,hSort,hf⟩
    have hij : j = i := resolvedMarkerName_injective P hName
    exact ⟨hv,hSort.trans hij,hf⟩
  · rintro ⟨hv,hs,hf⟩
    exact ⟨hv,i,rfl,hs,hf⟩

private theorem resolvedMarker_bool_eq (a b : Bool)
    (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

namespace ResolvedBareStage

variable {W : Set Nat} {d : Nat}

/-- Insert all private markers at once. Safety concerns the entire
(possibly infinite) live graph. The positive child set is triangle-free. -/
noncomputable def refineBatch (s : ResolvedBareStage 4 W)
    (sort : Nat → Fin d) (f : Nat → Bool)
    (hEven : ∀ v ∈ W, v % 2 = 0)
    (hSafe : ∀ C : Finset Nat, (∀ x ∈ C, x ∈ W ∧ f x = true) →
      IsDirectedCliqueOn s.edge C → C.card < 3) :
    ResolvedBareStage 4 W := by
  classical
  let Q := resolvedMarkerNames s.old W sort f
  let E := resolvedMarkerEdge s.edge s.old W sort f
  have hQW : ∀ q ∈ Q, q ∉ W := by
    intro q hq
    obtain ⟨i, _, hi⟩ := (mem_resolvedMarkerNames s.old W sort f q).1 hq
    rw [← hi]
    exact resolvedMarkerName_not_live s.old W hEven i
  have hQP : ∀ p ∈ s.old, p ∉ Q := by
    intro p hp hq
    obtain ⟨i, _, hi⟩ := (mem_resolvedMarkerNames s.old W sort f p).1 hq
    exact resolvedMarkerName_not_old s.old i (hi.symm ▸ hp)
  refine ⟨E,s.old ∪ Q,?_,?_,?_,?_⟩
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact s.separated p hp
    · exact hQW p hp
  · intro C hC hc
    by_cases hHit : ∃ q ∈ C, q ∈ Q
    · obtain ⟨q,hqC,hqQ⟩ := hHit
      obtain ⟨i,hm,hi⟩ := (mem_resolvedMarkerNames s.old W sort f q).1 hqQ
      let R := C.erase q
      have hR : ∀ y ∈ R, y ∈ W ∧ f y = true := by
        intro y hy
        obtain ⟨hyq,hyC⟩ := Finset.mem_erase.mp hy
        have hEdge := hc q hqC y hyC hyq.symm
        change resolvedMarkerEdge s.edge s.old W sort f q y = true at hEdge
        rw [← hi] at hEdge
        have hPos := (resolvedMarkerEdge_positive_iff s.edge s.old W sort f i hm y).1 hEdge
        exact ⟨hPos.1,hPos.2.2⟩
      have hRc : IsDirectedCliqueOn s.edge R := by
        intro x hx y hy hxy
        have hxQ : x ∉ Q := fun h => hQW x h (hR x hx).1
        have hyQ : y ∉ Q := fun h => hQW y h (hR y hy).1
        have hEdge := hc x (Finset.mem_erase.mp hx).2 y (Finset.mem_erase.mp hy).2 hxy
        change resolvedMarkerEdge s.edge s.old W sort f x y = true at hEdge
        rw [resolvedMarkerEdge_off s.edge s.old W sort f hxQ hyQ] at hEdge
        exact hEdge
      have hSmall := hSafe R hR hRc
      have hCard := Finset.card_erase_of_mem hqC
      change R.card = C.card - 1 at hCard
      omega
    · have hNo : ∀ x ∈ C, x ∉ Q := fun x hx hq => hHit ⟨x,hx,hq⟩
      apply s.free C
      · intro x hx
        rcases hC x hx with hp | hw
        · rcases Finset.mem_union.mp hp with hp | hq
          · exact Or.inl hp
          · exact False.elim (hNo x hx hq)
        · exact Or.inr hw
      · intro x hx y hy hxy
        have hEdge := hc x hx y hy hxy
        change resolvedMarkerEdge s.edge s.old W sort f x y = true at hEdge
        rw [resolvedMarkerEdge_off s.edge s.old W sort f (hNo x hx) (hNo y hy)] at hEdge
        exact hEdge
  · intro x y
    by_cases hx : x ∈ Q <;> by_cases hy : y ∈ Q
    · simp [E, resolvedMarkerEdge, Q, hx, hy, hQW x hx, hQW y hy]
    · simp [E, resolvedMarkerEdge, Q, hx, hy]
    · simp [E, resolvedMarkerEdge, Q, hx, hy]
    · simp [E, resolvedMarkerEdge, Q, hx, hy, s.sym x y]
  · intro x
    by_cases hx : x ∈ Q
    · simp [E, resolvedMarkerEdge, Q, hx, hQW x hx]
    · simp [E, resolvedMarkerEdge, Q, hx, s.loops]

theorem refineBatch_preserves (s : ResolvedBareStage 4 W)
    (sort : Nat → Fin d) (f : Nat → Bool) (hEven : ∀ v ∈ W, v % 2 = 0)
    (hSafe : ∀ C : Finset Nat, (∀ x ∈ C, x ∈ W ∧ f x = true) →
      IsDirectedCliqueOn s.edge C → C.card < 3)
    (x y : Nat) (hx : x ∈ s.old ∨ x ∈ W) (hy : y ∈ s.old ∨ y ∈ W) :
    (s.refineBatch sort f hEven hSafe).edge x y = s.edge x y := by
  have hNo : ∀ v, v ∈ s.old ∨ v ∈ W →
      v ∉ resolvedMarkerNames s.old W sort f := by
    intro v hv hq
    obtain ⟨i,_,hi⟩ := (mem_resolvedMarkerNames s.old W sort f v).1 hq
    rcases hv with hp | hw
    · exact resolvedMarkerName_not_old s.old i (hi.symm ▸ hp)
    · exact resolvedMarkerName_not_live s.old W hEven i (hi.symm ▸ hw)
  exact resolvedMarkerEdge_off s.edge s.old W sort f (hNo x hx) (hNo y hy)

/-- The resulting complete column partition is exactly the common
refinement of the original partition and the Boolean test. -/
theorem refineBatch_exact (s : ResolvedBareStage 4 W)
    (sort : Nat → Fin d) (f : Nat → Bool) (hEven : ∀ v ∈ W, v % 2 = 0)
    (hSafe : ∀ C : Finset Nat, (∀ x ∈ C, x ∈ W ∧ f x = true) →
      IsDirectedCliqueOn s.edge C → C.card < 3)
    (hExact : ResolvedClassExact s.edge s.old W sort) :
    ResolvedClassExact (s.refineBatch sort f hEven hSafe).edge
      (s.refineBatch sort f hEven hSafe).old W (fun v => (sort v, f v)) := by
  classical
  let t := s.refineBatch sort f hEven hSafe
  intro v hv w hw
  change (sort v, f v) = (sort w, f w) ↔ ∀ p ∈ t.old, t.edge p v = t.edge p w
  constructor
  · intro h p hp
    have hc : sort v = sort w := congrArg Prod.fst h
    have hf : f v = f w := congrArg Prod.snd h
    change p ∈ s.old ∪ resolvedMarkerNames s.old W sort f at hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rw [s.refineBatch_preserves sort f hEven hSafe p v (Or.inl hp) (Or.inr hv),
          s.refineBatch_preserves sort f hEven hSafe p w (Or.inl hp) (Or.inr hw)]
      exact (hExact v hv w hw).1 hc p hp
    · obtain ⟨i,hm,hi⟩ := (mem_resolvedMarkerNames s.old W sort f p).1 hp
      subst p
      apply resolvedMarker_bool_eq
      change resolvedMarkerEdge s.edge s.old W sort f (resolvedMarkerName s.old i) v = true ↔
        resolvedMarkerEdge s.edge s.old W sort f (resolvedMarkerName s.old i) w = true
      rw [resolvedMarkerEdge_positive_iff s.edge s.old W sort f i hm v,
        resolvedMarkerEdge_positive_iff s.edge s.old W sort f i hm w]
      simp [hv,hw,hc,hf]
  · intro h
    have hc : sort v = sort w := by
      apply (hExact v hv w hw).2
      intro p hp
      have hbit := h p (show p ∈ t.old from Finset.mem_union.mpr (Or.inl hp))
      rw [s.refineBatch_preserves sort f hEven hSafe p v (Or.inl hp) (Or.inr hv),
          s.refineBatch_preserves sort f hEven hSafe p w (Or.inl hp) (Or.inr hw)] at hbit
      exact hbit
    apply Prod.ext hc
    by_contra hNe
    have hMixed : ResolvedMixedClass W sort f (sort v) := by
      cases hV : f v <;> cases hW : f w
      · exact False.elim (hNe (hV.trans hW.symm))
      · exact ⟨⟨w,hw,hc.symm,hW⟩,⟨v,hv,rfl,hV⟩⟩
      · exact ⟨⟨v,hv,rfl,hV⟩,⟨w,hw,hc.symm,hW⟩⟩
      · exact False.elim (hNe (hV.trans hW.symm))
    let q := resolvedMarkerName s.old (sort v)
    have hq : q ∈ t.old := Finset.mem_union.mpr (Or.inr
      ((mem_resolvedMarkerNames s.old W sort f q).2 ⟨sort v,hMixed,rfl⟩))
    have hbit := h q hq
    change resolvedMarkerEdge s.edge s.old W sort f q v =
      resolvedMarkerEdge s.edge s.old W sort f q w at hbit
    have hIff : f v = true ↔ f w = true := by
      have hvPos := resolvedMarkerEdge_positive_iff s.edge s.old W sort f (sort v) hMixed v
      have hwPos := resolvedMarkerEdge_positive_iff s.edge s.old W sort f (sort v) hMixed w
      change resolvedMarkerEdge s.edge s.old W sort f q v = true ↔
        v ∈ W ∧ sort v = sort v ∧ f v = true at hvPos
      change resolvedMarkerEdge s.edge s.old W sort f q w = true ↔
        w ∈ W ∧ sort w = sort v ∧ f w = true at hwPos
      rw [hbit] at hvPos
      exact (by simpa [hv,hw,hc.symm] using hvPos.symm.trans hwPos)
    exact hNe (resolvedMarker_bool_eq _ _ hIff)

/-- Each marker is a genuine split even after any subset of the other
markers has been inserted. The positive neighbourhood is exactly the
positive child of one actual class of the complete preceding prefix. -/
theorem refineBatch_single_split (s : ResolvedBareStage 4 W)
    (sort : Nat → Fin d) (f : Nat → Bool) (hEven : ∀ v ∈ W, v % 2 = 0)
    (hSafe : ∀ C : Finset Nat, (∀ x ∈ C, x ∈ W ∧ f x = true) →
      IsDirectedCliqueOn s.edge C → C.card < 3)
    (hExact : ResolvedClassExact s.edge s.old W sort)
    (i : Fin d) (hm : ResolvedMixedClass W sort f i)
    (R : Finset Nat) (hR : R ⊆ resolvedMarkerNames s.old W sort f)
    (hNot : resolvedMarkerName s.old i ∉ R) :
    let t := s.refineBatch sort f hEven hSafe
    let q := resolvedMarkerName s.old i
    ∃ v ∈ W, ∃ w ∈ W,
      (∀ p ∈ s.old ∪ R, t.edge p v = t.edge p w) ∧
      t.edge q v = true ∧ t.edge q w = false ∧
      (∀ x ∈ W, t.edge q x = true ↔
        (∀ p ∈ s.old ∪ R, t.edge p x = t.edge p v) ∧ f x = true) := by
  classical
  let t := s.refineBatch sort f hEven hSafe
  obtain ⟨⟨v,hv,hvi,hfv⟩,⟨w,hw,hwi,hfw⟩⟩ := hm
  have hClass : ∀ x ∈ W, sort x = i ↔ ∀ p ∈ s.old ∪ R, t.edge p x = t.edge p v := by
    intro x hx
    constructor
    · intro hxi p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · rw [s.refineBatch_preserves sort f hEven hSafe p x (Or.inl hp) (Or.inr hx),
            s.refineBatch_preserves sort f hEven hSafe p v (Or.inl hp) (Or.inr hv)]
        exact (hExact x hx v hv).1 (hxi.trans hvi.symm) p hp
      · obtain ⟨j,hmj,hj⟩ := (mem_resolvedMarkerNames s.old W sort f p).1 (hR hp)
        have hji : j ≠ i := by
          intro he
          subst j
          exact hNot (hj.symm ▸ hp)
        subst p
        apply resolvedMarker_bool_eq
        change resolvedMarkerEdge s.edge s.old W sort f (resolvedMarkerName s.old j) x = true ↔
          resolvedMarkerEdge s.edge s.old W sort f (resolvedMarkerName s.old j) v = true
        rw [resolvedMarkerEdge_positive_iff s.edge s.old W sort f j hmj x,
            resolvedMarkerEdge_positive_iff s.edge s.old W sort f j hmj v]
        simp [hxi,hvi,hji.symm]
    · intro h
      have hEq : sort x = sort v := by
        apply (hExact x hx v hv).2
        intro p hp
        have hbit := h p (Finset.mem_union.mpr (Or.inl hp))
        rw [s.refineBatch_preserves sort f hEven hSafe p x (Or.inl hp) (Or.inr hx),
            s.refineBatch_preserves sort f hEven hSafe p v (Or.inl hp) (Or.inr hv)] at hbit
        exact hbit
      exact hEq.trans hvi
  have hPos : ∀ x ∈ W, t.edge (resolvedMarkerName s.old i) x = true ↔
      sort x = i ∧ f x = true := by
    intro x hx
    exact (resolvedMarkerEdge_positive_iff s.edge s.old W sort f i hm x).trans
      (by simp [hx])
  refine ⟨v,hv,w,hw,?_,(hPos v hv).2 ⟨hvi,hfv⟩,?_,?_⟩
  · intro p hp
    exact ((hClass w hw).1 hwi p hp).symm
  · have hn : ¬ t.edge (resolvedMarkerName s.old i) w = true := by
      rw [hPos w hw]
      simp [hfw]
    cases h : t.edge (resolvedMarkerName s.old i) w <;> simp_all
  · intro x hx
    rw [hPos x hx, hClass x hx]

/-- Singleton-isolation test and adjacency-to-pivot test are safe in a
K4-free live graph. The latter uses a genuine fourth distinct vertex. -/
theorem singleton_test_safe (s : ResolvedBareStage 4 W) (r : Nat) :
    ∀ C : Finset Nat, (∀ x ∈ C, x ∈ W ∧ decide (x = r) = true) →
      IsDirectedCliqueOn s.edge C → C.card < 3 := by
  intro C hC _
  have hSub : C ⊆ ({r} : Finset Nat) := by
    intro x hx
    exact Finset.mem_singleton.mpr (of_decide_eq_true (hC x hx).2)
  have hCard := Finset.card_le_card hSub
  simp only [Finset.card_singleton] at hCard
  omega

theorem neighbour_test_safe (s : ResolvedBareStage 4 W) (r : Nat) (hr : r ∈ W) :
    ∀ C : Finset Nat, (∀ x ∈ C, x ∈ W ∧ s.edge r x = true) →
      IsDirectedCliqueOn s.edge C → C.card < 3 := by
  classical
  intro C hC hc
  have hrNot : r ∉ C := by
    intro h
    have hb := (hC r h).2
    rw [s.loops] at hb
    cases hb
  have hClique : IsDirectedCliqueOn s.edge (insert r C) := by
    intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with he | hx
    · subst x
      rcases Finset.mem_insert.mp hy with he | hy
      · exact False.elim (hxy he.symm)
      · exact (hC y hy).2
    · rcases Finset.mem_insert.mp hy with he | hy
      · subst y
        exact (s.sym x r).trans (hC x hx).2
      · exact hc x hx y hy hxy
  have hFree := s.free (insert r C) (by
    intro x hx
    rcases Finset.mem_insert.mp hx with he | hx
    · exact Or.inr (he.symm ▸ hr)
    · exact Or.inr (hC x hx).1) hClique
  rw [Finset.card_insert_of_notMem hrNot] at hFree
  omega

end ResolvedBareStage
end Kk
