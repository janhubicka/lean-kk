import Kk.FiniteOldColumnAge
import Kk.PhysicalCanonicalSortTransport
import Kk.TrackFTypePrefixCanonicalAgeSandwich
import Mathlib.Tactic

/-!
# Actual (possibly infinite) live future age
English proof: docs/resolved_live_future_normalization_english_20261126.md.
The finite witness pool contains only vectors realized by actual cliques.
It is not the universal permitted continuation age.
-/

namespace Kk

/-- No nonempty support on zero labels exists. This treats an empty
selected front without requiring a total sort map Nat → Fin 0. -/
theorem resolvedZeroSortAge_eq (ell : Nat)
    (A B : IntegerGraphSupport 0 ell → Nat) : A = B := by
  funext T
  obtain ⟨i, _⟩ := T.2.1
  exact Fin.elim0 i

def ResolvedLiveFree (E : Nat → Nat → Bool) (ell : Nat)
    (P : Finset Nat) (W : Set Nat) : Prop :=
  ∀ s : Finset Nat, (∀ x ∈ s, x ∈ P ∨ x ∈ W) →
    IsDirectedCliqueOn E s → s.card < ell

def ResolvedLiveColumns {d : Nat} (E : Nat → Nat → Bool)
    (P : Finset Nat) (W : Set Nat) (sort : Nat → Fin d)
    (c : Nat → Fin d → Bool) : Prop :=
  ∀ p ∈ P, ∀ v ∈ W, E p v = c p (sort v) ∧ E v p = c p (sort v)

noncomputable def resolvedActualVectors {d : Nat}
    (E : Nat → Nat → Bool) (ell : Nat) (W : Set Nat)
    (sort : Nat → Fin d) : Finset (IntegerCliqueWeights d ell) := by
  classical
  exact Finset.univ.filter (fun w =>
    ∃ (s : Finset Nat) (hs : s.card < ell),
      (∀ x ∈ s, x ∈ W) ∧ IsDirectedCliqueOn E s ∧
      integerCliqueWeightsOfFinset sort s hs = w)

theorem mem_resolvedActualVectors {d ell : Nat}
    (E : Nat → Nat → Bool) (W : Set Nat) (sort : Nat → Fin d)
    (w : IntegerCliqueWeights d ell) :
    w ∈ resolvedActualVectors E ell W sort ↔
      ∃ (s : Finset Nat) (hs : s.card < ell),
        (∀ x ∈ s, x ∈ W) ∧ IsDirectedCliqueOn E s ∧
        integerCliqueWeightsOfFinset sort s hs = w := by
  classical
  simp only [resolvedActualVectors, Finset.mem_filter, Finset.mem_univ, true_and]

noncomputable def resolvedActualAge {d : Nat}
    (E : Nat → Nat → Bool) (ell : Nat) (W : Set Nat)
    (sort : Nat → Fin d) (T : IntegerGraphSupport d ell) : Nat :=
  (resolvedActualVectors E ell W sort).sup (fun w => integerCliqueOnSupport w T)

theorem resolvedActualAge_count_le {d ell : Nat}
    (E : Nat → Nat → Bool) (W : Set Nat) (sort : Nat → Fin d)
    (s : Finset Nat) (hs : s.card < ell)
    (hW : ∀ x ∈ s, x ∈ W) (hClique : IsDirectedCliqueOn E s)
    (T : IntegerGraphSupport d ell) :
    (s.filter (fun v => sort v ∈ T.1)).card ≤ resolvedActualAge E ell W sort T := by
  classical
  have hm := (mem_resolvedActualVectors E W sort
    (integerCliqueWeightsOfFinset sort s hs)).2 ⟨s, hs, hW, hClique, rfl⟩
  rw [← integerCliqueOnSupport_of_finset sort s hs T]
  exact Finset.le_sup (f := fun w : IntegerCliqueWeights d ell =>
    integerCliqueOnSupport w T) hm

theorem resolvedActualAge_attained {d ell : Nat}
    (E : Nat → Nat → Bool) (W : Set Nat) (sort : Nat → Fin d)
    (hell : 0 < ell) (T : IntegerGraphSupport d ell) :
    ∃ (w : IntegerCliqueWeights d ell),
      w ∈ resolvedActualVectors E ell W sort ∧
      integerCliqueOnSupport w T = resolvedActualAge E ell W sort T := by
  classical
  have hEmpty : (∅ : Finset Nat).card < ell := by simpa using hell
  let w0 := integerCliqueWeightsOfFinset sort (∅ : Finset Nat) hEmpty
  have hm : w0 ∈ resolvedActualVectors E ell W sort :=
    (mem_resolvedActualVectors E W sort w0).2
      ⟨∅, hEmpty, (by simp), (by simp [IsDirectedCliqueOn]), rfl⟩
  obtain ⟨w, hw, hmax⟩ := Finset.exists_mem_eq_sup
    (resolvedActualVectors E ell W sort) ⟨w0, hm⟩
    (fun w => integerCliqueOnSupport w T)
  exact ⟨w, hw, hmax.symm⟩

/-- A support maximum is attained by an actual clique wholly supported there.
No assertion of universal realization of arbitrary feasible vectors. -/
theorem resolvedActualAge_attained_supported {d ell : Nat}
    (E : Nat → Nat → Bool) (W : Set Nat) (sort : Nat → Fin d)
    (hell : 0 < ell) (T : IntegerGraphSupport d ell) :
    ∃ s : Finset Nat, s.card < ell ∧
      (∀ x ∈ s, x ∈ W ∧ sort x ∈ T.1) ∧ IsDirectedCliqueOn E s ∧
      s.card = resolvedActualAge E ell W sort T := by
  classical
  obtain ⟨w, hw, hmax⟩ := resolvedActualAge_attained E W sort hell T
  obtain ⟨s, hs, hW, hClique, hEq⟩ :=
    (mem_resolvedActualVectors E W sort w).1 hw
  let u := s.filter (fun v => sort v ∈ T.1)
  refine ⟨u, lt_of_le_of_lt (Finset.card_le_card (Finset.filter_subset _ _)) hs,
    ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxs, hxT⟩ := Finset.mem_filter.mp hx
    exact ⟨hW x hxs, hxT⟩
  · intro x hx y hy hxy
    exact hClique x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
  · calc
      u.card = integerCliqueOnSupport (integerCliqueWeightsOfFinset sort s hs) T :=
        (integerCliqueOnSupport_of_finset sort s hs T).symm
      _ = integerCliqueOnSupport w T := by rw [hEq]
      _ = _ := hmax

theorem resolvedActualAge_is_age {d ell : Nat}
    (E : Nat → Nat → Bool) (W : Set Nat) (sort : Nat → Fin d)
    (hell : 1 < ell) (hOccupied : ∀ i, ∃ v ∈ W, sort v = i) :
    IsIntegerGraphAge d ell (resolvedActualAge E ell W sort) := by
  classical
  constructor
  · intro T
    obtain ⟨i, hi⟩ := T.2.1
    obtain ⟨v, hv, hvi⟩ := hOccupied i
    have hs : ({v} : Finset Nat).card < ell := by simpa using hell
    have hc : IsDirectedCliqueOn E ({v} : Finset Nat) := by
      intro x hx y hy hxy
      have hxv : x = v := Finset.mem_singleton.mp hx
      have hyv : y = v := Finset.mem_singleton.mp hy
      exact False.elim (hxy (hxv.trans hyv.symm))
    have hb := resolvedActualAge_count_le E W sort {v} hs
      (by intro x hx; simpa only [Finset.mem_singleton.mp hx] using hv)
      hc T
    constructor
    · simpa [hvi, hi] using hb
    · unfold resolvedActualAge
      exact Finset.sup_le (fun w _ => integerCliqueOnSupport_le w T)
  · intro T
    obtain ⟨w, hw, hmax⟩ := resolvedActualAge_attained E W sort (by omega) T
    exact ⟨w, (by intro U; exact Finset.le_sup
      (f := fun z : IntegerCliqueWeights d ell => integerCliqueOnSupport z U) hw), hmax⟩

theorem resolvedLiveFree_finite_union {ell : Nat}
    (E : Nat → Nat → Bool) (P s : Finset Nat) (W : Set Nat)
    (hFree : ResolvedLiveFree E ell P W) (hs : ∀ v ∈ s, v ∈ W) :
    finitePoolCliqueCheck E ell (P ∪ s) = false := by
  apply (finitePoolCliqueCheck_false_iff_capacity_lt E ell (P ∪ s)).2
  obtain ⟨q, hq, hc, hCard⟩ := finiteDirectedCliqueCapacity_attained E (P ∪ s)
  rw [← hCard]
  apply hFree q _ hc
  intro v hv
  rcases Finset.mem_union.mp (hq hv) with hp | hvs
  · exact Or.inl hp
  · exact Or.inr (hs v hvs)

/-- The actual maximum capacities lie below the exact permitted gluing age.
All finite subsets of the possibly infinite future are covered. -/
theorem resolvedActualAge_le_oldCanonical {d ell : Nat}
    (E : Nat → Nat → Bool) (P : Finset Nat) (W : Set Nat)
    (sort : Nat → Fin d) (c : Nat → Fin d → Bool)
    (hSep : ∀ p ∈ P, p ∉ W)
    (hColumns : ResolvedLiveColumns E P W sort c)
    (hFree : ResolvedLiveFree E ell P W) :
    AgeLe (resolvedActualAge E ell W sort)
      (integerGraphAgeCanonical d ell (finiteOldColumnRawBound E ell d P c)) := by
  classical
  intro T
  unfold resolvedActualAge
  apply Finset.sup_le
  intro w hw
  obtain ⟨s, hs, hW, hc, hEq⟩ :=
    (mem_resolvedActualVectors E W sort w).1 hw
  have hDisj : Disjoint P s := by
    apply Finset.disjoint_left.mpr
    intro x hxP hxs
    exact hSep x hxP (hW x hxs)
  have hCol : ∀ p ∈ P, ∀ v ∈ s,
      E p v = c p (sort v) ∧ E v p = c p (sort v) :=
    fun p hp v hv => hColumns p hp v (hW v hv)
  have hRaw := finiteOldFuture_free_implies_raw_support E ell d
    P s sort c hDisj hCol (resolvedLiveFree_finite_union E P s W hFree hW)
    s (Finset.Subset.refl s) hc
  apply witnessValue_le_canonical
    (integerCliqueOnSupport (d := d) (ell := ell))
    (finiteOldColumnRawBound E ell d P c) w _ T
  intro U
  rw [← hEq, integerCliqueOnSupport_of_finset]
  exact hRaw U

theorem resolvedActualAge_congr {d ell : Nat}
    (E E' : Nat → Nat → Bool) (W : Set Nat) (sort : Nat → Fin d)
    (hEq : ∀ x ∈ W, ∀ y ∈ W, E' x y = E x y) :
    resolvedActualAge E' ell W sort = resolvedActualAge E ell W sort := by
  classical
  have hVectors : resolvedActualVectors E' ell W sort =
      resolvedActualVectors E ell W sort := by
    ext w
    rw [mem_resolvedActualVectors, mem_resolvedActualVectors]
    constructor <;> rintro ⟨s, hs, hW, hc, he⟩ <;>
      refine ⟨s, hs, hW, ?_, he⟩
    · intro x hx y hy hxy
      rw [← hEq x (hW x hx) y (hW y hy)]
      exact hc x hx y hy hxy
    · intro x hx y hy hxy
      rw [hEq x (hW x hx) y (hW y hy)]
      exact hc x hx y hy hxy
  funext T
  unfold resolvedActualAge
  rw [hVectors]

theorem resolvedOldCanonical_antitone {d ell : Nat}
    (E : Nat → Nat → Bool) (P Q : Finset Nat)
    (hPQ : P ⊆ Q) (c : Nat → Fin d → Bool) :
    AgeLe
      (integerGraphAgeCanonical d ell (finiteOldColumnRawBound E ell d Q c))
      (integerGraphAgeCanonical d ell (finiteOldColumnRawBound E ell d P c)) := by
  apply integerGraphAgeCanonical_mono_raw
  intro T
  have hSub : oldSupportCommonNeighbourPool P c T.1 ⊆
      oldSupportCommonNeighbourPool Q c T.1 := by
    classical
    intro x hx
    obtain ⟨hp, hbits⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hPQ hp, hbits⟩
  have hCap := finiteDirectedCliqueCapacity_mono E _ _ hSub
  unfold finiteOldColumnRawBound
  omega

/-- Direct survivor-neutrality principle. Normalization of the survivor
age before the move and actual live safety afterwards suffice. -/
theorem resolvedLive_survivor_neutral_of_saturation {d ell : Nat}
    (E : Nat → Nat → Bool) (P Q : Finset Nat) (W : Set Nat)
    (sort : Nat → Fin d) (c : Nat → Fin d → Bool)
    (hPQ : P ⊆ Q) (hSep : ∀ q ∈ Q, q ∉ W)
    (hColumns : ResolvedLiveColumns E Q W sort c)
    (hFree : ResolvedLiveFree E ell Q W)
    (hSat : integerGraphAgeCanonical d ell (finiteOldColumnRawBound E ell d P c) =
      resolvedActualAge E ell W sort) :
    integerGraphAgeCanonical d ell (finiteOldColumnRawBound E ell d Q c) =
      integerGraphAgeCanonical d ell (finiteOldColumnRawBound E ell d P c) := by
  have hLe := resolvedOldCanonical_antitone (ell := ell) E P Q hPQ c
  have hGe := resolvedActualAge_le_oldCanonical (ell := ell)
    E Q W sort c hSep hColumns hFree
  funext T
  apply Nat.le_antisymm (hLe T)
  rw [hSat]
  exact hGe T

/-- Actual support maxima pull back to the genuine surviving class union.
The sort map is injective, and no surviving old class loses vertices. -/
theorem resolvedActualAge_survivor_reindex {d e ell : Nat}
    (E : Nat → Nat → Bool) (W W' : Set Nat)
    (sort : Nat → Fin d) (sort' : Nat → Fin e)
    (pi : Fin e → Fin d) (hell : 0 < ell)
    (hInj : Function.Injective pi)
    (hW : ∀ v, v ∈ W' ↔ v ∈ W ∧ ∃ i, sort v = pi i)
    (hSort : ∀ v ∈ W', sort v = pi (sort' v))
    (T : IntegerGraphSupport e ell) :
    resolvedActualAge E ell W' sort' T =
      resolvedActualAge E ell W sort (integerGraphSupportImage pi T) := by
  classical
  apply Nat.le_antisymm
  · obtain ⟨s, hs, hMem, hc, hCard⟩ :=
      resolvedActualAge_attained_supported E W' sort' hell T
    have hOldW : ∀ v ∈ s, v ∈ W :=
      fun v hv => ((hW v).1 (hMem v hv).1).1
    have hFilter : s.filter (fun v => sort v ∈ (integerGraphSupportImage pi T).1) = s := by
      ext v
      simp only [Finset.mem_filter]
      constructor
      · exact And.left
      · intro hv
        refine ⟨hv, ?_⟩
        change sort v ∈ T.1.image pi
        exact Finset.mem_image.mpr ⟨sort' v, (hMem v hv).2, (hSort v (hMem v hv).1).symm⟩
    have hLe := resolvedActualAge_count_le E W sort s hs hOldW hc
      (integerGraphSupportImage pi T)
    rw [hFilter, hCard] at hLe
    exact hLe
  · obtain ⟨s, hs, hMem, hc, hCard⟩ :=
      resolvedActualAge_attained_supported E W sort hell (integerGraphSupportImage pi T)
    have hNew : ∀ v ∈ s, v ∈ W' ∧ sort' v ∈ T.1 := by
      intro v hv
      obtain ⟨hvW, hvImage⟩ := hMem v hv
      change sort v ∈ T.1.image pi at hvImage
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hvImage
      have hvW' := (hW v).2 ⟨hvW, i, he.symm⟩
      have hEq : sort' v = i := hInj ((hSort v hvW').symm.trans he.symm)
      exact ⟨hvW', by rw [hEq]; exact hi⟩
    have hFilter : s.filter (fun v => sort' v ∈ T.1) = s := by
      ext v
      simp only [Finset.mem_filter]
      exact ⟨And.left, fun hv => ⟨hv, (hNew v hv).2⟩⟩
    have hLe := resolvedActualAge_count_le E W' sort' s hs
      (fun v hv => (hNew v hv).1) hc T
    rw [hFilter, hCard] at hLe
    exact hLe

end Kk
