import Kk.TrackFGlobalLabelledNextSafety
import Mathlib.Tactic

/-!
# Track F: complete finite sorted graph realization in rank-zero coding fibres

English-first proof and twelve hostile checks committed before Lean:
docs/track_f_rankzero_finite_sorted_realization_english_audit.md

A finite requested graph B obeying ALL true source RAW sorted clique
inequalities can be realized by ACTUAL original coding vertices in
rank-zero large/dense source fibres, one requested vertex at a time.

The induction maintains a FULL physical partial embedding, original
source-column bits, original-index chronology, a total but mutable
source-sort bookkeeping map, and ACTUAL coding witnesses in their
designated rank-zero fibres.

The verified global feasible-next theorem (#352) discharges the
K_(ell-1)-free extension test at each step. No Henson left-density
hypothesis is postulated beyond the explicit rank-zero largeness of
the chosen ACTUAL coding sets. No diary or BRD characterization
is assumed; higher-rank and target multi-sort realization remain open.
-/

namespace Kk

/-- A physically realized initial segment [0,n) of a requested
finite sorted graph B in ACTUAL original source graph E.

A partial embedding f need only be injective/chronological on the
selected initial segment, not on the whole ambient Nat index set.
The sort bookkeeping map can be updated at each fresh selected
original; it is not a new graph relation.

The old-column invariant ensures the genuine original old source
neighbourhood of every chosen coding vertex exactly equals the
specified source sort's old neighbour set U_(σ i). -/
structure TrackFRankZeroRealizedPrefix
    (d ell m n : Nat)
    (E B : Nat → Nat → Bool)
    (U : Fin d → Finset Nat)
    (σ : Nat → Fin d)
    (S : Fin d → Set (HensonOneType ell E)) where
  f : Nat → Nat
  sortMap : Nat → Fin d
  front : Nat
  frontLower : m ≤ front
  injective : Set.InjOn f (↑(Finset.range n) : Set Nat)
  bounds : ∀ i : Nat, i < n → m ≤ f i ∧ f i < front
  ordered : ∀ i j : Nat, i < j → j < n → f i < f j
  induced : ∀ i : Nat, i < n → ∀ j : Nat, j < n →
    i ≠ j → E (f i) (f j) = B i j
  sorted : ∀ i : Nat, i < n → sortMap (f i) = σ i
  oldColumns : ∀ i : Nat, i < n → ∀ p : Nat, p < m →
    E p (f i) = decide (p ∈ U (σ i))
  coding : ∀ i : Nat, i < n →
    ∃ x : HensonOneType ell E,
      x.level = f i ∧ x ∈ S (σ i)

/-- The EMPTY requested graph is physically realized: all
selected-vertex statements are vacuous. The given σ:Nat→Fin d
provides a dummy value even when no source sort index is used. -/
theorem trackFRankZeroRealizedPrefix_empty
    (d ell m : Nat)
    (E B : Nat → Nat → Bool)
    (U : Fin d → Finset Nat)
    (σ : Nat → Fin d)
    (S : Fin d → Set (HensonOneType ell E)) :
    Nonempty (TrackFRankZeroRealizedPrefix
      d ell m 0 E B U σ S) := by
  refine ⟨{
    f := fun _ => 0
    sortMap := fun _ => σ 0
    front := m
    frontLower := le_refl m
    injective := ?_
    bounds := ?_
    ordered := ?_
    induced := ?_
    sorted := ?_
    oldColumns := ?_
    coding := ?_
  }⟩
  · intro i hi
    simp at hi
  · intro i hi
    omega
  · intro i j hij hj
    omega
  · intro i hi
    omega
  · intro i hi
    omega
  · intro i hi
    omega
  · intro i hi
    omega

/-- ONE fully verified induction step: extend an already realized
B-prefix of length n by the next requested sort-σ(n) vertex,
using the TRUE global old-source clique feasibility of B.

This is a GENUINE actual original-vertex extension, not an abstract
Fraisse one-point assertion. All previously selected source
indices are strictly before front and the next original is
chosen at or beyond front, so chronology and injection remain.

The complete old-source E columns, actual original coding-witness
membership, sorted labelling and both directions of all prescribed
B edges survive. -/
theorem trackFRankZeroRealizedPrefix_succ
    (d ell m n N : Nat) (hN : n + 1 ≤ N)
    (E B : Nat → Nat → Bool)
    (U : Fin d → Finset Nat)
    (σ : Nat → Fin d)
    (S : Fin d → Set (HensonOneType ell E))
    (u : Fin d → HensonOneType ell E)
    (hRootLevel : ∀ i, (u i).level = m)
    (hRootU : ∀ i, U i = (u i).neighbours)
    (hRootRank : ∀ i, HensonOneType.rank (u i) = 0)
    (hLarge : ∀ i, RankLargeness.Large HensonOneType.rank
      (S i) 0 (u i))
    (hActual : ∀ i (x : HensonOneType ell E),
      x ∈ S i → HensonOneType.IsCodingNode x)
    (hOld : ∀ i p, p ∈ U i → p < m)
    (hSymB : ∀ i j, B i j = B j i)
    (hGlobal : ∀ T : Finset Nat,
      T ⊆ Finset.range N → T.Nonempty →
      IsDirectedCliqueOn B T →
      T.card ≤ trackFCommonRawAge d ell m E U (T.image σ))
    (st : TrackFRankZeroRealizedPrefix d ell m n E B U σ S) :
    Nonempty (TrackFRankZeroRealizedPrefix
      d ell m (n + 1) E B U σ S) := by
  classical
  have hGlobalN : ∀ T : Finset Nat,
      T ⊆ Finset.range (n + 1) → T.Nonempty →
      IsDirectedCliqueOn B T →
      T.card ≤ trackFCommonRawAge d ell m E U (T.image σ) := by
    intro T hT hNon hC
    exact hGlobal T (hT.trans (Finset.range_mono hN)) hNon hC
  obtain ⟨x, hUX, hxS, hxFront, _hxRank, hxColumn, hxEdges⟩ :=
    HensonOneType.rank_zero_dense_actualCoding_realizes_global_next
      d ell m n E B U σ st.sortMap
      (S (σ n)) (u (σ n))
      (hRootLevel (σ n)) (hRootU (σ n))
      (hRootRank (σ n)) (hLarge (σ n))
      (hActual (σ n)) hOld
      st.f st.injective st.induced
      (fun i _ => hSymB n i)
      st.sorted st.oldColumns
      st.front st.frontLower st.bounds hGlobalN
  let f' : Nat → Nat :=
    fun i => if i = n then x.level else st.f i
  let sort' : Nat → Fin d :=
    fun c => if c = x.level then σ n else st.sortMap c
  have hfOld : ∀ i, i < n → f' i = st.f i := by
    intro i hi
    simp [f', Nat.ne_of_lt hi]
  have hfNew : f' n = x.level := by
    simp [f']
  have hOldNe : ∀ i, i < n → st.f i ≠ x.level := by
    intro i hi
    have hBound := (st.bounds i hi).2
    omega
  have hBounds : ∀ i, i < n + 1 →
      m ≤ f' i ∧ f' i < x.level + 1 := by
    intro i hi
    have hc : i < n ∨ i = n := by omega
    rcases hc with hiOld | hiNew
    · rw [hfOld i hiOld]
      have hb := st.bounds i hiOld
      exact ⟨hb.1, by omega⟩
    · subst i
      rw [hfNew]
      have hm : m ≤ x.level := st.frontLower.trans hxFront
      exact ⟨hm, Nat.lt_succ_self _⟩
  have hInj : Set.InjOn f'
      (↑(Finset.range (n + 1)) : Set Nat) := by
    intro i hi j hj hfi
    have hiBound : i < n + 1 := Finset.mem_range.mp hi
    have hjBound : j < n + 1 := Finset.mem_range.mp hj
    have hCasesI : i < n ∨ i = n := by omega
    have hCasesJ : j < n ∨ j = n := by omega
    rcases hCasesI with hiOld | hiNew
    · rcases hCasesJ with hjOld | hjNew
      · have hOldEq : st.f i = st.f j := by
          rw [hfOld i hiOld, hfOld j hjOld] at hfi
          exact hfi
        exact st.injective
          (Finset.mem_range.mpr hiOld)
          (Finset.mem_range.mpr hjOld) hOldEq
      · subst j
        rw [hfOld i hiOld, hfNew] at hfi
        exact False.elim ((hOldNe i hiOld) hfi)
    · subst i
      rcases hCasesJ with hjOld | hjNew
      · rw [hfNew, hfOld j hjOld] at hfi
        exact False.elim ((hOldNe j hjOld) hfi.symm)
      · subst j
        rfl
  have hOrder : ∀ i j, i < j → j < n + 1 → f' i < f' j := by
    intro i j hij hj
    have hiOld : i < n := by omega
    have hjCase : j < n ∨ j = n := by omega
    rcases hjCase with hjOld | hjNew
    · rw [hfOld i hiOld, hfOld j hjOld]
      exact st.ordered i j hij hjOld
    · subst j
      rw [hfOld i hiOld, hfNew]
      have hOld := (st.bounds i hiOld).2
      omega
  have hInduced : ∀ i, i < n + 1 → ∀ j, j < n + 1 →
      i ≠ j → E (f' i) (f' j) = B i j := by
    intro i hi j hj hij
    have hiCase : i < n ∨ i = n := by omega
    have hjCase : j < n ∨ j = n := by omega
    rcases hiCase with hiOld | hiNew
    · rcases hjCase with hjOld | hjNew
      · rw [hfOld i hiOld, hfOld j hjOld]
        exact st.induced i hiOld j hjOld hij
      · subst j
        rw [hfOld i hiOld, hfNew]
        exact (hxEdges i hiOld).1
    · subst i
      rcases hjCase with hjOld | hjNew
      · rw [hfNew, hfOld j hjOld]
        exact (hxEdges j hjOld).2
      · subst j
        exact False.elim (hij rfl)
  have hSort : ∀ i, i < n + 1 →
      sort' (f' i) = σ i := by
    intro i hi
    have hc : i < n ∨ i = n := by omega
    rcases hc with hiOld | hiNew
    · rw [hfOld i hiOld]
      simp [sort', hOldNe i hiOld, st.sorted i hiOld]
    · subst i
      simp [sort',hfNew]
  have hColumn : ∀ i, i < n + 1 → ∀ p, p < m →
      E p (f' i) = decide (p ∈ U (σ i)) := by
    intro i hi p hp
    have hc : i < n ∨ i = n := by omega
    rcases hc with hiOld | hiNew
    · rw [hfOld i hiOld]
      exact st.oldColumns i hiOld p hp
    · subst i
      rw [hfNew]
      exact hxColumn p hp
  have hCoding : ∀ i, i < n + 1 →
      ∃ t : HensonOneType ell E,
        t.level = f' i ∧ t ∈ S (σ i) := by
    intro i hi
    have hc : i < n ∨ i = n := by omega
    rcases hc with hiOld | hiNew
    · obtain ⟨t, htLevel, htS⟩ := st.coding i hiOld
      exact ⟨t, htLevel.trans (hfOld i hiOld).symm, htS⟩
    · subst i
      exact ⟨x, hfNew.symm, hxS⟩
  exact ⟨{
    f := f'
    sortMap := sort'
    front := x.level + 1
    frontLower := st.frontLower.trans
      (hxFront.trans (Nat.le_succ _))
    injective := hInj
    bounds := hBounds
    ordered := hOrder
    induced := hInduced
    sorted := hSort
    oldColumns := hColumn
    coding := hCoding
  }⟩

/-- Every finite initial segment of a globally feasible labelled
graph B can be realized with complete actual source original
coding and induced-graph invariants, for any finite length n≤N.

This induction is not vacuous: the empty state is explicit,
and every positive step invokes the PHYSICAL next-vertex
realization lemma derived from the global sorted clique bounds. -/
theorem trackFRankZeroRealizedPrefix_of_global
    (d ell m N : Nat) (E B : Nat → Nat → Bool)
    (U : Fin d → Finset Nat)
    (σ : Nat → Fin d)
    (S : Fin d → Set (HensonOneType ell E))
    (u : Fin d → HensonOneType ell E)
    (hRootLevel : ∀ i, (u i).level = m)
    (hRootU : ∀ i, U i = (u i).neighbours)
    (hRootRank : ∀ i, HensonOneType.rank (u i) = 0)
    (hLarge : ∀ i, RankLargeness.Large HensonOneType.rank
      (S i) 0 (u i))
    (hActual : ∀ i (x : HensonOneType ell E),
      x ∈ S i → HensonOneType.IsCodingNode x)
    (hOld : ∀ i p, p ∈ U i → p < m)
    (hSymB : ∀ i j, B i j = B j i)
    (hGlobal : ∀ T : Finset Nat,
      T ⊆ Finset.range N → T.Nonempty →
      IsDirectedCliqueOn B T →
      T.card ≤ trackFCommonRawAge d ell m E U (T.image σ)) :
    ∀ n : Nat, n ≤ N →
      Nonempty (TrackFRankZeroRealizedPrefix
        d ell m n E B U σ S) := by
  intro n
  induction n with
  | zero =>
      intro _
      exact trackFRankZeroRealizedPrefix_empty
        d ell m E B U σ S
  | succ n ih =>
      intro hn
      obtain ⟨st⟩ := ih (by omega)
      exact trackFRankZeroRealizedPrefix_succ
        d ell m n N hn E B U σ S u
        hRootLevel hRootU hRootRank hLarge hActual hOld
        hSymB hGlobal st

/-- MAIN BOTTOM-RANK FINITE RICHNESS THEOREM.

Any finite prescribed labelled graph B obeying the ACTUAL
old source RAW clique inequalities is realized as a genuine
induced finite subgraph of original source graph E by ACTUAL
coding originals chosen from their specified rank-zero
large coding-node fibres.

The embedding f is strictly increasing on its selected finite
domain, but the source-to-TARGET Henson embedding is not
assumed to preserve enumeration order anywhere.

All original old-column bits remain exactly those of their
designated sorts, and EVERY requested directed edge/nonedge
of B is realized. This theorem is the rank-zero/base layer
of the manuscript multi-sort finite graph richness induction,
not the higher-rank or full BRD lower characterization. -/
theorem trackFRankZero_realizes_all_feasible_sorted_graph
    (d ell m N : Nat) (E B : Nat → Nat → Bool)
    (U : Fin d → Finset Nat)
    (σ : Nat → Fin d)
    (S : Fin d → Set (HensonOneType ell E))
    (u : Fin d → HensonOneType ell E)
    (hRootLevel : ∀ i, (u i).level = m)
    (hRootU : ∀ i, U i = (u i).neighbours)
    (hRootRank : ∀ i, HensonOneType.rank (u i) = 0)
    (hLarge : ∀ i, RankLargeness.Large HensonOneType.rank
      (S i) 0 (u i))
    (hActual : ∀ i (x : HensonOneType ell E),
      x ∈ S i → HensonOneType.IsCodingNode x)
    (hOld : ∀ i p, p ∈ U i → p < m)
    (hSymB : ∀ i j, B i j = B j i)
    (hGlobal : ∀ T : Finset Nat,
      T ⊆ Finset.range N → T.Nonempty →
      IsDirectedCliqueOn B T →
      T.card ≤ trackFCommonRawAge d ell m E U (T.image σ)) :
    ∃ f : Nat → Nat,
      (∀ i j : Nat, i < j → j < N → f i < f j) ∧
      (∀ i : Nat, i < N → m ≤ f i) ∧
      (∀ i : Nat, i < N → ∃ t : HensonOneType ell E,
        t.level = f i ∧ t ∈ S (σ i)) ∧
      (∀ i : Nat, i < N → ∀ p : Nat, p < m →
        E p (f i) = decide (p ∈ U (σ i))) ∧
      (∀ i : Nat, i < N → ∀ j : Nat, j < N →
        i ≠ j → E (f i) (f j) = B i j) := by
  obtain ⟨st⟩ :=
    trackFRankZeroRealizedPrefix_of_global
      d ell m N E B U σ S u
      hRootLevel hRootU hRootRank hLarge hActual hOld
      hSymB hGlobal N (le_refl N)
  exact ⟨st.f, st.ordered,
    (fun i hi => (st.bounds i hi).1),
    st.coding, st.oldColumns, st.induced⟩

end Kk
