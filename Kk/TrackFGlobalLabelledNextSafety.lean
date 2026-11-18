import Kk.TrackFOnePointGluingSafety
import Kk.FiniteCliqueEmbeddingTransport
import Mathlib.Tactic

/-!
# Track F: global finite sorted graph clique feasibility implies one-point safety

English proof and twelve hostile checks committed BEFORE Lean:
docs/track_f_global_labelled_next_safety_english_audit.md

A finite requested graph B on abstract originals 0,...,n,
sort-labelled by σ, satisfies ALL genuine old-source RAW clique
constraints. Suppose its first n vertices have already been
realized by an injective induced map f into the ACTUAL old
source graph E. Then EVERY actual directed clique among the
positive past neighbours of requested vertex n inherits the
correct source raw inequality, by pulling it back along f.

Compose that exact preimage/image lemma with the now-verified
physical one-point safety theorem (#345). The next proposed
old-neighbourhood pool is genuinely K_(ell-1)-free, without
assuming local safety separately.

The third theorem uses rank-zero density of ACTUAL source
coding nodes to realize this new original with all two-directed
past adjacencies exactly as in B. It is the FINITE next-vertex
step, not yet the full finite-length graph realization induction.
-/

namespace Kk

/-- The actual positive past vertices of the next abstract
requested graph vertex n. The physical original at old index
f(i) is positive exactly when B(i,n)=true. -/
def trackFNextPositivePast
    (B : Nat → Nat → Bool) (f : Nat → Nat) (n : Nat) :
    Finset Nat :=
  ((Finset.range n).filter (fun i => B i n = true)).image f

/-- From GLOBAL raw clique feasibility of a finite labelled
graph B, derive the exact one-point raw inequality on EVERY
actual directed clique D among the requested positive past.

The first n abstract vertices are realized injectively and
induced in the ACTUAL graph E. B is symmetric on every pair
involving the new vertex n. The finite sort labelling of
already chosen original indices agrees with σ through f.

No assumption that positive itself is a clique, no invented
diary age, and no source-to-target enumeration monotonicity. -/
theorem trackFNextPositivePast_raw_feasible_of_global
    (d ell m n : Nat)
    (E B : Nat → Nat → Bool)
    (U : Fin d → Finset Nat)
    (f : Nat → Nat)
    (σ : Nat → Fin d) (sort : Nat → Fin d)
    (hInj : Set.InjOn f (↑(Finset.range n) : Set Nat))
    (hInduced : ∀ i : Nat, i < n →
      ∀ j : Nat, j < n → i ≠ j →
        E (f i) (f j) = B i j)
    (hNewSym : ∀ i : Nat, i < n → B n i = B i n)
    (hSort : ∀ i : Nat, i < n → sort (f i) = σ i)
    (hGlobal : ∀ T : Finset Nat,
      T ⊆ Finset.range (n + 1) → T.Nonempty →
      IsDirectedCliqueOn B T →
      T.card ≤ trackFCommonRawAge d ell m E U (T.image σ)) :
    ∀ D : Finset Nat,
      D ⊆ trackFNextPositivePast B f n →
      IsDirectedCliqueOn E D →
      D.card + 1 ≤ trackFCommonRawAge d ell m E U
        (insert (σ n) (D.image sort)) := by
  classical
  intro D hD hClique
  let posIndices : Finset Nat :=
    (Finset.range n).filter (fun i => B i n = true)
  let T : Finset Nat :=
    posIndices.filter (fun i => f i ∈ D)
  have hTPos : T ⊆ posIndices := Finset.filter_subset _ _
  have hPosN : ∀ i ∈ posIndices, i < n := by
    intro i hi
    exact Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  have hTBelow : ∀ i ∈ T, i < n := by
    intro i hi
    exact hPosN i (hTPos hi)
  have hTPass : ∀ i ∈ T, B i n = true := by
    intro i hi
    exact (Finset.mem_filter.mp (hTPos hi)).2
  have hTImage : T.image f = D := by
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
      exact hix ▸ (Finset.mem_filter.mp hi).2
    · intro x hx
      have hxPos : x ∈ posIndices.image f := by
        exact hD hx
      obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hxPos
      exact Finset.mem_image.mpr
        ⟨i, Finset.mem_filter.mpr ⟨hi, hix ▸ hx⟩, hix⟩
  have hInjT : Set.InjOn f (↑T : Set Nat) := by
    intro i hi j hj hij
    have hiN : i ∈ Finset.range n :=
      Finset.mem_range.mpr (hTBelow i hi)
    have hjN : j ∈ Finset.range n :=
      Finset.mem_range.mpr (hTBelow j hj)
    exact hInj hiN hjN hij
  have hTcard : T.card = D.card := by
    have hCardImage := Finset.card_image_iff.mpr hInjT
    rw [hTImage] at hCardImage
    exact hCardImage.symm
  have hTclique : IsDirectedCliqueOn B T := by
    intro i hi j hj hij
    have hiD : f i ∈ D := by
      apply (Finset.mem_filter.mp hi).2
    have hjD : f j ∈ D := by
      apply (Finset.mem_filter.mp hj).2
    have hfiNe : f i ≠ f j := by
      intro hfij
      exact hij (hInjT hi hj hfij)
    have hEdge : E (f i) (f j) = true :=
      hClique (f i) hiD (f j) hjD hfiNe
    exact (hInduced i (hTBelow i hi) j
      (hTBelow j hj) hij).symm.trans hEdge
  have hnNotT : n ∉ T := by
    intro hnT
    have hnlt := hTBelow n hnT
    omega
  have hBclique : IsDirectedCliqueOn B (insert n T) := by
    intro i hi j hj hij
    rcases Finset.mem_insert.mp hi with hin | hiT
    · subst i
      rcases Finset.mem_insert.mp hj with hjn | hjT
      · exact False.elim (hij hjn.symm)
      · rw [hNewSym j (hTBelow j hjT)]
        exact hTPass j hjT
    · rcases Finset.mem_insert.mp hj with hjn | hjT
      · subst j
        exact hTPass i hiT
      · exact hTclique i hiT j hjT hij
  have hSubset : insert n T ⊆ Finset.range (n+1) := by
    intro i hi
    rcases Finset.mem_insert.mp hi with hin | hiT
    · subst i
      simp
    · exact Finset.mem_range.mpr (by
        have hiN := hTBelow i hiT
        omega)
  have hImageSort : D.image sort = T.image σ := by
    rw [← hTImage]
    apply Finset.Subset.antisymm
    · intro j hj
      obtain ⟨x, hxImg, hxj⟩ := Finset.mem_image.mp hj
      obtain ⟨i, hiT, hix⟩ := Finset.mem_image.mp hxImg
      exact Finset.mem_image.mpr
        ⟨i, hiT, by
          calc
            σ i = sort (f i) := (hSort i (hTBelow i hiT)).symm
            _ = sort x := congrArg sort hix
            _ = j := hxj⟩
    · intro j hj
      obtain ⟨i, hiT, hij⟩ := Finset.mem_image.mp hj
      refine Finset.mem_image.mpr ⟨f i, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨i, hiT, rfl⟩
      · exact (hSort i (hTBelow i hiT)).trans hij
  have hSupport :
      (insert n T).image σ = insert (σ n) (D.image sort) := by
    rw [Finset.image_insert, ← hImageSort]
  have hCardNew : (insert n T).card = D.card + 1 := by
    simp [hnNotT, hTcard]
  have hReq : (insert n T).Nonempty := by
    exact ⟨n, Finset.mem_insert_self _ _⟩
  have hGlobalT := hGlobal (insert n T) hSubset hReq hBclique
  rw [hCardNew, hSupport] at hGlobalT
  exact hGlobalT

/-- GLOBAL feasibility of every source labelled B-clique
discharges the full ACTUAL physical K_(ell-1)-free safety
test for the next requested original. This composes exact
finite-image/preimage source cliques with the verified real
old/new clique decomposition theorem of PR #345.

The old columns and source/past chronological separation are
explicit invariant hypotheses of the intended finite induction. -/
theorem trackFNextPositivePast_safe_of_global
    (d ell m n : Nat) (E B : Nat → Nat → Bool)
    (U : Fin d → Finset Nat)
    (hOld : ∀ i x, x ∈ U i → x < m)
    (f : Nat → Nat)
    (σ : Nat → Fin d) (sort : Nat → Fin d)
    (hInj : Set.InjOn f (↑(Finset.range n) : Set Nat))
    (hInduced : ∀ i : Nat, i < n →
      ∀ j : Nat, j < n → i ≠ j →
        E (f i) (f j) = B i j)
    (hNewSym : ∀ i : Nat, i < n → B n i = B i n)
    (hSort : ∀ i : Nat, i < n → sort (f i) = σ i)
    (hPast : ∀ i : Nat, i < n → m ≤ f i)
    (hColumn : ∀ i : Nat, i < n →
      ∀ p : Nat, p < m →
        E p (f i) = decide (p ∈ U (σ i)))
    (hGlobal : ∀ T : Finset Nat,
      T ⊆ Finset.range (n + 1) → T.Nonempty →
      IsDirectedCliqueOn B T →
      T.card ≤ trackFCommonRawAge d ell m E U (T.image σ)) :
    finitePoolCliqueCheck E (ell - 1)
      (U (σ n) ∪ trackFNextPositivePast B f n) = false := by
  classical
  let past : Finset Nat := (Finset.range n).image f
  let positive : Finset Nat := trackFNextPositivePast B f n
  have hPosSubset : positive ⊆ past := by
    exact Finset.image_subset_image (Finset.filter_subset _ _)
  have hPastActual : ∀ c ∈ past, m ≤ c := by
    intro c hc
    obtain ⟨i, hi, hic⟩ := Finset.mem_image.mp hc
    exact hic ▸ hPast i (Finset.mem_range.mp hi)
  have hColumnActual : ∀ c ∈ past, ∀ p, p < m →
      E p c = decide (p ∈ U (sort c)) := by
    intro c hc p hp
    obtain ⟨i, hi, hic⟩ := Finset.mem_image.mp hc
    have hCol := hColumn i (Finset.mem_range.mp hi) p hp
    have hs := hSort i (Finset.mem_range.mp hi)
    simpa only [← hic, hs] using hCol
  exact trackFOnePointPool_safe_of_sorted_clique_inequalities
    d ell m E U hOld past positive hPastActual hPosSubset
    sort hColumnActual (σ n)
    (trackFNextPositivePast_raw_feasible_of_global
      d ell m n E B U f σ sort
      hInj hInduced hNewSym hSort hGlobal)

namespace HensonOneType

/-- NEXT ACTUAL source coding vertex of a globally feasible finite
labelled graph B, selected from a rank-zero dense source fibre S.

The prior n source ORIGINAL vertices have been realized by f with
the correct induced B-edge table and actual old-prefix source-sort
columns. The global B RAW clique feasibility predicates imply
the exact one-point safety certificate (proved above); the
verified density theorem then gives a GENUINE new coding original.

The conclusion preserves ALL three induction invariants at once:
- the source fibre and chronological bound;
- the exact actual E column on the original common prefix m;
- BOTH directed actual B edges to all n previously chosen originals.

The finite iteration over n remains a separate theorem. -/
theorem rank_zero_dense_actualCoding_realizes_global_next
    (d ell m n : Nat) (E B : Nat → Nat → Bool)
    (U : Fin d → Finset Nat)
    (σ : Nat → Fin d) (sort : Nat → Fin d)
    (S : Set (HensonOneType ell E))
    (u : HensonOneType ell E)
    (huLevel : u.level = m)
    (huRoot : U (σ n) = u.neighbours)
    (huRank : rank u = 0)
    (hLarge : RankLargeness.Large rank S 0 u)
    (hActual : ∀ x : HensonOneType ell E,
      x ∈ S → IsCodingNode x)
    (hOld : ∀ i x, x ∈ U i → x < m)
    (f : Nat → Nat)
    (hInj : Set.InjOn f (↑(Finset.range n) : Set Nat))
    (hInduced : ∀ i : Nat, i < n →
      ∀ j : Nat, j < n → i ≠ j →
        E (f i) (f j) = B i j)
    (hNewSym : ∀ i : Nat, i < n → B n i = B i n)
    (hSort : ∀ i : Nat, i < n → sort (f i) = σ i)
    (hColumn : ∀ i : Nat, i < n →
      ∀ p : Nat, p < m →
        E p (f i) = decide (p ∈ U (σ i)))
    (front : Nat) (hFront : m ≤ front)
    (hPastBounds : ∀ i : Nat, i < n →
      m ≤ f i ∧ f i < front)
    (hGlobal : ∀ T : Finset Nat,
      T ⊆ Finset.range (n + 1) → T.Nonempty →
      IsDirectedCliqueOn B T →
      T.card ≤ trackFCommonRawAge d ell m E U (T.image σ)) :
    ∃ x : HensonOneType ell E,
      u ≤ x ∧ x ∈ S ∧ front ≤ x.level ∧ rank x = 0 ∧
      (∀ p : Nat, p < m →
        E p x.level = decide (p ∈ U (σ n))) ∧
      (∀ i : Nat, i < n →
        E (f i) x.level = B i n ∧
        E x.level (f i) = B n i) := by
  classical
  let past : Finset Nat := (Finset.range n).image f
  let positive : Finset Nat := trackFNextPositivePast B f n
  have hPosSubset : positive ⊆ past := by
    exact Finset.image_subset_image (Finset.filter_subset _ _)
  have hPastActual : ∀ c ∈ past,
      u.level ≤ c ∧ c < front := by
    intro c hc
    obtain ⟨i, hi, hic⟩ := Finset.mem_image.mp hc
    have hiN := Finset.mem_range.mp hi
    have hb := hPastBounds i hiN
    constructor
    · rw [huLevel]
      exact hic ▸ hb.1
    · exact hic ▸ hb.2
  have hSafeU :
      finitePoolCliqueCheck E (ell - 1)
        (U (σ n) ∪ positive) = false :=
    trackFNextPositivePast_safe_of_global
      d ell m n E B U hOld f σ sort
      hInj hInduced hNewSym hSort
      (fun i hi => (hPastBounds i hi).1)
      hColumn hGlobal
  have hSafe :
      finitePoolCliqueCheck E (ell - 1)
        (u.neighbours ∪ positive) = false := by
    simpa only [huRoot] using hSafeU
  obtain ⟨x, hUX, hxS, hxFront, hxRank, hxPast⟩ :=
    rank_zero_dense_actualCoding_realizes_safe_past
      S u huRank hLarge hActual front
      (by simpa only [huLevel] using hFront)
      past positive hPastActual hPosSubset hSafe
  have hOldColumn : ∀ p : Nat, p < m →
      E p x.level = decide (p ∈ U (σ n)) := by
    intro p hp
    have hpU : p < u.level := by simpa only [huLevel] using hp
    have hpX : p < x.level := lt_of_lt_of_le hpU hUX.1
    have hMem : (p ∈ x.neighbours) ↔ (p ∈ u.neighbours) :=
      (hUX.2 p hpU).symm
    have hCode := (hActual x hxS p hpX).1
    have hDecide :
        decide (p ∈ x.neighbours) =
          decide (p ∈ u.neighbours) := by
      by_cases h : p ∈ u.neighbours
      · have hX : p ∈ x.neighbours := hMem.mpr h
        simp [h,hX]
      · have hX : p ∉ x.neighbours := by
          intro hX
          exact h (hMem.mp hX)
        simp [h,hX]
    calc
      E p x.level = decide (p ∈ x.neighbours) := hCode
      _ = decide (p ∈ u.neighbours) := hDecide
      _ = decide (p ∈ U (σ n)) := by
        rw [huRoot]
  have hFutureBits : ∀ i : Nat, i < n →
      E (f i) x.level = B i n ∧
      E x.level (f i) = B n i := by
    intro i hi
    have hiPast : f i ∈ past :=
      Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩
    have hxBits := hxPast (f i) hiPast
    have hPositiveAt : (f i ∈ positive) ↔ B i n = true := by
      constructor
      · intro hPos
        obtain ⟨j, hj, hjImage⟩ := Finset.mem_image.mp hPos
        have hjN : j < n :=
          Finset.mem_range.mp (Finset.mem_filter.mp hj).1
        have hji : j = i :=
          hInj (Finset.mem_range.mpr hjN)
            (Finset.mem_range.mpr hi) hjImage
        subst j
        exact (Finset.mem_filter.mp hj).2
      · intro hBit
        exact Finset.mem_image.mpr
          ⟨i, Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr hi, hBit⟩, rfl⟩
    have hDecide :
        decide (f i ∈ positive) = B i n := by
      cases hBit : B i n with
      | false =>
          have hNot : f i ∉ positive := by
            intro hp
            have he := hPositiveAt.mp hp
            rw [hBit] at he
            cases he
          simp [hNot, hBit]
      | true =>
          have hYes : f i ∈ positive := hPositiveAt.mpr hBit
          simp [hYes, hBit]
    constructor
    · exact hxBits.1.trans hDecide
    · calc
        E x.level (f i) = decide (f i ∈ positive) := hxBits.2
        _ = B i n := hDecide
        _ = B n i := (hNewSym i hi).symm
  exact ⟨x, hUX, hxS, hxFront, hxRank,
    hOldColumn, hFutureBits⟩

end HensonOneType

end Kk
