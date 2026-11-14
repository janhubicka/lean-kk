import Kk.FiniteUniformHensonRealization
import Kk.NumericHFullSelectedColumn
import Kk.NumericPrefixGapZero
import Mathlib.Tactic

/-!
# Track A: one uniform future, all old/gap numerical-H L columns

English proof and hostile audit committed FIRST:
  docs/finite_uniform_numeric_columns_english_audit.md

A single already checked pinned Henson original embedding has exact
old-to-every-future labelled columns c and exact zeros toward EVERY
intervening original omitted from the earlier image. The literal
finite numerical-H ordinary binary L constructor transfers those
bits to ALL old or gap real generations q<=k toward the future's
top-generation copies, in BOTH orientations. Odd dummy coordinates
have zero L bits in both directions.

The corollary uses the one finite universal future from the
explicitly constructed relative target, and chooses M containing
all old and selected future top copies. No unbounded diary or
auxiliary H+ E/B3/common source orbit follows.
-/

namespace Kk

open SuccessorTree.V10

/-- Exact labelled old-to-top L atoms, at EVERY old generation,
from ONE pinned finite induced original embedding. No positivity
or chosen-target shortcut. Original names need not be consecutive. -/
theorem finiteNumericH_pinned_old_generation_column_both
    (E A : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k M b N d : Nat) (hbN : b ≤ N)
    (f : Nat → Nat) (W : Finset Nat)
    (tau : Nat → Fin d) (c : Nat → Fin d → Bool)
    (hFix : ∀ i, i < b → f i = i)
    (hGraph : ∀ i j, i < N → j < N → i ≠ j →
      E (f i) (f j) = A i j)
    (hFuture : ∀ w ∈ W, b ≤ w ∧ w < N)
    (hAfter : ∀ w ∈ W, b ≤ f w)
    (hAColumn : ∀ i, i < b → ∀ w ∈ W,
      A i w = c i (tau w)) :
    ∀ i, i < b → ∀ w ∈ W, ∀ q, q ≤ k →
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k i q) (hPosition k (f w) k)
          (0 : Fin 1) = c i (tau w) ∧
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k (f w) k) (hPosition k i q)
          (0 : Fin 1) = c i (tau w) := by
  intro i hi w hw q hq
  have hOldBefore : i < f w := by
    have hWAfter := hAfter w hw
    omega
  have hDistinct : i ≠ w := by
    have hW := (hFuture w hw).1
    omega
  have hEColumn : E i (f w) = c i (tau w) := by
    have hInduced := hGraph i w (by omega)
      (hFuture w hw).2 hDistinct
    rw [hFix i hi] at hInduced
    exact hInduced.trans (hAColumn i hi w hw)
  have hNumeric :
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k i q) (hPosition k (f w) k)
          (0 : Fin 1) = E i (f w) := by
    change hNumericBinary (normalizedGraphModel E).binary k
      (hPosition k i q) (hPosition k (f w) k)
        (0 : Fin 1) = E i (f w)
    exact numericH_older_generation_to_top_exact
      (normalizedGraphModel E).binary k i (f w) q
      (0 : Fin 1) hOldBefore hq
  have hSwap := henson_finiteNumericH_binary_symmetric
    E hSym k M (hPosition k (f w) k) (hPosition k i q)
  exact ⟨hNumeric.trans hEColumn,
    hSwap.trans (hNumeric.trans hEColumn)⟩

/-- The pinned Henson original's exact ZERO bits toward ALL omitted
predecessors lift to ALL real numerical-H generations, in both L
tuple orientations, toward every selected TOP future copy.

This does NOT claim that already selected old/image originals
have zero columns: only genuinely omitted predecessors are tested. -/
theorem finiteNumericH_pinned_gap_generation_zero_both
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k M b N : Nat)
    (f : Nat → Nat) (W : Finset Nat)
    (hFuture : ∀ w ∈ W, b ≤ w ∧ w < N)
    (hGap : ∀ m, b ≤ m → m < N → ∀ z, z < f m →
      z ∉ (Finset.range m).image f →
      E z (f m) = false ∧ E (f m) z = false) :
    ∀ w ∈ W, ∀ z, z < f w →
      z ∉ (Finset.range w).image f →
      ∀ q, q ≤ k →
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k z q) (hPosition k (f w) k)
            (0 : Fin 1) = false ∧
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k (f w) k) (hPosition k z q)
            (0 : Fin 1) = false := by
  intro w hw z hz hOutside q hq
  have hEZero := (hGap w (hFuture w hw).1
    (hFuture w hw).2 z hz hOutside).1
  have hNumeric :
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k z q) (hPosition k (f w) k)
          (0 : Fin 1) = E z (f w) := by
    change hNumericBinary (normalizedGraphModel E).binary k
      (hPosition k z q) (hPosition k (f w) k)
        (0 : Fin 1) = E z (f w)
    exact numericH_older_generation_to_top_exact
      (normalizedGraphModel E).binary k z (f w) q
      (0 : Fin 1) hz hq
  have hSwap := henson_finiteNumericH_binary_symmetric
    E hSym k M (hPosition k (f w) k) (hPosition k z q)
  exact ⟨hNumeric.trans hEZero,
    hSwap.trans (hNumeric.trans hEZero)⟩

/-- The SINGLE explicitly built finite universal Henson original
future has the exact old-to-every-future L column at ALL old real
generations, and ALL omitted intermediate original/generation L
columns are zero. Odd dummy L columns toward selected top copies
also vanish.

One finite numerical cutoff M simultaneously includes the entire
old top-generation prefix and all selected new top positions.
The original embedding f is unchanged by this L transfer.
The full finite top-clique age-profile transport is independently
proved in Kk.FiniteUniformNumericTopAge, while this theorem
certifies the *old/gap cross columns* of that same construction. -/
theorem henson_leftDense_uniform_finite_numericH_complete_columns
    (d ell b k : Nat) (hell : 2 ≤ ell) (hd : 0 < d)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool) :
    let B := finiteOldColumnRawBound E ell d (Finset.range b) c
    let V := RelativeUniversalTaggedVertex d ell B
    let N := b + Fintype.card V
    let W : Finset Nat := finiteTaggedFuturePool (V := V) b
    let A : Nat → Nat → Bool := finiteTaggedOldFutureEdge b E
      (relativeUniversalTaggedEdge d ell B)
      (relativeUniversalTaggedSort d ell B) c
    let tau : Nat → Fin d := finiteTaggedFutureSort hd
      (relativeUniversalTaggedSort d ell B) b
    ∃ (f : Nat → Nat) (M : Nat),
      (∀ i, i < b → f i = i) ∧
      (∀ i j, i < N → j < N → i < j → f i < f j) ∧
      (∀ i j, i < N → j < N → i ≠ j →
        E (f i) (f j) = A i j) ∧
      (∀ m, b ≤ m → m < N → ∀ z, z < f m →
        z ∉ (Finset.range m).image f →
          E z (f m) = false ∧ E (f m) z = false) ∧
      (∀ x ∈ W, b ≤ f x) ∧
      (∀ i ∈ Finset.range b ∪ W.image f, hPosition k i k < M) ∧
      (∀ i, i < b → ∀ w ∈ W, ∀ q, q ≤ k →
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k i q) (hPosition k (f w) k)
            (0 : Fin 1) = c i (tau w) ∧
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k (f w) k) (hPosition k i q)
            (0 : Fin 1) = c i (tau w)) ∧
      (∀ w ∈ W, ∀ z, z < f w →
        z ∉ (Finset.range w).image f →
        ∀ q, q ≤ k →
          (finiteNumericHL (normalizedGraphModel E) k M).binary
            (hPosition k z q) (hPosition k (f w) k)
              (0 : Fin 1) = false ∧
          (finiteNumericHL (normalizedGraphModel E) k M).binary
            (hPosition k (f w) k) (hPosition k z q)
              (0 : Fin 1) = false) ∧
      (∀ w ∈ W, ∀ a : Nat,
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (2*a+1) (hPosition k (f w) k)
            (0 : Fin 1) = false ∧
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k (f w) k) (2*a+1)
            (0 : Fin 1) = false) := by
  classical
  let B : IntegerGraphSupport d ell → Nat :=
    finiteOldColumnRawBound E ell d (Finset.range b) c
  let V := RelativeUniversalTaggedVertex d ell B
  let N : Nat := b + Fintype.card V
  let W : Finset Nat := finiteTaggedFuturePool (V := V) b
  let R : V → V → Bool := relativeUniversalTaggedEdge d ell B
  let sort : V → Fin d := relativeUniversalTaggedSort d ell B
  let A : Nat → Nat → Bool := finiteTaggedOldFutureEdge b E R sort c
  let tau : Nat → Fin d := finiteTaggedFutureSort hd sort b
  obtain ⟨f,hFix,hMono,hGraph,hGap,hAfter,_hProfile⟩ :=
    henson_leftDense_realizes_all_finite_relative_age_profiles
      d ell b hell hd E hAvoid hDense c
  have hSym : ∀ i j, E i j = E j i :=
    hensonForbiddenFamily_symmetric ell hell E hAvoid
  let S : Finset Nat := W.image f
  let M : Nat := (Finset.range b ∪ S).sup
      (fun j => hPosition k j k) + 1
  have hBound : ∀ i ∈ Finset.range b ∪ S,
      hPosition k i k < M := by
    intro i hi
    have hLe : hPosition k i k ≤
        (Finset.range b ∪ S).sup (fun j => hPosition k j k) :=
      Finset.le_sup (f := fun j => hPosition k j k) hi
    exact Nat.lt_succ_of_le hLe
  have hFuture : ∀ w ∈ W, b ≤ w ∧ w < N := by
    intro w hw
    exact (finiteTaggedFuturePool_mem_iff (V := V) b w).mp hw
  have hBN : b ≤ N := by
    dsimp [N]
    omega
  have hAColumn : ∀ i, i < b → ∀ w ∈ W,
      A i w = c i (tau w) := by
    intro i hi w hw
    obtain ⟨v,hv,hvw⟩ := Finset.mem_image.mp hw
    subst w
    change finiteTaggedOldFutureEdge b E R sort c i
        (finiteTaggedIndex b v) =
      c i (finiteTaggedFutureSort hd sort b
        (finiteTaggedIndex b v))
    rw [finiteTaggedFutureSort_index]
    exact finiteTaggedEdge_old_future b E R sort c i v hi
  have hColumns :=
    finiteNumericH_pinned_old_generation_column_both
      E A hSym k M b N d hBN f W tau c
      hFix hGraph hFuture hAfter hAColumn
  have hSkipped :=
    finiteNumericH_pinned_gap_generation_zero_both
      E hSym k M b N f W hFuture hGap
  have hDummy : ∀ w ∈ W, ∀ a : Nat,
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (2*a+1) (hPosition k (f w) k) (0 : Fin 1) = false ∧
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k (f w) k) (2*a+1) (0 : Fin 1) = false := by
    intro w hw a
    exact finiteNumericH_odd_dummy_to_top_zero E k M a (f w)
  exact ⟨f,M,hFix,hMono,hGraph,hGap,hAfter,hBound,
    hColumns,hSkipped,hDummy⟩

#print axioms Kk.finiteNumericH_pinned_old_generation_column_both
#print axioms Kk.finiteNumericH_pinned_gap_generation_zero_both
#print axioms Kk.henson_leftDense_uniform_finite_numericH_complete_columns

end Kk
