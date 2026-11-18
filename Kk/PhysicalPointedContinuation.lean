import Kk.PointedContinuationColumn
import Kk.FiniteUniformNumericComplete
import Kk.UniformStageNonvacuousSortWitness
import Mathlib.Tactic

/-!
# Track B: one complete finite continuation around a fixed selected original

English proof and independent audit preceded this module:
  docs/track_b_pointed_continuation_english_audit.md

The next column is explicitly constructed. Its exact raw bounds include every
original below a freely chosen protected cutoff H. One common embedding and
numerical cutoff realize all compatible future clique profiles while fixing
EVERY original below H, including the already selected pivot and any earlier
finite graph witnesses. The full thirteen-clause realization certificate is
retained, rather than projected to unrelated existential edge/profile claims.

Previous graph vertices are fixed, but their former future-sort roles are not
preserved: every intermediate original other than the pivot is explicitly
given a zero column to the new future. No infinite resolved schedule, auxiliary
Kpt source, corrected B3, or common labelled inverse-source orbit is asserted.
-/

namespace Kk

open SuccessorTree.V10

/-- All thirteen clauses of the existing uniform finite numerical-H realization,
with its physical embedding and cutoff exposed as shared parameters. This keeps
chronology, induced graph, every carrier bound, exact all-support profiles,
complete old/gap columns, and odd-dummy zeros in ONE certificate. -/
def FiniteNumericStageWitness
    (E : Nat → Nat → Bool) (d ell b k : Nat) (hd : 0 < d)
    (c : Nat → Fin d → Bool) (f : Nat → Nat) (M : Nat) : Prop :=
    let B := finiteOldColumnRawBound E ell d (Finset.range b) c
    let V := RelativeUniversalTaggedVertex d ell B
    let N := b + Fintype.card V
    let W : Finset Nat := finiteTaggedFuturePool (V := V) b
    let A : Nat → Nat → Bool := finiteTaggedOldFutureEdge b E
      (relativeUniversalTaggedEdge d ell B)
      (relativeUniversalTaggedSort d ell B) c
    let tau : Nat → Fin d := finiteTaggedFutureSort hd
      (relativeUniversalTaggedSort d ell B) b
    (∀ i, i < b → f i = i) ∧
    (∀ i j, i < N → j < N → i < j → f i < f j) ∧
    (∀ i j, i < N → j < N → i ≠ j →
      E (f i) (f j) = A i j) ∧
    (∀ m, b ≤ m → m < N → ∀ z, z < f m →
      z ∉ (Finset.range m).image f →
        E z (f m) = false ∧ E (f m) z = false) ∧
    (∀ w ∈ W, b ≤ f w) ∧
    (∀ i ∈ Finset.range b ∪ W.image f,
      hPosition k i k < M) ∧
    (∀ i, i < b → ∀ q, q ≤ k →
      hPosition k i q < M) ∧
    (∀ w ∈ W, ∀ z, z < f w → ∀ q, q ≤ k →
      hPosition k z q < M) ∧
    (∀ u ∈ numericHTopPool k (W.image f),
      u ∈ (finiteNumericHL (normalizedGraphModel E) k M).carrier) ∧
    (∀ v : IntegerCliqueWeights d ell,
      v ∈ feasibleIntegerCliqueVectors d ell B ↔
        ∃ t : Finset Nat,
          t ⊆ numericHTopPool k (W.image f) ∧
          IsDirectedCliqueOn
            (fun x y =>
              (finiteNumericHL (normalizedGraphModel E) k M).binary
                x y (0 : Fin 1)) t ∧
          (∀ T : IntegerGraphSupport d ell,
            (t.filter (fun z =>
              z ∈ numericHTopPool k
                ((W.filter (fun x => tau x ∈ T.1)).image f))).card =
                integerCliqueOnSupport v T)) ∧
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
          (0 : Fin 1) = false)

/-- The established constructive realization theorem supplies the full named
certificate without dropping any of its thirteen same-witness clauses. -/
theorem henson_leftDense_finite_numeric_stage_witness
    (E : Nat → Nat → Bool) (d ell b k : Nat)
    (hell : 2 ≤ ell) (hd : 0 < d)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool) :
    ∃ (f : Nat → Nat) (M : Nat),
      FiniteNumericStageWitness E d ell b k hd c f M := by
  exact henson_leftDense_realizes_all_finite_numericH_L_columns_and_profiles
    d ell b k hell hd E hAvoid hDense c

/-- The complete ORIGINAL E column is recovered for the SAME embedding and
cutoff carried by the numerical certificate. This is useful for a subsequent
physical construction, and retains both positive and negative atoms. -/
theorem finiteNumericStageWitness_original_columns
    (E : Nat → Nat → Bool) (d ell b k : Nat) (hd : 0 < d)
    (c : Nat → Fin d → Bool) (f : Nat → Nat) (M : Nat)
    (hSym : ∀ i j, E i j = E j i)
    (hStage : FiniteNumericStageWitness E d ell b k hd c f M) :
    let B := finiteOldColumnRawBound E ell d (Finset.range b) c
    let V := RelativeUniversalTaggedVertex d ell B
    let W : Finset Nat := finiteTaggedFuturePool (V := V) b
    let tau : Nat → Fin d := finiteTaggedFutureSort hd
      (relativeUniversalTaggedSort d ell B) b
    ∀ p, p < b → ∀ w ∈ W,
      E p (f w) = c p (tau w) ∧ E (f w) p = c p (tau w) := by
  classical
  unfold FiniteNumericStageWitness at hStage
  rcases hStage with ⟨_hFix, _hMono, _hGraph, _hGap, hAfter,
    _hCut, _hOldCarrier, _hGapCarrier, _hTopCarrier, _hProfile,
    hColumns, _hGapNumeric, _hDummy⟩
  dsimp only
  intro p hp w hw
  have hBefore : p < f w := lt_of_lt_of_le hp (hAfter w hw)
  have hNumeric := finiteNumericH_top_exact_original_edge
    E hSym k M p (f w) (ne_of_lt hBefore)
  have hForward : E p (f w) = c p
      (finiteTaggedFutureSort hd
        (relativeUniversalTaggedSort d ell
          (finiteOldColumnRawBound E ell d (Finset.range b) c)) b w) :=
    hNumeric.symm.trans (hColumns p hp w hw k le_rfl).1
  exact ⟨hForward, (hSym (f w) p).trans hForward⟩

/-- Construct the compatible finite future for the explicit pointed column.
The actual full-prefix raw bound is first identified with the exact successor
formula. One shared f,M then realizes every feasible new clique vector and all
complete numerical columns, and fixes the chosen original v literally.

H may be chosen beyond EVERY vertex of a previous finite stage. Such vertices
remain fixed graph vertices; their old future-sort designation is not claimed
to persist. Zero-bound branches produce no fabricated future originals. -/
theorem henson_leftDense_constructs_pointed_continuation
    (E : Nat → Nat → Bool) (d e ell b v H k : Nat)
    (hell : 2 ≤ ell) (he : 0 < e)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool) (s : Fin d)
    (pi : Fin e → Fin d) (beta : Fin e → Bool)
    (hbv : b ≤ v) (hvH : v < H)
    (hPivot : ∀ p, p < b →
      E p v = c p s ∧ E v p = c p s) :
    let C := pointedContinuationColumn b v c pi beta
    let B := finiteOldColumnRawBound E ell e (Finset.range H) C
    let V := RelativeUniversalTaggedVertex e ell B
    let W : Finset Nat := finiteTaggedFuturePool (V := V) H
    let tau : Nat → Fin e := finiteTaggedFutureSort he
      (relativeUniversalTaggedSort e ell B) H
    B = pointedContinuationRawBound E ell b c s pi beta ∧
    ∃ (f : Nat → Nat) (M : Nat),
      FiniteNumericStageWitness E e ell H k he C f M ∧
      f v = v ∧
      (∀ p, p < H → ∀ w ∈ W,
        E p (f w) = C p (tau w) ∧ E (f w) p = C p (tau w)) ∧
      (∀ p, p < b → ∀ w ∈ W, ∀ q, q ≤ k →
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k p q) (hPosition k (f w) k) (0 : Fin 1) =
            c p (pi (tau w)) ∧
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k (f w) k) (hPosition k p q) (0 : Fin 1) =
            c p (pi (tau w))) ∧
      (∀ w ∈ W, ∀ q, q ≤ k →
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k v q) (hPosition k (f w) k) (0 : Fin 1) =
            beta (tau w) ∧
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k (f w) k) (hPosition k v q) (0 : Fin 1) =
            beta (tau w)) ∧
      (∀ p, b ≤ p → p < H → p ≠ v → ∀ w ∈ W, ∀ q, q ≤ k →
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k p q) (hPosition k (f w) k) (0 : Fin 1) = false ∧
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k (f w) k) (hPosition k p q) (0 : Fin 1) = false) := by
  classical
  let C := pointedContinuationColumn b v c pi beta
  let B := finiteOldColumnRawBound E ell e (Finset.range H) C
  let V := RelativeUniversalTaggedVertex e ell B
  let W : Finset Nat := finiteTaggedFuturePool (V := V) H
  let tau : Nat → Fin e := finiteTaggedFutureSort he
    (relativeUniversalTaggedSort e ell B) H
  have hRaw : B = pointedContinuationRawBound E ell b c s pi beta :=
    pointedContinuation_raw_bound E ell b v H c s pi beta hbv hvH hPivot
  refine ⟨hRaw, ?_⟩
  obtain ⟨f, M, hStage⟩ := henson_leftDense_finite_numeric_stage_witness
    E e ell H k hell he hAvoid hDense C
  have hSym : ∀ i j, E i j = E j i :=
    hensonForbiddenFamily_symmetric ell hell E hAvoid
  have hOriginal := finiteNumericStageWitness_original_columns
    E e ell H k he C f M hSym hStage
  have hFull := hStage
  unfold FiniteNumericStageWitness at hStage
  rcases hStage with ⟨hFix, _hMono, _hGraph, _hGap, _hAfter,
    _hCut, _hOldCarrier, _hGapCarrier, _hTopCarrier, _hProfile,
    hColumns, _hGapNumeric, _hDummy⟩
  refine ⟨f, M, hFull, hFix v hvH, hOriginal, ?_, ?_, ?_⟩
  · intro p hp w hw q hq
    have hpH : p < H := lt_of_lt_of_le hp (le_trans hbv (Nat.le_of_lt hvH))
    simpa only [C, pointedContinuationColumn, if_pos hp] using
      hColumns p hpH w hw q hq
  · intro w hw q hq
    have hPivotColumn : C v (tau w) = beta (tau w) :=
      pointedContinuationColumn_pivot b v c pi beta hbv (tau w)
    exact ⟨(hColumns v hvH w hw q hq).1.trans hPivotColumn,
      (hColumns v hvH w hw q hq).2.trans hPivotColumn⟩
  · intro p hbp hpH hpv w hw q hq
    have hNotOld : ¬ p < b := Nat.not_lt.mpr hbp
    simpa only [C, pointedContinuationColumn, if_neg hNotOld, if_neg hpv] using
      hColumns p hpH w hw q hq


/-- ANY supplied complete first stage can be extended around a genuinely
selected T-sort vertex. The new embedding fixes all first-stage graph witnesses,
and its numerical cutoff strictly exceeds the supplied first cutoff. No
preservation of former future-sort roles or full Kpt sources is asserted.

The argument and independent audit precede the code in section 6 of
`docs/track_b_pointed_continuation_english_audit.md`. -/
theorem finiteNumericStageWitness_extends_pointed
    (E : Nat → Nat → Bool) (d e ell b k : Nat)
    (hell : 2 ≤ ell) (hd : 0 < d) (he : 0 < e)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool)
    (T : IntegerGraphSupport d ell)
    (hPositive : 0 < integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) T)
    (pi : Fin e → Fin d) (beta : Fin e → Bool)
    (f : Nat → Nat) (M : Nat)
    (hFirst : FiniteNumericStageWitness E d ell b k hd c f M) :
    let B := finiteOldColumnRawBound E ell d (Finset.range b) c
    let V := RelativeUniversalTaggedVertex d ell B
    let W : Finset Nat := finiteTaggedFuturePool (V := V) b
    let tau : Nat → Fin d := finiteTaggedFutureSort hd
      (relativeUniversalTaggedSort d ell B) b
    ∃ (w H : Nat) (g : Nat → Nat) (M' : Nat),
      w ∈ W ∧ tau w ∈ T.1 ∧ b ≤ f w ∧
      (∀ x ∈ W, f x < H) ∧
      (∀ p, p < b → E p (f w) = c p (tau w) ∧
        E (f w) p = c p (tau w)) ∧
      (finiteOldColumnRawBound E ell e (Finset.range H)
        (pointedContinuationColumn b (f w) c pi beta) =
          pointedContinuationRawBound E ell b c (tau w) pi beta) ∧
      FiniteNumericStageWitness E e ell H k he
        (pointedContinuationColumn b (f w) c pi beta) g M' ∧
      (∀ p, p < H → g p = p) ∧
      (∀ x ∈ W, g (f x) = f x) ∧ g (f w) = f w ∧ M < M' := by
  classical
  let B := finiteOldColumnRawBound E ell d (Finset.range b) c
  let V := RelativeUniversalTaggedVertex d ell B
  let W : Finset Nat := finiteTaggedFuturePool (V := V) b
  let tau : Nat → Fin d := finiteTaggedFutureSort hd
    (relativeUniversalTaggedSort d ell B) b
  have hSym : ∀ i j, E i j = E j i :=
    hensonForbiddenFamily_symmetric ell hell E hAvoid
  have hOriginal := finiteNumericStageWitness_original_columns
    E d ell b k hd c f M hSym hFirst
  obtain ⟨w, hw, hSort⟩ :=
    finiteTaggedFuture_exists_T_sort_of_positive_canonical
      d ell b hd (by omega) B T hPositive
  have hFirstData := hFirst
  unfold FiniteNumericStageWitness at hFirstData
  rcases hFirstData with ⟨_hFix, _hMono, _hGraph, _hGap, hAfter,
    _hCut, _hOldCarrier, _hGapCarrier, _hTopCarrier, _hProfile,
    _hColumns, _hGapNumeric, _hDummy⟩
  let H : Nat := max (M + 1) (max b ((W.image f).sup (fun i : Nat => i) + 1))
  have hBound : ∀ x ∈ W, f x < H := by
    intro x hx
    have hSup : f x ≤ (W.image f).sup (fun i : Nat => i) :=
      Finset.le_sup (f := fun i : Nat => i)
        (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    dsimp [H]
    omega
  have hMH : M < H := by
    dsimp [H]
    omega
  have hPivot : ∀ p, p < b → E p (f w) = c p (tau w) ∧
      E (f w) p = c p (tau w) := by
    intro p hp
    exact hOriginal p hp w hw
  obtain ⟨hRaw, g, M', hSecond, hFixedPivot, _hNextOriginal,
      _hNextOld, _hNextPivot, _hNextGap⟩ :=
    henson_leftDense_constructs_pointed_continuation
      E d e ell b (f w) H k hell he hAvoid hDense c (tau w)
      pi beta (hAfter w hw) (hBound w hw) hPivot
  have hSecondData := hSecond
  unfold FiniteNumericStageWitness at hSecondData
  rcases hSecondData with ⟨hFixed, _hMono2, _hGraph2, _hGap2, _hAfter2,
    _hCut2, hOldCarrier2, _hGapCarrier2, _hTopCarrier2, _hProfile2,
    _hColumns2, _hGapNumeric2, _hDummy2⟩
  have hCutIncreasing : M < M' := by
    have hCarrier := hOldCarrier2 M hMH k le_rfl
    have hScale : M ≤ 2 * (k + 1) * M := by
      nlinarith [Nat.zero_le (k * M)]
    dsimp [hPosition] at hCarrier
    omega
  refine ⟨w, H, g, M', hw, hSort, hAfter w hw,
    hBound, hPivot, hRaw, hSecond, hFixed, ?_, hFixedPivot, hCutIncreasing⟩
  intro x hx
  exact hFixed (f x) (hBound x hx)

/-- Two genuine finite stages coexist in the SAME original graph. A positive
old canonical support supplies an actual selected vertex from the first common
universal future. The second complete future is constructed around that SAME
vertex, and fixes EVERY graph witness of the first future. BOTH entire numeric
stage certificates are retained, with strictly increasing numerical cutoffs.

The first witnesses remain fixed graph vertices. Their designation as active
future sorts is not preserved: the explicitly constructed second column is zero
at every old intermediate original other than the chosen pivot. This is a finite
coherence theorem, not an infinite diary or full Kpt-source construction. -/
theorem henson_leftDense_two_coherent_pointed_stages
    (E : Nat → Nat → Bool) (d e ell b k : Nat)
    (hell : 2 ≤ ell) (hd : 0 < d) (he : 0 < e)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool)
    (T : IntegerGraphSupport d ell)
    (hPositive : 0 < integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) T)
    (pi : Fin e → Fin d) (beta : Fin e → Bool) :
    let B := finiteOldColumnRawBound E ell d (Finset.range b) c
    let V := RelativeUniversalTaggedVertex d ell B
    let W : Finset Nat := finiteTaggedFuturePool (V := V) b
    let tau : Nat → Fin d := finiteTaggedFutureSort hd
      (relativeUniversalTaggedSort d ell B) b
    ∃ (f : Nat → Nat) (M w H : Nat) (g : Nat → Nat) (M' : Nat),
      FiniteNumericStageWitness E d ell b k hd c f M ∧
      w ∈ W ∧ tau w ∈ T.1 ∧ b ≤ f w ∧
      (∀ x ∈ W, f x < H) ∧
      (∀ p, p < b → E p (f w) = c p (tau w) ∧
        E (f w) p = c p (tau w)) ∧
      (finiteOldColumnRawBound E ell e (Finset.range H)
        (pointedContinuationColumn b (f w) c pi beta) =
          pointedContinuationRawBound E ell b c (tau w) pi beta) ∧
      FiniteNumericStageWitness E e ell H k he
        (pointedContinuationColumn b (f w) c pi beta) g M' ∧
      (∀ p, p < H → g p = p) ∧
      (∀ x ∈ W, g (f x) = f x) ∧ g (f w) = f w ∧ M < M' := by
  obtain ⟨f, M, hFirst⟩ := henson_leftDense_finite_numeric_stage_witness
    E d ell b k hell hd hAvoid hDense c
  obtain ⟨w, H, g, M', hRest⟩ := finiteNumericStageWitness_extends_pointed
    E d e ell b k hell hd he hAvoid hDense c T hPositive pi beta f M hFirst
  exact ⟨f, M, w, H, g, M', hFirst, hRest⟩

#print axioms Kk.henson_leftDense_finite_numeric_stage_witness
#print axioms Kk.finiteNumericStageWitness_original_columns
#print axioms Kk.henson_leftDense_constructs_pointed_continuation
#print axioms Kk.finiteNumericStageWitness_extends_pointed
#print axioms Kk.henson_leftDense_two_coherent_pointed_stages

end Kk
