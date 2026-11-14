import Kk.FiniteUniformNumericComplete
import Kk.FiniteOldColumnAge
import Kk.IntegerWitnessCanonical
import Mathlib.Tactic

/-!
# KK Track A: exact all-support age preservation under arbitrarily delayed neutral columns

English proof and hostile audit committed FIRST:
  docs/cofinal_neutral_old_column_age_english_audit.md

Fix an entire old original prefix [0,b), and an arbitrary later
cut F>=b. Extend a prescribed complete future type column c by
ZERO on *every* actual original in [b,F). Because the integer
graph-age supports are NONEMPTY, these padded originals cannot
join any common future neighbourhood. Consequently all literal
old-neighbourhood clique capacities, raw bound functions, their
joint integer canonical ages, and their feasible normalized
labelled clique vectors are IDENTICAL before and after padding.

The already checked single-witness finite Henson/numerical-H theorem
applied at F then yields one physical future after F whose full
top-generation L clique profile is still the ORIGINAL age at b.
Every padded original-to-future numerical-H L column is absent at
ALL real generations, in BOTH directions; the unpadded old columns
remain exact. All endpoints concern finite ordinary graph L only.

This does not establish a positive-link reserved-block step or the
coherent infinite resolved diary, full auxiliary H+ E/B3, or BRDs.
-/

namespace Kk

open SuccessorTree.V10

/-- Extend prescribed old-to-future typed columns to a later
original cutoff by making EVERY intervening original have a
completely negative typed column. The unchanged original table
E may have arbitrary edges among these padding originals. -/
def delayedOldColumn {d : Nat} (b : Nat)
    (c : Nat → Fin d → Bool) (p : Nat) (t : Fin d) : Bool :=
  if p < b then c p t else false

theorem delayedOldColumn_old
    {d : Nat} (b : Nat) (c : Nat → Fin d → Bool)
    (p : Nat) (t : Fin d) (hp : p < b) :
    delayedOldColumn b c p t = c p t := by
  simp [delayedOldColumn, hp]

theorem delayedOldColumn_padding_zero
    {d : Nat} (b : Nat) (c : Nat → Fin d → Bool)
    (p : Nat) (t : Fin d) (hp : b ≤ p) :
    delayedOldColumn b c p t = false := by
  have hnp : ¬ p < b := by omega
  simp [delayedOldColumn, hnp]

/-- The essential NONEMPTY-support argument: an inserted padding
original with all-zero columns cannot belong to the common old
neighbourhood of any genuinely nonempty set of future sorts.
The exact finite neighbourhood pools are E-independent. -/
theorem delayedOldCommonNeighbourPool_eq
    {d ell : Nat} (b F : Nat) (hBF : b ≤ F)
    (c : Nat → Fin d → Bool) (T : IntegerGraphSupport d ell) :
    oldSupportCommonNeighbourPool (Finset.range F)
        (delayedOldColumn b c) T.1 =
      oldSupportCommonNeighbourPool (Finset.range b) c T.1 := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hpF,hAll⟩ := Finset.mem_filter.mp hp
    obtain ⟨t,ht⟩ := T.2.1
    have hOne := hAll t ht
    have hpB : p < b := by
      by_contra hnb
      have hpLate : b ≤ p := by omega
      have hZero := delayedOldColumn_padding_zero b c p t hpLate
      rw [hZero] at hOne
      contradiction
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hpB,?_⟩
    intro u hu
    have hCol := hAll u hu
    simpa [delayedOldColumn, hpB] using hCol
  · intro hp
    obtain ⟨hpB,hAll⟩ := Finset.mem_filter.mp hp
    have hpLtB : p < b := Finset.mem_range.mp hpB
    have hpLtF : p < F := lt_of_lt_of_le hpLtB hBF
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hpLtF,?_⟩
    intro u hu
    simpa [delayedOldColumn, hpLtB] using hAll u hu

/-- Equality of the FULL raw old-column bound function at every
nonempty admissible support: no chosen-type or cardinal shortcut.
The raw bound may be zero. -/
theorem delayedOldRawBound_eq
    (E : Nat → Nat → Bool) (ell d b F : Nat)
    (hBF : b ≤ F) (c : Nat → Fin d → Bool) :
    finiteOldColumnRawBound E ell d (Finset.range F)
      (delayedOldColumn b c) =
    finiteOldColumnRawBound E ell d (Finset.range b) c := by
  funext T
  unfold finiteOldColumnRawBound
  rw [delayedOldCommonNeighbourPool_eq b F hBF c T]

/-- In particular the canonicalized jointly feasible integer
graph-age function is IDENTICAL at every support after inserting
an arbitrarily long neutral original prefix. -/
theorem delayedOldCanonicalAge_eq
    (E : Nat → Nat → Bool) (ell d b F : Nat)
    (hBF : b ≤ F) (c : Nat → Fin d → Bool) :
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range F)
        (delayedOldColumn b c)) =
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) := by
  rw [delayedOldRawBound_eq E ell d b F hBF c]

/-- Every normalized feasible labelled clique vector remains
EXACTLY the same under neutral delay. This is a set equality,
not just equality of a few capacity maximizers. -/
theorem delayedOldFeasibleVectors_eq
    (E : Nat → Nat → Bool) (ell d b F : Nat)
    (hBF : b ≤ F) (c : Nat → Fin d → Bool) :
    feasibleIntegerCliqueVectors d ell
      (finiteOldColumnRawBound E ell d (Finset.range F)
        (delayedOldColumn b c)) =
    feasibleIntegerCliqueVectors d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) := by
  rw [delayedOldRawBound_eq E ell d b F hBF c]

/-- For ANY requested later original cutoff F>=b, the same
normalized Henson original E has a finite common numerical-H
top future beyond F realizing exactly the ORIGINAL b-prefix
old-column age. It is pinned on the ENTIRE larger [0,F)
and has zero top-crossing L bits (both directions, ALL real
generations) to every intervening padding original.

The one f and M are selected by invoking the already verified
complete finite numerical-H theorem ONCE at F with the literal
neutral column extension. They work for ALL feasible vectors,
all supports, all old columns and all padding/gap zeros.

This is a neutral-delay lemma. It does not apply when the future
must meet a reserved clique added within [b,F); those positive
links require Track B's separate complete mixed-neighbourhood
certificate and reference-age update.
-/
theorem henson_leftDense_uniform_numericH_after_neutral_delay
    (d ell b F k : Nat)
    (hell : 2 ≤ ell) (hd : 0 < d) (hBF : b ≤ F)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool) :
    let C := delayedOldColumn b c
    let B := finiteOldColumnRawBound E ell d (Finset.range b) c
    let V := RelativeUniversalTaggedVertex d ell B
    let N := F + Fintype.card V
    let W : Finset Nat := finiteTaggedFuturePool (V := V) F
    let A : Nat → Nat → Bool := finiteTaggedOldFutureEdge F E
      (relativeUniversalTaggedEdge d ell B)
      (relativeUniversalTaggedSort d ell B) C
    let tau : Nat → Fin d := finiteTaggedFutureSort hd
      (relativeUniversalTaggedSort d ell B) F
    ∃ (f : Nat → Nat) (M : Nat),
      (∀ i, i < F → f i = i) ∧
      (∀ i j, i < N → j < N → i < j → f i < f j) ∧
      (∀ i j, i < N → j < N → i ≠ j →
        E (f i) (f j) = A i j) ∧
      (∀ m, F ≤ m → m < N → ∀ z, z < f m →
        z ∉ (Finset.range m).image f →
          E z (f m) = false ∧ E (f m) z = false) ∧
      (∀ w ∈ W, F ≤ f w) ∧
      (∀ i ∈ Finset.range F ∪ W.image f,
        hPosition k i k < M) ∧
      (∀ i, i < F → ∀ q, q ≤ k → hPosition k i q < M) ∧
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
      (∀ i, b ≤ i → i < F → ∀ w ∈ W, ∀ q, q ≤ k →
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k i q) (hPosition k (f w) k)
            (0 : Fin 1) = false ∧
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k (f w) k) (hPosition k i q)
            (0 : Fin 1) = false) ∧
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
  let C : Nat → Fin d → Bool := delayedOldColumn b c
  let B : IntegerGraphSupport d ell → Nat :=
    finiteOldColumnRawBound E ell d (Finset.range b) c
  have hRaw :
      finiteOldColumnRawBound E ell d (Finset.range F) C = B :=
    delayedOldRawBound_eq E ell d b F hBF c
  have hMain :=
    henson_leftDense_realizes_all_finite_numericH_L_columns_and_profiles
      d ell F k hell hd E hAvoid hDense C
  rw [hRaw] at hMain
  obtain ⟨f,M,hFix,hMono,hGraph,hGap,hAfter,
      hCut,hOldCarrier,hGapCarrier,hTopCarrier,hProfile,
      hColumns,hGapNumeric,hDummy⟩ := hMain
  have hPrescribed : ∀ i, i < b → ∀ w ∈
      finiteTaggedFuturePool (V := RelativeUniversalTaggedVertex d ell B) F,
      ∀ q, q ≤ k →
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k i q) (hPosition k (f w) k)
            (0 : Fin 1) = c i
                (finiteTaggedFutureSort hd
                  (relativeUniversalTaggedSort d ell B) F w) ∧
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k (f w) k) (hPosition k i q)
            (0 : Fin 1) = c i
                (finiteTaggedFutureSort hd
                  (relativeUniversalTaggedSort d ell B) F w) := by
    intro i hi w hw q hq
    have hBoth := hColumns i (lt_of_lt_of_le hi hBF) w hw q hq
    simpa only [C, delayedOldColumn, if_pos hi] using hBoth
  have hPadding : ∀ i, b ≤ i → i < F → ∀ w ∈
      finiteTaggedFuturePool (V := RelativeUniversalTaggedVertex d ell B) F,
      ∀ q, q ≤ k →
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k i q) (hPosition k (f w) k)
            (0 : Fin 1) = false ∧
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k (f w) k) (hPosition k i q)
            (0 : Fin 1) = false := by
    intro i hi hiF w hw q hq
    have hBoth := hColumns i hiF w hw q hq
    have hNot : ¬ i < b := by omega
    simpa only [C, delayedOldColumn, if_neg hNot] using hBoth
  exact ⟨f,M,hFix,hMono,hGraph,hGap,hAfter,
    hCut,hOldCarrier,hGapCarrier,hTopCarrier,hProfile,
    hPrescribed,hPadding,hGapNumeric,hDummy⟩

#print axioms Kk.delayedOldColumn_old
#print axioms Kk.delayedOldColumn_padding_zero
#print axioms Kk.delayedOldCommonNeighbourPool_eq
#print axioms Kk.delayedOldRawBound_eq
#print axioms Kk.delayedOldCanonicalAge_eq
#print axioms Kk.delayedOldFeasibleVectors_eq
#print axioms Kk.henson_leftDense_uniform_numericH_after_neutral_delay

end Kk
