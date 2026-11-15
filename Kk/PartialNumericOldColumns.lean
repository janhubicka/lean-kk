import Kk.FullBlockActualAge
import Kk.NumericPrefixGapZero
import Mathlib.Tactic

/-!
# Track A: literal PARTIAL numerical-H prefix and actual old/top L columns

The English-first proof and 20 hostile checks precede this module:
  docs/partial_numeric_old_columns_english_audit.md

Unlike a completed block, [0,hPosition(k,b,g)) with g<=k includes
only the generations q<g of original b. We prove the literal
partition into all real generations of earlier originals, these
partial b real generations, and every odd dummy; then identify the
TRUE actual finite numerical-H binary L columns to any later top
original in both orientations. The raw/canonical old age is
computed without odd dummies in the U-common-neighbourhood,
for every NONEMPTY future support U.

This does NOT identify the partial age with the complete original
age: the mixed-generation clique capacity can be strictly smaller.
The sharp partial-capacity formula is recorded separately in the
English audit and needs its own Lean proof.
-/

namespace Kk

open SuccessorTree.V10

/-- All EVEN numbered physical old-prefix coordinates at an
intermediate original-block cut. These are precisely the bounded
real generations, including incomplete current original b. -/
def numericHPartialRealPool (k b g : Nat) : Finset Nat :=
  (Finset.range (hPosition k b g)).filter (fun z => z % 2 = 0)

/-- All odd dummy coordinates in the same literal partial prefix.
The numerical-H binary L to later tops is identically zero here. -/
def numericHPartialOddPool (k b g : Nat) : Finset Nat :=
  (Finset.range (hPosition k b g)).filter (fun z => z % 2 = 1)

/-- Every bounded real generation has an even numerical coordinate. -/
theorem numericH_partial_hPosition_even (k i q : Nat) :
    hPosition k i q % 2 = 0 := by
  have hFactor :
      hPosition k i q = 2 * ((k + 1) * i + q) := by
    dsimp [hPosition]
    ring
  rw [hFactor]
  simp [Nat.mul_mod]

/-- Exactly the real and odd coordinates constitute the whole
numbered old partial prefix. No selected-front shadow appears. -/
theorem numericH_partial_real_odd_partition (k b g : Nat) :
    Finset.range (hPosition k b g) =
      numericHPartialRealPool k b g ∪
        numericHPartialOddPool k b g := by
  classical
  ext z
  constructor
  · intro hz
    by_cases hEven : z % 2 = 0
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨hz,hEven⟩))
    · have hLtMod : z % 2 < 2 := Nat.mod_lt z (by omega)
      have hOdd : z % 2 = 1 := by omega
      exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨hz,hOdd⟩))
  · intro hz
    rcases Finset.mem_union.mp hz with hReal | hOdd
    · exact (Finset.mem_filter.mp hReal).1
    · exact (Finset.mem_filter.mp hOdd).1

/-- The two coordinate sorts are disjoint, including the empty
current generation and k=0 cases. -/
theorem numericH_partial_real_odd_disjoint (k b g : Nat) :
    Disjoint (numericHPartialRealPool k b g)
      (numericHPartialOddPool k b g) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hzReal hzOdd
  have h0 : z % 2 = 0 := (Finset.mem_filter.mp hzReal).2
  have h1 : z % 2 = 1 := (Finset.mem_filter.mp hzOdd).2
  omega

/-- An even coordinate before a PARTIAL original-block cut is
a real generation of an original i<=b. If i=b, its generation
is strictly below the cut generation g. This uses the literal
numerical coordinate classification, not an age inference. -/
theorem numericH_partial_real_repr
    (k b g z : Nat) (hg : g ≤ k)
    (hz : z ∈ numericHPartialRealPool k b g) :
    ∃ i q : Nat, i ≤ b ∧ q ≤ k ∧ z = hPosition k i q ∧
      (i < b ∨ (i = b ∧ q < g)) := by
  have hzRange := (Finset.mem_filter.mp hz).1
  have hzEven : z % 2 = 0 := (Finset.mem_filter.mp hz).2
  have hzLt : z < hPosition k b g := Finset.mem_range.mp hzRange
  rcases numericCoordinate_odd_or_real k z with
    ⟨a,ha⟩ | ⟨i,q,hq,hReal⟩
  · rw [ha] at hzEven
    omega
  · have hCut : hPosition k i q < hPosition k b g := by
      rw [←hReal]
      exact hzLt
    have hNext : hPosition k b g < hPosition k (b+1) 0 :=
      hPosition_lt_of_block_lt k b (b+1) g 0 hg (by omega)
    have hLtNext : hPosition k i q < hPosition k (b+1) 0 := by
      omega
    have hi : i ≤ b := by
      rcases hPosition_before k i q (b+1) 0 hq
        (by omega) hLtNext with hBefore | ⟨hEqual,hImpossible⟩
      · omega
      · omega
    refine ⟨i,q,hi,hq,hReal,?_⟩
    by_cases hlt : i < b
    · exact Or.inl hlt
    · have hieq : i = b := by omega
      have hqLt : q < g := by
        rw [hieq] at hCut
        dsimp [hPosition] at hCut
        omega
      exact Or.inr ⟨hieq,hqLt⟩

/-- At a genuine partial cut, its EVEN pool consists precisely of
all generations of earlier originals and q<g of current original b.
At g=0 this reduces to the earlier complete real-copy pool. -/
theorem numericH_partial_real_pool_exact
    (k b g : Nat) (hg : g ≤ k) :
    numericHPartialRealPool k b g =
      numericHCompleteRealPool k (Finset.range b) ∪
        (Finset.range g).image (fun q => hPosition k b q) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨i,q,hi,hq,hEq,hCase⟩ :=
      numericH_partial_real_repr k b g z hg hz
    rcases hCase with hiLt | ⟨hiEq,hqLt⟩
    · apply Finset.mem_union.mpr
      left
      apply (numericHCompleteRealPool_mem_iff k
        (Finset.range b) z).mpr
      exact ⟨i,Finset.mem_range.mpr hiLt,q,hq,hEq.symm⟩
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      refine ⟨q,Finset.mem_range.mpr hqLt,?_⟩
      rw [hiEq] at hEq
      exact hEq.symm
  · intro hz
    rcases Finset.mem_union.mp hz with hEarlier | hCurrent
    · obtain ⟨i,hi,q,hq,hEq⟩ :=
        (numericHCompleteRealPool_mem_iff k
          (Finset.range b) z).mp hEarlier
      have hLt : hPosition k i q < hPosition k b g :=
        hPosition_lt_of_block_lt k i b q g hq
          (Finset.mem_range.mp hi)
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_,?_⟩
      · rw [←hEq]
        exact hLt
      · rw [←hEq]
        exact numericH_partial_hPosition_even k i q
    · obtain ⟨q,hq,hEq⟩ := Finset.mem_image.mp hCurrent
      have hqLt : q < g := Finset.mem_range.mp hq
      have hLt : hPosition k b q < hPosition k b g := by
        dsimp [hPosition]
        omega
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_,?_⟩
      · rw [←hEq]
        exact hLt
      · rw [←hEq]
        exact numericH_partial_hPosition_even k b q

/-- A total typed old column at a PARTIAL cut:
every included real generation carries its original's E-column;
every odd dummy has a zero ordinary-L column. -/
noncomputable def numericHPartialOldColumn
    {d : Nat} (k b g : Nat) (c : Nat → Fin d → Bool) :
    Nat → Fin d → Bool :=
  fun z t =>
    if z ∈ numericHPartialRealPool k b g
    then c (numericHRealOriginal k z) t
    else false

/-- The TRUE partial-prefix-to-later-top numerical-H L column
agrees on EVERY old physical coordinate and in BOTH directions
with the original's E column (real) or zero (odd).
The later original j(t) is GIVEN and lies strictly beyond b. -/
theorem finiteNumericH_partial_actual_top_column_both
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k b g M : Nat) (hg : g ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t)
    (z : Nat) (hz : z < hPosition k b g)
    (t : Fin d) :
    (finiteNumericHL (normalizedGraphModel E) k M).binary
        z (hPosition k (j t) k) (0 : Fin 1) =
      numericHPartialOldColumn k b g
        (fun i u => E i (j u)) z t ∧
    (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k (j t) k) z (0 : Fin 1) =
      numericHPartialOldColumn k b g
        (fun i u => E i (j u)) z t := by
  classical
  by_cases hzReal : z ∈ numericHPartialRealPool k b g
  · obtain ⟨i,q,hi,hq,hEq,_⟩ :=
      numericH_partial_real_repr k b g z hg hzReal
    have hij : i < j t := lt_of_le_of_lt hi (hj t)
    have hForward :
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          z (hPosition k (j t) k) (0 : Fin 1) = E i (j t) := by
      rw [hEq]
      change hNumericBinary (normalizedGraphModel E).binary k
        (hPosition k i q) (hPosition k (j t) k)
        (0 : Fin 1) = E i (j t)
      exact numericH_older_generation_to_top_exact
        (normalizedGraphModel E).binary k i (j t) q
        (0 : Fin 1) hij hq
    have hSwap :
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          z (hPosition k (j t) k) (0 : Fin 1) =
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k (j t) k) z (0 : Fin 1) :=
      henson_finiteNumericH_binary_symmetric E hSym k M
        z (hPosition k (j t) k)
    have hCol :
        numericHPartialOldColumn k b g
          (fun i u => E i (j u)) z t = E i (j t) := by
      have hMem : hPosition k i q ∈ numericHPartialRealPool k b g := by
        rw [← hEq]
        exact hzReal
      rw [hEq]
      simp [numericHPartialOldColumn,hMem,
        numericHRealOriginal_at k i q hq]
    exact ⟨hForward.trans hCol.symm,
      (hSwap.symm.trans hForward).trans hCol.symm⟩
  · have hzEvenNo : z % 2 ≠ 0 := by
      intro heven
      exact hzReal
        (Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hz,heven⟩)
    have hzOdd : z % 2 = 1 := by
      have hm : z % 2 < 2 := Nat.mod_lt z (by omega)
      omega
    have hzForm : z = 2 * (z / 2) + 1 := by
      have hm := Nat.mod_add_div z 2
      omega
    have hZero := finiteNumericH_odd_dummy_to_top_zero
      E k M (z / 2) (j t)
    have hCol :
        numericHPartialOldColumn k b g
          (fun i u => E i (j u)) z t = false := by
      simp [numericHPartialOldColumn,hzReal]
    have hForward :
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          z (hPosition k (j t) k) (0 : Fin 1) = false := by
      rw [hzForm]
      exact hZero.1
    have hReverse :
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k (j t) k) z (0 : Fin 1) = false := by
      rw [hzForm]
      exact hZero.2
    exact ⟨hForward.trans hCol.symm, hReverse.trans hCol.symm⟩

/-- At every NONEMPTY future support, the literal full old
numbered prefix and the EVEN real pool have the same actual
old common-neighbourhood. The odd dummies are present but
their genuine L columns to later tops vanish. -/
theorem finiteNumericH_partial_actual_common_pool_eq
    {d ell : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k b g M : Nat) (hg : g ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t)
    (U : IntegerGraphSupport d ell) :
    oldSupportCommonNeighbourPool
      (Finset.range (hPosition k b g))
      (fun z t => (finiteNumericHL
        (normalizedGraphModel E) k M).binary
          z (hPosition k (j t) k) (0 : Fin 1)) U.1 =
    oldSupportCommonNeighbourPool
      (numericHPartialRealPool k b g)
      (numericHPartialOldColumn k b g
        (fun i t => E i (j t))) U.1 := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨hzRange,hAll⟩ := Finset.mem_filter.mp hz
    have hzReal : z ∈ numericHPartialRealPool k b g := by
      by_contra hNot
      obtain ⟨t,ht⟩ := U.2.1
      have hActual := hAll t ht
      have hEq :=
        (finiteNumericH_partial_actual_top_column_both
          E hSym k b g M hg j hj z
          (Finset.mem_range.mp hzRange) t).1
      have hZero :
          numericHPartialOldColumn k b g
            (fun i u => E i (j u)) z t = false := by
        simp [numericHPartialOldColumn,hNot]
      change (finiteNumericHL (normalizedGraphModel E) k M).binary
        z (hPosition k (j t) k) (0 : Fin 1) = true at hActual
      rw [hEq,hZero] at hActual
      contradiction
    apply Finset.mem_filter.mpr
    refine ⟨hzReal,?_⟩
    intro t ht
    have hActual := hAll t ht
    have hEq :=
      (finiteNumericH_partial_actual_top_column_both
        E hSym k b g M hg j hj z
        (Finset.mem_range.mp hzRange) t).1
    exact hEq.symm.trans hActual
  · intro hz
    obtain ⟨hzReal,hAll⟩ := Finset.mem_filter.mp hz
    have hzRange : z ∈ Finset.range (hPosition k b g) :=
      (Finset.mem_filter.mp hzReal).1
    apply Finset.mem_filter.mpr
    refine ⟨hzRange,?_⟩
    intro t ht
    have hCol := hAll t ht
    have hEq :=
      (finiteNumericH_partial_actual_top_column_both
        E hSym k b g M hg j hj z
        (Finset.mem_range.mp hzRange) t).1
    exact hEq.trans hCol

/-- The literal actual old numerical-H raw age, at ANY
partial original-block cut BEFORE the top of b, is exactly
the real-pool raw age of its true original-pulled-back column.
This is NOT generally the complete ORIGINAL age. -/
theorem finiteNumericH_partial_actual_raw_age_eq_real_pool
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (ell k b g M : Nat) (hg : g ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t) :
    finiteOldColumnRawBound
      (fun x y => (finiteNumericHL
        (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
      ell d (Finset.range (hPosition k b g))
      (fun z t => (finiteNumericHL (normalizedGraphModel E) k M).binary
        z (hPosition k (j t) k) (0 : Fin 1)) =
    finiteOldColumnRawBound
      (fun x y => (finiteNumericHL
        (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
      ell d (numericHPartialRealPool k b g)
      (numericHPartialOldColumn k b g
        (fun i t => E i (j t))) := by
  funext U
  unfold finiteOldColumnRawBound
  rw [finiteNumericH_partial_actual_common_pool_eq
    E hSym k b g M hg j hj U]

/-- Its canonical integer graph age is unchanged by
excluding odd dummy vertices from the old common pool.
This does not assume a global resolved source. -/
theorem finiteNumericH_partial_actual_canonical_age_eq_real_pool
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (ell k b g M : Nat) (hg : g ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t) :
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound
        (fun x y => (finiteNumericHL
          (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
        ell d (Finset.range (hPosition k b g))
        (fun z t => (finiteNumericHL
          (normalizedGraphModel E) k M).binary
          z (hPosition k (j t) k) (0 : Fin 1))) =
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound
        (fun x y => (finiteNumericHL
          (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
        ell d (numericHPartialRealPool k b g)
        (numericHPartialOldColumn k b g
          (fun i t => E i (j t)))) := by
  rw [finiteNumericH_partial_actual_raw_age_eq_real_pool
    E hSym ell k b g M hg j hj]

#print axioms Kk.numericH_partial_real_odd_partition
#print axioms Kk.numericH_partial_real_odd_disjoint
#print axioms Kk.numericH_partial_real_repr
#print axioms Kk.numericH_partial_real_pool_exact
#print axioms Kk.finiteNumericH_partial_actual_top_column_both
#print axioms Kk.finiteNumericH_partial_actual_common_pool_eq
#print axioms Kk.finiteNumericH_partial_actual_raw_age_eq_real_pool
#print axioms Kk.finiteNumericH_partial_actual_canonical_age_eq_real_pool

end Kk
