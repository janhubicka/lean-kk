import Kk.FullRealGenerationCapacity
import Kk.NumericPrefixGapZero
import Mathlib.Tactic

/-!
# Track A: the COMPLETE literal numerical-H old prefix has exactly the original age

English mathematics and hostile audit were committed FIRST in
  docs/full_numeric_block_prefix_age_english_audit.md

For a height k and b old ORIGINAL names, the full H prefix ending
just before original b starts is [0,hPosition k b 0). It consists of
ALL k+1 real generation copies of i<b plus ALL odd fake coordinates
in that numeric interval, with no other positions.

The complete old-to-future typed column at each real generation is
the original c(i,t), while every odd fake has a zero ordinary-L
column to selected future TOP copies. At each NONEMPTY support U,
odd fakes are excluded and the actual old common-neighbourhood is
exactly the complete real-copy pool of the common ORIGINAL U
neighbours. The mixed-generation clique projection proved in
FullRealGenerationCapacity now yields pointwise equality of the
complete numeric prefix raw old age and the original raw old age,
and therefore of canonical integer ages and all feasible vectors.

This equality is for COMPLETE original block boundaries, NOT an
arbitrary partial generation cut inside a reserved original
(which has the separate sharp pivot capacity). It concerns only
ordinary binary L; auxiliary Kpt E/B3, resolved diary and orbit
claims are not asserted.
-/

namespace Kk

open SuccessorTree.V10

/-- All odd fake H coordinates occurring in the COMPLETE numeric
block prefix [0, hPosition k b 0). The dummy ordinary binary L
atoms are zero; this does not constrain auxiliary Kpt E. -/
def numericHFullBlockOddPool (k b : Nat) : Finset Nat :=
  (Finset.range (hPosition k b 0)).filter (fun z => z % 2 = 1)

/-- The literal complete numerical-H prefix is EXACTLY the set of
all real generations of earlier originals, together with ALL odd
dummy positions. No old physical coordinate is omitted. -/
theorem numericH_full_block_prefix_exact
    (k b : Nat) :
    Finset.range (hPosition k b 0) =
      numericHCompleteRealPool k (Finset.range b) ∪
        numericHFullBlockOddPool k b := by
  classical
  ext z
  constructor
  · intro hz
    have hzLt : z < hPosition k b 0 := Finset.mem_range.mp hz
    rcases numericCoordinate_odd_or_real k z with ⟨a,ha⟩ |
      ⟨i,q,hq,hReal⟩
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_filter.mpr
      refine ⟨hz,?_⟩
      rw [ha]
      omega
    · have hi : i < b := by
        by_contra hNot
        have hbi : b ≤ i := by omega
        have hCoeff :
            (2 * (k+1)) * b ≤ (2 * (k+1)) * i :=
          Nat.mul_le_mul_left _ hbi
        dsimp [hPosition] at hzLt hReal
        omega
      apply Finset.mem_union.mpr
      left
      apply (numericHCompleteRealPool_mem_iff k
        (Finset.range b) z).mpr
      exact ⟨i,Finset.mem_range.mpr hi,q,hq,hReal.symm⟩
  · intro hz
    rcases Finset.mem_union.mp hz with hReal | hOdd
    · obtain ⟨i,hi,q,hq,hEq⟩ :=
        (numericHCompleteRealPool_mem_iff k
          (Finset.range b) z).mp hReal
      have hLt : hPosition k i q < hPosition k b 0 :=
        hPosition_lt_of_block_lt k i b q 0 hq
          (Finset.mem_range.mp hi)
      apply Finset.mem_range.mpr
      rw [←hEq]
      exact hLt
    · exact (Finset.mem_filter.mp hOdd).1

/-- Real coordinates are even; fake coordinates are odd.
The two parts of the exact full-prefix decomposition are
DISJOINT, including at height k=0 and empty b=0. -/
theorem numericH_full_block_real_odd_disjoint (k b : Nat) :
    Disjoint
      (numericHCompleteRealPool k (Finset.range b))
      (numericHFullBlockOddPool k b) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hzReal hzOdd
  obtain ⟨i,hi,q,hq,hEq⟩ :=
    (numericHCompleteRealPool_mem_iff k
      (Finset.range b) z).mp hzReal
  have hzMod : z % 2 = 1 := (Finset.mem_filter.mp hzOdd).2
  rw [←hEq] at hzMod
  dsimp [hPosition] at hzMod
  omega

/-- Complete typed original-to-future column on the genuine
numeric-H block prefix: EVERY old real generation carries
the exact original column, and ALL odd dummy coordinates
have completely negative ordinary-L future columns. -/
noncomputable def numericHFullBlockOldColumn
    {d : Nat} (k b : Nat) (c : Nat → Fin d → Bool) :
    Nat → Fin d → Bool :=
  fun z t =>
    if z ∈ numericHCompleteRealPool k (Finset.range b)
    then c (numericHRealOriginal k z) t
    else false

/-- Exactly the same prescribed original column appears at
EVERY bounded real generation of each original i<b. -/
theorem numericH_full_block_real_column
    {d : Nat} (k b i q : Nat)
    (hi : i < b) (hq : q ≤ k)
    (c : Nat → Fin d → Bool) (t : Fin d) :
    numericHFullBlockOldColumn k b c
      (hPosition k i q) t = c i t := by
  classical
  have hMem : hPosition k i q ∈
      numericHCompleteRealPool k (Finset.range b) :=
    (numericHCompleteRealPool_mem_iff k
      (Finset.range b) (hPosition k i q)).mpr
      ⟨i,Finset.mem_range.mpr hi,q,hq,rfl⟩
  simp [numericHFullBlockOldColumn,hMem,
    numericHRealOriginal_at k i q hq]

/-- Every odd fake numeric coordinate has ZERO ordinary
old-to-future column, independently of its auxiliary E data. -/
theorem numericH_full_block_odd_column
    {d : Nat} (k b z : Nat)
    (hz : z ∈ numericHFullBlockOddPool k b)
    (c : Nat → Fin d → Bool) (t : Fin d) :
    numericHFullBlockOldColumn k b c z t = false := by
  classical
  have hNotReal :
      z ∉ numericHCompleteRealPool k (Finset.range b) := by
    intro hReal
    exact (Finset.disjoint_left.mp
      (numericH_full_block_real_odd_disjoint k b)) hReal hz
  simp [numericHFullBlockOldColumn,hNotReal]

/-- At EVERY admissible NONEMPTY support U the complete numeric
old common-neighbour pool contains exactly the full real copies
of the ORIGINAL common-neighbour pool. Every odd dummy is excluded
by its complete ZERO future column. This is equality of actual
finite Nat-coordinate sets, not just clique capacities. -/
theorem numericH_full_block_common_neighbourhood_eq
    {d ell : Nat} (k b : Nat)
    (c : Nat → Fin d → Bool)
    (U : IntegerGraphSupport d ell) :
    oldSupportCommonNeighbourPool
      (Finset.range (hPosition k b 0))
      (numericHFullBlockOldColumn k b c) U.1 =
    numericHCompleteRealPool k
      (oldSupportCommonNeighbourPool (Finset.range b) c U.1) := by
  classical
  let Real : Finset Nat :=
    numericHCompleteRealPool k (Finset.range b)
  have hRealEq :=
    finiteNumericH_complete_real_common_pool_eq
      k (Finset.range b) c U
  ext z
  constructor
  · intro hz
    obtain ⟨hzRange,hAll⟩ := Finset.mem_filter.mp hz
    have hzReal : z ∈ Real := by
      by_contra hNo
      obtain ⟨t,ht⟩ := U.2.1
      have hBit := hAll t ht
      have hZero : numericHFullBlockOldColumn k b c z t = false := by
        simp [numericHFullBlockOldColumn,Real,hNo]
      rw [hZero] at hBit
      contradiction
    have hCommon :
        z ∈ oldSupportCommonNeighbourPool Real
          (numericHRealColumn k c) U.1 := by
      apply Finset.mem_filter.mpr
      refine ⟨hzReal,?_⟩
      intro t ht
      have hBit := hAll t ht
      simpa [numericHFullBlockOldColumn,
        numericHRealColumn, Real,hzReal] using hBit
    rw [hRealEq] at hCommon
    exact hCommon
  · intro hz
    have hCommon :
        z ∈ oldSupportCommonNeighbourPool Real
          (numericHRealColumn k c) U.1 := by
      rw [hRealEq]
      exact hz
    obtain ⟨hzReal,hAll⟩ := Finset.mem_filter.mp hCommon
    have hzRange : z ∈ Finset.range (hPosition k b 0) := by
      have hzUnion : z ∈
          numericHCompleteRealPool k (Finset.range b) ∪
            numericHFullBlockOddPool k b :=
        Finset.mem_union.mpr (Or.inl hzReal)
      rw [←numericH_full_block_prefix_exact k b] at hzUnion
      exact hzUnion
    apply Finset.mem_filter.mpr
    refine ⟨hzRange,?_⟩
    intro t ht
    have hBit := hAll t ht
    simpa [numericHFullBlockOldColumn,
      numericHRealColumn,Real,hzReal] using hBit

/-- The literal COMPLETE numerical-H prefix old raw age,
including every real generation and every odd dummy, is
IDENTICAL at ALL supports to the original old-prefix raw age.
It needs no genuine-age positivity or source-orbit assumptions,
but it is not the age at a PARTIAL generation cut. -/
theorem finiteNumericH_full_block_raw_age_eq_original
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (ell d k b M : Nat)
    (c : Nat → Fin d → Bool) :
    finiteOldColumnRawBound
      (fun x y => (finiteNumericHL
        (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
      ell d (Finset.range (hPosition k b 0))
      (numericHFullBlockOldColumn k b c) =
    finiteOldColumnRawBound E ell d (Finset.range b) c := by
  funext U
  unfold finiteOldColumnRawBound
  rw [numericH_full_block_common_neighbourhood_eq k b c U]
  exact congrArg (fun n : Nat => ell - 1 - n)
    (finiteNumericH_complete_real_capacity_eq_original
      E hSym k M
      (oldSupportCommonNeighbourPool (Finset.range b) c U.1))

/-- Thus the COMPLETE numbered numeric-H old-prefix
canonical integer graph age agrees with the original
old-prefix age, pointwise on every nonempty support. -/
theorem finiteNumericH_full_block_canonical_age_eq_original
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (ell d k b M : Nat)
    (c : Nat → Fin d → Bool) :
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound
        (fun x y => (finiteNumericHL
          (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
        ell d (Finset.range (hPosition k b 0))
        (numericHFullBlockOldColumn k b c)) =
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) := by
  rw [finiteNumericH_full_block_raw_age_eq_original
    E hSym ell d k b M c]

/-- All normalized feasible labelled clique vectors are
unchanged under this exact complete-block numerical expansion,
not just the canonical maximum of one support coordinate. -/
theorem finiteNumericH_full_block_feasible_vectors_eq_original
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (ell d k b M : Nat)
    (c : Nat → Fin d → Bool) :
    feasibleIntegerCliqueVectors d ell
      (finiteOldColumnRawBound
        (fun x y => (finiteNumericHL
          (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
        ell d (Finset.range (hPosition k b 0))
        (numericHFullBlockOldColumn k b c)) =
    feasibleIntegerCliqueVectors d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) := by
  rw [finiteNumericH_full_block_raw_age_eq_original
    E hSym ell d k b M c]

/-- To interpret the complete prefix as an ACTUAL finite-H
substructure, choose a carrier cutoff M at least the start
of the next original block. The total Boolean L table by
itself does not establish carrier membership. -/
theorem finiteNumericH_full_block_carrier_of_cut
    (E : Nat → Nat → Bool)
    (k b M : Nat) (hM : hPosition k b 0 ≤ M) :
    ∀ z ∈ Finset.range (hPosition k b 0),
      z ∈ (finiteNumericHL (normalizedGraphModel E) k M).carrier := by
  intro z hz
  change z < M
  exact lt_of_lt_of_le (Finset.mem_range.mp hz) hM

#print axioms Kk.numericH_full_block_prefix_exact
#print axioms Kk.numericH_full_block_real_odd_disjoint
#print axioms Kk.numericH_full_block_real_column
#print axioms Kk.numericH_full_block_odd_column
#print axioms Kk.numericH_full_block_common_neighbourhood_eq
#print axioms Kk.finiteNumericH_full_block_raw_age_eq_original
#print axioms Kk.finiteNumericH_full_block_canonical_age_eq_original
#print axioms Kk.finiteNumericH_full_block_feasible_vectors_eq_original
#print axioms Kk.finiteNumericH_full_block_carrier_of_cut

end Kk
