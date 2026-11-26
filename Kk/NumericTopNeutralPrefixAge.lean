import Kk.FullRealGenerationCapacity
import Kk.NumericHFullSelectedColumn
import Kk.TrackFTypePrefixCanonicalAgeSandwich
import Mathlib.Tactic

/-!
# Actual TOP columns: whole numerical-prefix age neutrality

English proof and independent review were committed before this source:
`docs/selected_top_age_neutral_b3_english_20261124.md` and
`docs/audits/2026-11-24-selected-top-b3-independent-review.md`.

The ordinary columns are the literal numerical-H columns into later TOP
copies. Every old block is present before the tested real cut, and every
positive common neighbour through that cut comes from a base at most the
tested base. Complete real-copy capacity equality therefore sandwiches the
two WHOLE numerical-prefix canonical ages between the actual base-prefix
ages. Equal base endpoint ages force exact physical prefix-age equality.

This is a finite ordinary-L statement. It does not by itself instantiate
chosen B3, actual AlgorithmRun stage inclusion, or the resolved-Q constructor.
The Boolean tables are total on Nat, so no finite-carrier bound is required
by the capacity calculation. Genuine original/carrier bounds must still be
supplied when applying it to physical selected sources.
-/

namespace Kk

open SuccessorTree.V10

/-- Literal ordinary columns into the displayed TOP copies. The target list
may repeat a base; distinct sort labels are not required to be distinct names. -/
noncomputable def numericHTopActualColumn
    (E : Nat → Nat → Bool) (d k N : Nat)
    (target : Fin d → Nat) : Nat → Fin d → Bool :=
  fun z t => (finiteNumericHL (normalizedGraphModel E) k N).binary
    z (hPosition k (target t) k) (0 : Fin 1)

/-- Actual canonical ordinary reference age on the ENTIRE numerical prefix,
including every generation and every odd coordinate. -/
noncomputable def numericHTopPrefixCanonicalAge
    (E : Nat → Nat → Bool) (ell d k N prefixBound : Nat)
    (target : Fin d → Nat) : IntegerGraphSupport d ell → Nat :=
  integerGraphAgeCanonical d ell
    (finiteOldColumnRawBound
      (fun x y => (finiteNumericHL (normalizedGraphModel E) k N).binary
        x y (0 : Fin 1)) ell d (Finset.range prefixBound)
      (numericHTopActualColumn E d k N target))

/-- Actual canonical base-graph reference age of the same displayed future
columns. This is computed from all old bases, not from assigned age labels. -/
noncomputable def baseTopPrefixCanonicalAge
    (E : Nat → Nat → Bool) (ell d prefixBound : Nat)
    (target : Fin d → Nat) : IntegerGraphSupport d ell → Nat :=
  integerGraphAgeCanonical d ell
    (finiteOldColumnRawBound E ell d (Finset.range prefixBound)
      (fun q t => E q (target t)))

/-- At any bounded real generation, the complete numerical prefix common
capacity lies between the actual before-base and after-base capacities.
Nonemptiness of the support excludes odd/fake common neighbours. The proof
uses set inclusions in complete real-copy pools, so repeated generations
cannot create an extra clique and repeated sort labels are permitted. -/
theorem numericHTop_prefix_common_capacity_sandwich
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (d k N b g : Nat) (hg : g ≤ k)
    (target : Fin d → Nat) (hLater : ∀ t, b < target t)
    (S : Finset (Fin d)) (hS : S.Nonempty) :
    let L : Nat → Nat → Bool := fun x y =>
      (finiteNumericHL (normalizedGraphModel E) k N).binary x y (0 : Fin 1)
    let C := numericHTopActualColumn E d k N target
    let B := fun q t => E q (target t)
    let Q0 := oldSupportCommonNeighbourPool (Finset.range b) B S
    let Q1 := oldSupportCommonNeighbourPool (Finset.range (b+1)) B S
    let H0 := oldSupportCommonNeighbourPool (Finset.range (hPosition k b g)) C S
    let H1 := oldSupportCommonNeighbourPool
      (Finset.range (hPosition k b g+1)) C S
    finiteDirectedCliqueCapacity E Q0 ≤ finiteDirectedCliqueCapacity L H0 ∧
      finiteDirectedCliqueCapacity L H0 ≤ finiteDirectedCliqueCapacity L H1 ∧
      finiteDirectedCliqueCapacity L H1 ≤ finiteDirectedCliqueCapacity E Q1 := by
  classical
  intro L C B Q0 Q1 H0 H1
  have hColumn : ∀ q m : Nat, q ≤ b → m ≤ k → ∀ t : Fin d,
      C (hPosition k q m) t = E q (target t) := by
    intro q m hqb hm t
    change hNumericBinary (normalizedGraphModel E).binary k
      (hPosition k q m) (hPosition k (target t) k) (0 : Fin 1) =
        (normalizedGraphModel E).binary q (target t) (0 : Fin 1)
    exact numericH_older_generation_to_top_exact
      (normalizedGraphModel E).binary k q (target t) m (0 : Fin 1)
      (lt_of_le_of_lt hqb (hLater t)) hm
  have hLowerPool : numericHCompleteRealPool k Q0 ⊆ H0 := by
    intro z hz
    obtain ⟨q,hq,m,hm,hzEq⟩ :=
      (numericHCompleteRealPool_mem_iff k Q0 z).1 hz
    obtain ⟨hqRange,hqAll⟩ := Finset.mem_filter.mp hq
    have hqb : q < b := Finset.mem_range.mp hqRange
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      rw [← hzEq]
      exact hPosition_lt_of_block_lt k q b m g hm hqb
    · intro t ht
      rw [← hzEq, hColumn q m (Nat.le_of_lt hqb) hm t]
      exact hqAll t ht
  have hMiddlePool : H0 ⊆ H1 := by
    intro z hz
    obtain ⟨hzRange,hzAll⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_filter.mpr ⟨?_,hzAll⟩
    have hzLt := Finset.mem_range.mp hzRange
    exact Finset.mem_range.mpr (by omega)
  have hUpperPool : H1 ⊆ numericHCompleteRealPool k Q1 := by
    intro z hz
    obtain ⟨hzRange,hzAll⟩ := Finset.mem_filter.mp hz
    have hzLe : z ≤ hPosition k b g := by
      have hzLt := Finset.mem_range.mp hzRange
      omega
    obtain ⟨t,ht⟩ := hS
    have hPositive : hNumericBinary (normalizedGraphModel E).binary k
        z (hPosition k (target t) k) (0 : Fin 1) = true := hzAll t ht
    obtain ⟨i,j,q,m,_hij,hq,hm,_hGate,hDir⟩ :=
      (hNumericBinary_true_iff (normalizedGraphModel E).binary k
        z (hPosition k (target t) k) (0 : Fin 1)).1 hPositive
    have hReal : ∃ a r : Nat, r ≤ k ∧ z = hPosition k a r := by
      rcases hDir with ⟨hzI,_hTarget,_hBase⟩ | ⟨hzJ,_hTarget,_hBase⟩
      · exact ⟨i,q,hq,hzI⟩
      · exact ⟨j,m,hm,hzJ⟩
    obtain ⟨a,r,hr,hzEq⟩ := hReal
    have hab : a ≤ b := by
      by_contra hNot
      have hba : b < a := by omega
      have hAfter := hPosition_lt_of_block_lt k b a g r hg hba
      rw [hzEq] at hzLe
      omega
    apply (numericHCompleteRealPool_mem_iff k Q1 z).2
    refine ⟨a,?_,r,hr,hzEq.symm⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega),?_⟩
    intro s hs
    have hBit := hzAll s hs
    rw [hzEq,hColumn a r hab hr s] at hBit
    exact hBit
  have hLow := finiteDirectedCliqueCapacity_mono L
    (numericHCompleteRealPool k Q0) H0 hLowerPool
  have hLowEq : finiteDirectedCliqueCapacity L
      (numericHCompleteRealPool k Q0) = finiteDirectedCliqueCapacity E Q0 :=
    finiteNumericH_complete_real_capacity_eq_original E hSym k N Q0
  rw [hLowEq] at hLow
  have hMid := finiteDirectedCliqueCapacity_mono L H0 H1 hMiddlePool
  have hHigh := finiteDirectedCliqueCapacity_mono L H1
    (numericHCompleteRealPool k Q1) hUpperPool
  have hHighEq : finiteDirectedCliqueCapacity L
      (numericHCompleteRealPool k Q1) = finiteDirectedCliqueCapacity E Q1 :=
    finiteNumericH_complete_real_capacity_eq_original E hSym k N Q1
  rw [hHighEq] at hHigh
  exact ⟨hLow,hMid,hHigh⟩

/-- Full canonical-age sandwich on all admissible supports. Canonicalization
is used monotonically, without asserting equality of raw and canonical ages.
The pure capacity statement is valid at arbitrary ell and d, including an
empty sort set, because every requested support is explicitly nonempty. -/
theorem numericHTop_prefix_canonical_age_sandwich
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (ell d k N b g : Nat) (hg : g ≤ k)
    (target : Fin d → Nat) (hLater : ∀ t, b < target t) :
    AgeLe (baseTopPrefixCanonicalAge E ell d (b+1) target)
      (numericHTopPrefixCanonicalAge E ell d k N (hPosition k b g+1) target) ∧
    AgeLe (numericHTopPrefixCanonicalAge E ell d k N (hPosition k b g+1) target)
      (numericHTopPrefixCanonicalAge E ell d k N (hPosition k b g) target) ∧
    AgeLe (numericHTopPrefixCanonicalAge E ell d k N (hPosition k b g) target)
      (baseTopPrefixCanonicalAge E ell d b target) := by
  classical
  let L : Nat → Nat → Bool := fun x y =>
    (finiteNumericHL (normalizedGraphModel E) k N).binary x y (0 : Fin 1)
  let C := numericHTopActualColumn E d k N target
  let B := fun q t => E q (target t)
  let Q0 := finiteOldColumnRawBound E ell d (Finset.range b) B
  let Q1 := finiteOldColumnRawBound E ell d (Finset.range (b+1)) B
  let H0 := finiteOldColumnRawBound L ell d (Finset.range (hPosition k b g)) C
  let H1 := finiteOldColumnRawBound L ell d (Finset.range (hPosition k b g+1)) C
  have hRaw : AgeLe Q1 H1 ∧ AgeLe H1 H0 ∧ AgeLe H0 Q0 := by
    have hAt : ∀ T : IntegerGraphSupport d ell,
        Q1 T ≤ H1 T ∧ H1 T ≤ H0 T ∧ H0 T ≤ Q0 T := by
      intro T
      have hCapacity := numericHTop_prefix_common_capacity_sandwich
        E hSym d k N b g hg target hLater T.1 T.2.1
      dsimp only [Q0,Q1,H0,H1,finiteOldColumnRawBound]
      dsimp only [L,C,B] at hCapacity ⊢
      omega
    exact ⟨fun T => (hAt T).1,
      fun T => (hAt T).2.1,fun T => (hAt T).2.2⟩
  exact ⟨integerGraphAgeCanonical_mono_raw d ell Q1 H1 hRaw.1,
    integerGraphAgeCanonical_mono_raw d ell H1 H0 hRaw.2.1,
    integerGraphAgeCanonical_mono_raw d ell H0 Q0 hRaw.2.2⟩

/-- Actual base-prefix canonical neutrality forces equality of the complete
physical numerical ages before and through the tested real cut. Both equal
the same original reference age. No equality of singleton ranks alone, no
source-coherence assumption and no chosen B3 verdict are used. -/
theorem numericHTop_prefix_canonical_ages_eq_of_base_neutral
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (ell d k N b g : Nat) (hg : g ≤ k)
    (target : Fin d → Nat) (hLater : ∀ t, b < target t)
    (hNeutral : baseTopPrefixCanonicalAge E ell d b target =
      baseTopPrefixCanonicalAge E ell d (b+1) target) :
    numericHTopPrefixCanonicalAge E ell d k N (hPosition k b g) target =
      numericHTopPrefixCanonicalAge E ell d k N (hPosition k b g+1) target ∧
    numericHTopPrefixCanonicalAge E ell d k N (hPosition k b g) target =
      baseTopPrefixCanonicalAge E ell d b target := by
  obtain ⟨hLow,hMid,hHigh⟩ := numericHTop_prefix_canonical_age_sandwich
    E hSym ell d k N b g hg target hLater
  constructor
  · funext T
    apply Nat.le_antisymm
    · exact (hHigh T).trans (by simpa only [hNeutral] using hLow T)
    · exact hMid T
  · funext T
    apply Nat.le_antisymm (hHigh T)
    have h := (hLow T).trans (hMid T)
    simpa only [hNeutral] using h

#print axioms Kk.numericHTop_prefix_common_capacity_sandwich
#print axioms Kk.numericHTop_prefix_canonical_age_sandwich
#print axioms Kk.numericHTop_prefix_canonical_ages_eq_of_base_neutral

end Kk
