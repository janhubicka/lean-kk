import Kk.B3CutStarLocality
import SuccessorTree.V10.HExactE
import Mathlib.Tactic

/-!
# Exact first-gadget E free cut in the numerical H scaffold

In a 2-vertex auxiliary clique gadget one proposes to put the first
original j at generation 0 and the second original j+1 at generation 1.
The actual E free cut of the latter is EXACTLY one coordinate after
the former:

  fl_H(iota(j+1,1)) = iota(j,0)+1          (1<k).

Thus at cut iota(j,0), the second original PASSES the numerical H
free-cut eligibility condition cut+1 <= fl_H(second). This is not
a proof that it belongs to Algorithm 5.4's full source: that also
requires a strict higher closure node prefixing its Kpt original.
It does show that invoking the E gate alone cannot exclude it.

This is the precise remaining obstruction to the manuscript's claim
that the first of two reserved clique vertices is always boring:
one must inspect full parameter-closed selection, or prove no
B3 witness involving the eligible second original is new.
-/

namespace Kk

open SuccessorTree.V10

/-- Exact free level of the generation-one real vertex of the next
original block in the ACTUAL finite numerical H, not merely in
a model with postulated E columns. -/
theorem finiteNumericH_next_generation_one_freeLevel
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N j : Nat)
    (hk : 1 < k)
    (hVertex : hPosition k (j+1) 1 < N) :
    (finiteNumericH K k N).freeLevel (hPosition k (j+1) 1) =
      hPosition k j 0 + 1 := by
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  let v : Nat := hPosition k (j+1) 1
  let c : Nat := hPosition k j 0 + 1
  have hColumn : ∀ u : Nat, A.E u v = true ↔ u < c := by
    intro u
    change finiteNumericHE k N u v = true ↔ u < c
    constructor
    · intro h
      have hExact : exactHEBool k u v = true :=
        ((finiteNumericHE_true_iff k N u v).1 h).2
      have hGen : generatedE k (j+1) 1 u :=
        (exactHEBool_at_real_iff k (j+1) 1 u (by omega)).1 hExact
      have hc : u < nonTopFreeCut k (j+1) 1 :=
        (generatedE_nonTop_iff k (j+1) 1 u
          (by omega) (by omega) hk).1 hGen
      simpa [c, nonTopFreeCut] using hc
    · intro hu
      have hc : u < nonTopFreeCut k (j+1) 1 := by
        simpa [c, nonTopFreeCut] using hu
      have hGen : generatedE k (j+1) 1 u :=
        (generatedE_nonTop_iff k (j+1) 1 u
          (by omega) (by omega) hk).2 hc
      exact (finiteNumericHE_true_iff k N u v).2
        ⟨hVertex,
          (exactHEBool_at_real_iff k (j+1) 1 u (by omega)).2 hGen⟩
  have hFreeCut : IsFreeCut A.E v c := by
    constructor
    · intro u hu
      exact (hColumn u).2 hu
    · cases h : A.E c v with
      | false => rfl
      | true =>
        have hc := (hColumn c).1 h
        omega
  have hCanonical : IsFreeCut A.E v (A.freeLevel v) :=
    canonicalFreeLevel_isFreeCut A.E A.spaced A.downward v
  exact freeCut_unique A.E v (A.freeLevel v) c hCanonical hFreeCut

/-- The next generation-one original is in the **eligible ambient
free-cut pool** at its predecessor's generation-zero cut. Whether
Algorithm 5.4 actually SELECTS this name is not determined by
free-cut eligibility. -/
theorem finiteNumericH_next_original_is_freeCut_eligible
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N j : Nat)
    (hk : 1 < k)
    (hVertex : hPosition k (j+1) 1 < N) :
    hPosition k j 0 + 1 ≤
      (finiteNumericH K k N).freeLevel (hPosition k (j+1) 1) := by
  rw [finiteNumericH_next_generation_one_freeLevel K k N j hk hVertex]


/-- The first reserved original need not be immediately before the
second in the original enumeration. For ANY two increasing original
block indices i<j, the generation-one copy of j has its free cut
strictly beyond the generation-zero copy of i. Thus no choice of
intervening unused original indices can exclude that upper name
by the ordinary E free-cut eligibility test alone. -/
theorem finiteNumericH_later_generation_one_is_freeCut_eligible
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N i j : Nat)
    (hk : 1 < k)
    (hij : i < j)
    (hVertex : hPosition k j 1 < N) :
    hPosition k i 0 + 1 ≤
      (finiteNumericH K k N).freeLevel (hPosition k j 1) := by
  have hPred : j - 1 + 1 = j := by omega
  have hNext :=
    finiteNumericH_next_generation_one_freeLevel
      K k N (j-1) hk (by simpa only [hPred] using hVertex)
  have hFree :
      (finiteNumericH K k N).freeLevel (hPosition k j 1) =
        hPosition k (j-1) 0 + 1 := by
    simpa only [hPred] using hNext
  rw [hFree]
  have hi : i ≤ j-1 := by omega
  have hPos : hPosition k i 0 ≤ hPosition k (j-1) 0 := by
    rcases lt_or_eq_of_le hi with hlt | heq
    · exact Nat.le_of_lt
        (hPosition_lt_of_block_lt k i (j-1) 0 0 (Nat.zero_le _) hlt)
    · exact le_of_eq (congrArg (fun t => hPosition k t 0) heq)
  omega

end Kk
