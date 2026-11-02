import Kk.IntegerWitnessCanonical
import Mathlib.Tactic

/-!
# Correspondence of unrestricted and bounded-total integer clique witnesses

The KK-free manuscript defines a graph-age function using an arbitrary
finite multiplicity vector on the full set of sorts. The checked Lean
canonicalizer uses total weight at most ell-1.

For a chosen nonempty support T, discard all weights outside T.
This preserves the sum on T, decreases every sum over an arbitrary U,
and reduces the total sum to at most the bound on T.

The formal result identifies the two graph-age predicates, without
assuming the equivalence as an external axiom. The canonicalizer
equality and geometric numerical-H realization are distinct targets.
-/

namespace Kk

/-- A full integer witness has no *total*-weight restriction. -/
abbrev RawIntegerCliqueWeights (d ell : Nat) := Fin d → Fin ell

/-- The ordinary multiplicity sum of an unrestricted witness on a support. -/
def rawIntegerCliqueOnSupport {d ell : Nat}
    (w : RawIntegerCliqueWeights d ell)
    (T : IntegerGraphSupport d ell) : Nat :=
  T.1.sum (fun j => (w j).val)

/-- The integer-witness graph-age predicate stated in the manuscript:
each value is witnessed by a full finite multiplicity vector obeying
all the support constraints, with no global total-weight bound. -/
def IsRawIntegerGraphAge (d ell : Nat)
    (F : IntegerGraphSupport d ell → Nat) : Prop :=
  (∀ T, 1 ≤ F T ∧ F T ≤ ell - 1) ∧
  (∀ T, ∃ w : RawIntegerCliqueWeights d ell,
    (∀ U, rawIntegerCliqueOnSupport w U ≤ F U) ∧
    rawIntegerCliqueOnSupport w T = F T)

/-- For one objective support T, every full witness can be normalized
to total size at most ell-1 without increasing any support sum or
changing the sum on T. The bound on the raw T-coordinate is explicit. -/
theorem normalize_raw_integer_clique_witness
    {d ell : Nat} (hell : 0 < ell)
    (B : IntegerGraphSupport d ell → Nat)
    (hCap : ∀ U, B U ≤ ell - 1)
    (w : RawIntegerCliqueWeights d ell)
    (hW : ∀ U, rawIntegerCliqueOnSupport w U ≤ B U)
    (T : IntegerGraphSupport d ell) :
    ∃ wn : IntegerCliqueWeights d ell,
      (∀ U, integerCliqueOnSupport wn U ≤ B U) ∧
      integerCliqueOnSupport wn T =
        rawIntegerCliqueOnSupport w T := by
  classical
  let zero : Fin ell := ⟨0, hell⟩
  let wT : Fin d → Fin ell :=
    fun j => if j ∈ T.1 then w j else zero
  have hTotal :
      Finset.univ.sum (fun j : Fin d => (wT j).val) =
        rawIntegerCliqueOnSupport w T := by
    have hSubset :
        T.1.sum (fun j => (wT j).val) =
          Finset.univ.sum (fun j : Fin d => (wT j).val) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      simp [wT, hj, zero]
    rw [← hSubset]
    unfold rawIntegerCliqueOnSupport
    apply Finset.sum_congr rfl
    intro j hj
    simp [wT, hj]
  have hTotalBound :
      Finset.univ.sum (fun j : Fin d => (wT j).val) ≤ ell - 1 := by
    rw [hTotal]
    exact (hW T).trans (hCap T)
  have hLess : ∀ U : IntegerGraphSupport d ell,
      U.1.sum (fun j => (wT j).val) ≤
        rawIntegerCliqueOnSupport w U := by
    intro U
    unfold rawIntegerCliqueOnSupport
    apply Finset.sum_le_sum
    intro j hj
    by_cases h : j ∈ T.1
    · simp [wT, h]
    · simp [wT, h, zero]
  refine ⟨⟨wT, hTotalBound⟩, ?_, ?_⟩
  · intro U
    exact (hLess U).trans (hW U)
  · change T.1.sum (fun j => (wT j).val) =
      T.1.sum (fun j => (w j).val)
    apply Finset.sum_congr rfl
    intro j hj
    simp [wT, hj]

/-- The paper's unrestricted and the formalized bounded-total
integer-witness definitions describe the identical graph-age class,
provided ell is positive (as it is for K_ell, ell >= 2). -/
theorem rawIntegerGraphAge_iff_normalized
    (d ell : Nat) (hell : 0 < ell)
    (F : IntegerGraphSupport d ell → Nat) :
    IsRawIntegerGraphAge d ell F ↔ IsIntegerGraphAge d ell F := by
  constructor
  · rintro ⟨hRange, hW⟩
    refine ⟨hRange, ?_⟩
    intro T
    obtain ⟨w, hBounds, hValue⟩ := hW T
    obtain ⟨wn, hNormBounds, hNormValue⟩ :=
      normalize_raw_integer_clique_witness
        hell F (fun U => (hRange U).2) w hBounds T
    exact ⟨wn, hNormBounds, hNormValue.trans hValue⟩
  · rintro ⟨hRange, hW⟩
    refine ⟨hRange, ?_⟩
    intro T
    obtain ⟨wn, hBounds, hValue⟩ := hW T
    refine ⟨wn.1, ?_, ?_⟩
    · intro U
      exact hBounds U
    · exact hValue

end Kk
