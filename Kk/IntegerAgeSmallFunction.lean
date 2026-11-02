import Kk.RawWitnessNormalization
import Mathlib.Tactic

/-!
# Monotonicity and the small-function identity for integer graph ages

The KK-free manuscript's black graph-age foundation includes:
* F(S) <= F(T) whenever S is a nonempty support contained in T;
* if F(S)<|S| for a nonempty S⊆T, then F(T) equals the
  maximum value on nonempty proper supports of T.

The paper's displayed small-function statement omits the
qualification that S and the supports inside its maximum lie
in the nonempty domain X_{D,ell}. We do NOT edit that black
prose; we formalize the domain-correct version here.

The proof uses the actual raw integer-witness definition through the
verified equivalence with the total-bounded witness predicate.
No extra mathematical axiom or numerical-H/diary claim is introduced.
-/

namespace Kk

/-- Every normalized integer graph-age function is monotone on its
(nonempty) support domain. -/
theorem integerGraphAge_monotone
    (d ell : Nat)
    (F : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell F)
    (S T : IntegerGraphSupport d ell)
    (hST : S.1 ⊆ T.1) :
    F S ≤ F T := by
  obtain ⟨w,hBounds,hVal⟩ := hAge.2 S
  rw [← hVal]
  calc
    integerCliqueOnSupport w S ≤ integerCliqueOnSupport w T := by
      unfold integerCliqueOnSupport
      apply Finset.sum_le_sum_of_subset_of_nonneg hST
      intro j _ _
      exact Nat.zero_le _
    _ ≤ F T := hBounds T

/-- The same monotonicity assertion for the manuscript's *unrestricted*
integer-witness graph-age definition. -/
theorem rawIntegerGraphAge_monotone
    (d ell : Nat) (hell : 0 < ell)
    (F : IntegerGraphSupport d ell → Nat)
    (hAge : IsRawIntegerGraphAge d ell F)
    (S T : IntegerGraphSupport d ell)
    (hST : S.1 ⊆ T.1) :
    F S ≤ F T :=
  integerGraphAge_monotone d ell F
    ((rawIntegerGraphAge_iff_normalized d ell hell F).mp hAge)
    S T hST

/-- An age that is too small on a nonempty support S cannot
have a saturating T-witness positive on all coordinates of S.
The remaining positive coordinates therefore form a nonempty
proper support U of T on which the age still has value F(T). -/
theorem integerGraphAge_small_support_witness
    (d ell : Nat)
    (F : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell F)
    (S T : IntegerGraphSupport d ell)
    (hST : S.1 ⊆ T.1)
    (hSmall : F S < S.1.card) :
    ∃ U : IntegerGraphSupport d ell,
      U.1 ⊆ T.1 ∧ U.1 ≠ T.1 ∧ F U = F T := by
  classical
  obtain ⟨w,hBounds,hVal⟩ := hAge.2 T
  let Q : Finset (Fin d) := T.1.filter (fun j => 0 < (w.1 j).val)
  have hQT : Q ⊆ T.1 := Finset.filter_subset _ _
  have hQneq : Q ≠ T.1 := by
    intro hEq
    have hSQ : S.1 ⊆ Q := by
      simpa [hEq] using hST
    have hSCardBound : S.1.card ≤ F S := by
      calc
        S.1.card = S.1.sum (fun _ => (1 : Nat)) := by simp
        _ ≤ S.1.sum (fun j => (w.1 j).val) := by
          apply Finset.sum_le_sum
          intro j hj
          have hjQ : j ∈ Q := hSQ hj
          have hjPos : 0 < (w.1 j).val :=
            (Finset.mem_filter.mp hjQ).2
          omega
        _ = integerCliqueOnSupport w S := rfl
        _ ≤ F S := hBounds S
    omega
  have hQNonempty : Q.Nonempty := by
    by_contra hEmpty
    have hQEmpty : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hEmpty
    have hZero : T.1.sum (fun j => (w.1 j).val) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hjNot : j ∉ Q := by rw [hQEmpty]; simp
      have hjNotPos : ¬ 0 < (w.1 j).val := by
        intro hjPos
        exact hjNot (Finset.mem_filter.mpr ⟨hj,hjPos⟩)
      omega
    have hPositive : 1 ≤ F T := (hAge.1 T).1
    change T.1.sum (fun j => (w.1 j).val) = F T at hVal
    omega
  let U : IntegerGraphSupport d ell :=
    ⟨Q, ⟨hQNonempty, (Finset.card_le_card hQT).trans T.2.2⟩⟩
  have hQSum :
      Q.sum (fun j => (w.1 j).val) =
        T.1.sum (fun j => (w.1 j).val) := by
    apply Finset.sum_subset hQT
    intro j hj hjNot
    have hjNotPos : ¬ 0 < (w.1 j).val := by
      intro hjPos
      exact hjNot (Finset.mem_filter.mpr ⟨hj,hjPos⟩)
    omega
  have hU : F U = F T := by
    apply Nat.le_antisymm
    · exact integerGraphAge_monotone d ell F hAge U T hQT
    · calc
        F T = integerCliqueOnSupport w T := hVal.symm
        _ = integerCliqueOnSupport w U := by
          change T.1.sum (fun j => (w.1 j).val) =
            Q.sum (fun j => (w.1 j).val)
          exact hQSum.symm
        _ ≤ F U := hBounds U
  exact ⟨U, hQT, hQneq, hU⟩

/-- Exact domain-safe version of the manuscript's small-function lemma,
including the maximum over *nonempty* proper supports of T. -/
theorem integerGraphAge_small_function
    (d ell : Nat)
    (F : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell F)
    (S T : IntegerGraphSupport d ell)
    (hST : S.1 ⊆ T.1)
    (hSmall : F S < S.1.card) :
    F T =
      (Finset.univ.filter (fun U : IntegerGraphSupport d ell =>
        U.1 ⊆ T.1 ∧ U.1 ≠ T.1)).sup F := by
  classical
  obtain ⟨U,hUT,hUne,hEq⟩ :=
    integerGraphAge_small_support_witness d ell F hAge S T hST hSmall
  let candidates : Finset (IntegerGraphSupport d ell) :=
    Finset.univ.filter (fun V => V.1 ⊆ T.1 ∧ V.1 ≠ T.1)
  have hUmem : U ∈ candidates := by
    simp [candidates, hUT, hUne]
  have hUpper : candidates.sup F ≤ F T := by
    apply Finset.sup_le
    intro V hV
    have hVT : V.1 ⊆ T.1 :=
      (Finset.mem_filter.mp hV).2.1
    exact integerGraphAge_monotone d ell F hAge V T hVT
  have hLower : F T ≤ candidates.sup F := by
    rw [←hEq]
    exact Finset.le_sup (f := fun V : IntegerGraphSupport d ell => F V) hUmem
  exact Nat.le_antisymm hLower hUpper

/-- Full small-function identity for unrestricted raw witnesses as
used in Definition Graph_Age_Function. -/
theorem rawIntegerGraphAge_small_function
    (d ell : Nat) (hell : 0 < ell)
    (F : IntegerGraphSupport d ell → Nat)
    (hAge : IsRawIntegerGraphAge d ell F)
    (S T : IntegerGraphSupport d ell)
    (hST : S.1 ⊆ T.1)
    (hSmall : F S < S.1.card) :
    F T =
      (Finset.univ.filter (fun U : IntegerGraphSupport d ell =>
        U.1 ⊆ T.1 ∧ U.1 ≠ T.1)).sup F :=
  integerGraphAge_small_function d ell F
    ((rawIntegerGraphAge_iff_normalized d ell hell F).mp hAge)
    S T hST hSmall

end Kk
