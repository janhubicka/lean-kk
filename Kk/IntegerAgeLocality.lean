import Kk.IntegerAgeSmallFunction
import Mathlib.Tactic

/-!
# Locality of canonical one-support graph-age restrictions

A common step in the KK-free paper replaces an age F by its largest
graph age below one extra bound on support S. It is not legitimate
to claim that every other support T is unchanged: the raw bound on S
can affect overlapping supports.

The precise sufficient condition is that every nonempty support
inside S ∩ T already has F-value at most the new bound n. We
prove that this condition preserves F(T), by zeroing a genuine
integer-clique witness outside T and checking the entire new raw
constraint. In particular, disjoint supports never interact.

This is a graph-age lemma, not a theorem about the complete
parameter-closed numerical-H B3 age test or a global envelope.
-/

namespace Kk

/-- Impose one additional raw upper bound on a support S. -/
def integerAgeLowerAt (d ell : Nat)
    (F : IntegerGraphSupport d ell → Nat)
    (S : IntegerGraphSupport d ell) (n : Nat) :
    IntegerGraphSupport d ell → Nat :=
  fun U => if U = S then min (F U) n else F U

theorem integerAgeLowerAt_le (d ell : Nat)
    (F : IntegerGraphSupport d ell → Nat)
    (S : IntegerGraphSupport d ell) (n : Nat) :
    AgeLe (integerAgeLowerAt d ell F S n) F := by
  intro U
  by_cases h : U = S
  · subst U
    simp [integerAgeLowerAt]
  · simp [integerAgeLowerAt, h]

/-- Lowering the bound on S does not alter the canonical age at T
when every nonempty subset of S∩T already has age at most n.
The case S∩T=∅ is included (the condition is then vacuous). -/
theorem integerGraphAgeCanonical_single_bound_locality
    (d ell : Nat) (hell : 0 < ell)
    (F : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell F)
    (S T : IntegerGraphSupport d ell) (n : Nat)
    (hOverlap : ∀ U : IntegerGraphSupport d ell,
      U.1 ⊆ S.1 → U.1 ⊆ T.1 → F U ≤ n) :
    integerGraphAgeCanonical d ell (integerAgeLowerAt d ell F S n) T =
      F T := by
  classical
  obtain ⟨w,hBounds,hValue⟩ := hAge.2 T
  let zero : Fin ell := ⟨0, hell⟩
  let wT : Fin d → Fin ell :=
    fun j => if j ∈ T.1 then w.1 j else zero
  have hTotalLe :
      Finset.univ.sum (fun j : Fin d => (wT j).val) ≤
        Finset.univ.sum (fun j : Fin d => (w.1 j).val) := by
    apply Finset.sum_le_sum
    intro j hj
    by_cases h : j ∈ T.1
    · simp [wT, h]
    · simp [wT, h, zero]
  let wn : IntegerCliqueWeights d ell :=
    ⟨wT, hTotalLe.trans w.2⟩
  have hSmall : ∀ U : IntegerGraphSupport d ell,
      integerCliqueOnSupport wn U ≤ integerCliqueOnSupport w U := by
    intro U
    unfold integerCliqueOnSupport
    apply Finset.sum_le_sum
    intro j hj
    by_cases h : j ∈ T.1
    · simp [wn, wT, h]
    · simp [wn, wT, h, zero]
  let Q : Finset (Fin d) := S.1 ∩ T.1
  have hQsum :
      Q.sum (fun j => (wT j).val) =
        S.1.sum (fun j => (wT j).val) := by
    apply Finset.sum_subset (Finset.inter_subset_left)
    intro j hjS hjNot
    have hjNotT : j ∉ T.1 := by
      intro hjT
      exact hjNot (Finset.mem_inter.mpr ⟨hjS, hjT⟩)
    simp [wT, hjNotT, zero]
  have hQvalue :
      Q.sum (fun j => (wT j).val) =
        Q.sum (fun j => (w.1 j).val) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjT : j ∈ T.1 := (Finset.mem_inter.mp hj).2
    simp [wT, hjT]
  have hSBound : integerCliqueOnSupport wn S ≤ n := by
    change S.1.sum (fun j => (wT j).val) ≤ n
    rw [← hQsum, hQvalue]
    by_cases hQ : Q.Nonempty
    · let U : IntegerGraphSupport d ell :=
        ⟨Q, ⟨hQ, (Finset.card_le_card
          (Finset.inter_subset_left)).trans S.2.2⟩⟩
      calc
        Q.sum (fun j => (w.1 j).val) =
            integerCliqueOnSupport w U := rfl
        _ ≤ F U := hBounds U
        _ ≤ n := hOverlap U
          (Finset.inter_subset_left) (Finset.inter_subset_right)
    · have hEmpty : Q = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hQ
      simp [hEmpty]
  have hFeasible :
      WitnessRespects
        (integerCliqueOnSupport (d := d) (ell := ell))
        (integerAgeLowerAt d ell F S n) wn := by
    intro U
    by_cases hUS : U = S
    · subst U
      have hF : integerCliqueOnSupport wn S ≤ F S :=
        (hSmall S).trans (hBounds S)
      change integerCliqueOnSupport wn S ≤ min (F S) n
      exact le_min hF hSBound
    · have hF : integerCliqueOnSupport wn U ≤ F U :=
        (hSmall U).trans (hBounds U)
      simpa [integerAgeLowerAt, hUS] using hF
  have hValueT : integerCliqueOnSupport wn T = F T := by
    calc
      integerCliqueOnSupport wn T =
          integerCliqueOnSupport w T := by
        unfold integerCliqueOnSupport
        apply Finset.sum_congr rfl
        intro j hj
        simp [wn, wT, hj]
      _ = F T := hValue
  apply Nat.le_antisymm
  · calc
      integerGraphAgeCanonical d ell
          (integerAgeLowerAt d ell F S n) T ≤
            integerAgeLowerAt d ell F S n T :=
          integerGraphAgeCanonical_le_raw d ell _ T
      _ ≤ F T := integerAgeLowerAt_le d ell F S n T
  · rw [←hValueT]
    exact witnessValue_le_canonical
      (integerCliqueOnSupport (d := d) (ell := ell))
      (integerAgeLowerAt d ell F S n) wn hFeasible T

/-- Disjoint supports are independent under any one-support raw
restriction, including a restriction whose numerical bound is zero. -/
theorem integerGraphAgeCanonical_single_bound_disjoint
    (d ell : Nat) (hell : 0 < ell)
    (F : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell F)
    (S T : IntegerGraphSupport d ell)
    (hDisj : Disjoint S.1 T.1) (n : Nat) :
    integerGraphAgeCanonical d ell (integerAgeLowerAt d ell F S n) T =
      F T := by
  apply integerGraphAgeCanonical_single_bound_locality
    d ell hell F hAge S T n
  intro U hUS hUT
  have hX : U.1 = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro j hj
    exact (Finset.disjoint_left.mp hDisj)
      (hUS hj) (hUT hj)
  exact False.elim (U.2.1.ne_empty hX)

end Kk
