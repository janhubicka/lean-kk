import Kk.IntegerAgeLocality
import Kk.IntegerAgeUniversalProperties
import Mathlib.Tactic

/-!
# Additional support bounds depend only on the canonical age

English proof and independent audit preceded this module:
`docs/track_b_exact_free_split_restriction_english_audit.md`.

The proof identifies the complete feasible normalized-vector sets. It does
not require positivity of the raw bounds or their canonicalizations.
-/

namespace Kk

/-- Imposing a bound at one support depends only on the canonical age of
the old complete constraint system. This also covers a vanishing branch. -/
theorem integerGraphAgeCanonical_lowerAt_canonical
    (d ell : Nat) (B : IntegerGraphSupport d ell → Nat)
    (S : IntegerGraphSupport d ell) (n : Nat) :
    integerGraphAgeCanonical d ell (integerAgeLowerAt d ell B S n) =
      integerGraphAgeCanonical d ell
        (integerAgeLowerAt d ell (integerGraphAgeCanonical d ell B) S n) := by
  classical
  let value := integerCliqueOnSupport (d := d) (ell := ell)
  have hRestrict (A : IntegerGraphSupport d ell → Nat)
      (w : IntegerCliqueWeights d ell) :
      WitnessRespects value (integerAgeLowerAt d ell A S n) w ↔
        WitnessRespects value A w ∧ value w S ≤ n := by
    constructor
    · intro hw
      refine ⟨?_, ?_⟩
      · intro U
        exact (hw U).trans (integerAgeLowerAt_le d ell A S n U)
      · have h : value w S ≤ min (A S) n := by
          simpa [integerAgeLowerAt] using hw S
        exact h.trans (min_le_right _ _)
    · rintro ⟨hA, hS⟩ U
      by_cases hUS : U = S
      · subst U
        simpa [integerAgeLowerAt] using le_min (hA S) hS
      · simpa only [integerAgeLowerAt, if_neg hUS] using hA U
  have hFeasible (w : IntegerCliqueWeights d ell) :
      WitnessRespects value (integerAgeLowerAt d ell B S n) w ↔
      WitnessRespects value
        (integerAgeLowerAt d ell (integerGraphAgeCanonical d ell B) S n) w := by
    rw [hRestrict B w, hRestrict (integerGraphAgeCanonical d ell B) w]
    exact and_congr
      (integerGraphAgeCanonical_preserves_clique_vectors d ell B w).symm Iff.rfl
  have hSet :
      Finset.univ.filter (WitnessRespects value (integerAgeLowerAt d ell B S n)) =
      Finset.univ.filter (WitnessRespects value
        (integerAgeLowerAt d ell (integerGraphAgeCanonical d ell B) S n)) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hFeasible w
  funext U
  change (Finset.univ.filter
      (WitnessRespects value (integerAgeLowerAt d ell B S n))).sup
      (fun w => value w U) = _
  rw [hSet]
  rfl

end Kk
