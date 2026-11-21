import Kk.SupportBlockGapAge
import Kk.HensonLeftDensityAge
import Kk.IntegerAgeSmallFunction
import Mathlib.Tactic

/-!
# Finite exact normalization of complete original-column ages

English proof and independent adversarial audits preceded this source in
`docs/track_b_finite_normalization_late_pivot_english_audit_20261121.md`.

Every genuine target age below the complete old raw bound can be realized
EXACTLY AS A RAW BOUND after finitely many actual isolated support cliques.
All columns on the entire initial prefix are retained. The pivot may remain
a symbolic sort during this preparation. New gap columns are zero.

This does not assert that the intermediate drops form a prescribed saturated
cover chain, or establish full dependent Kpt/B3 history or an infinite diary.
-/

namespace Kk

private theorem targetNormalization_clique_capacity
    (E : Nat → Nat → Bool) (Q : Finset Nat)
    (hClique : IsDirectedCliqueOn E Q) :
    finiteDirectedCliqueCapacity E Q = Q.card := by
  have hLower := directedClique_card_le_capacity E Q Q
    (Finset.Subset.refl Q) hClique
  obtain ⟨S, hSQ, _, hCard⟩ := finiteDirectedCliqueCapacity_attained E Q
  have hUpper := Finset.card_le_card hSQ
  omega

/-- One actual isolated support block attains the target value at T, keeps
the entire target below the raw age, and preserves every old original column.
It may also lower proper sub-supports of T; monotonicity of the target proves
that these side effects are safe. No cover hypothesis is needed. -/
theorem henson_leftDense_cap_finite_target_support
    (E : Nat → Nat → Bool) (d ell b : Nat) (hell : 2 ≤ ell)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool)
    (C : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell C)
    (hBelow : AgeLe C (finiteOldColumnRawBound E ell d (Finset.range b) c))
    (T : IntegerGraphSupport d ell) :
    ∃ (F : Nat) (c' : Nat → Fin d → Bool),
      b ≤ F ∧
      (∀ p, p < b → ∀ t, c' p t = c p t) ∧
      AgeLe C (finiteOldColumnRawBound E ell d (Finset.range F) c') ∧
      finiteOldColumnRawBound E ell d (Finset.range F) c' T = C T ∧
      AgeLe (finiteOldColumnRawBound E ell d (Finset.range F) c')
        (finiteOldColumnRawBound E ell d (Finset.range b) c) := by
  classical
  let r := ell - 1 - C T
  have hPositive := (hAge.1 T).1
  have hBound := (hAge.1 T).2
  have hr : r < ell := by dsimp [r]; omega
  obtain ⟨Q, hCard, hAfter, hClique, hIso⟩ :=
    henson_leftDense_exists_reserved_originals ell hell E hAvoid hDense b r hr
  let F := max b (Q.sup (fun q : Nat => q) + 1)
  let c' := supportBlockGappedColumn b Q T.1 c
  have hBF : b ≤ F := le_max_left _ _
  have hWithin : ∀ q ∈ Q, b ≤ q ∧ q < F := by
    intro q hq
    have hSup := Finset.le_sup (f := fun q : Nat => q) hq
    exact ⟨hAfter q hq, lt_of_lt_of_le (Nat.lt_succ_of_le hSup) (le_max_right _ _)⟩
  have hDisjoint : Disjoint (Finset.range b) Q := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hpLt := Finset.mem_range.mp hp
    have hpGe := hAfter p hq
    omega
  have hZero : ∀ p ∈ Finset.range b, ∀ q ∈ Q, E p q = false := by
    intro p hp q hq
    have hpLt := Finset.mem_range.mp hp
    have hpq : p < q := lt_of_lt_of_le hpLt (hAfter q hq)
    have hpNot : p ∉ Q := by
      intro hpQ
      exact Finset.disjoint_left.mp hDisjoint hp hpQ
    exact (hIso q hq p hpq hpNot).1
  have hCapacity : finiteDirectedCliqueCapacity E Q = r :=
    (targetNormalization_clique_capacity E Q hClique).trans hCard
  have hUpdate (U : IntegerGraphSupport d ell) :
      finiteOldColumnRawBound E ell d (Finset.range F) c' U =
        if U.1 ⊆ T.1 then
          min (finiteOldColumnRawBound E ell d (Finset.range b) c U) (C T)
        else finiteOldColumnRawBound E ell d (Finset.range b) c U := by
    change finiteOldColumnRawBound E ell d (Finset.range F)
      (supportBlockGappedColumn b Q T.1 c) U = _
    rw [supportBlockGappedRawBound_eq E ell d b F hBF Q hWithin T c]
    rw [supportBlockRawBound_exact E ell d (Finset.range b) Q hDisjoint hZero c T U]
    rw [hCapacity]
    unfold finiteOldColumnRawBound
    dsimp [r]
    split_ifs <;> omega
  refine ⟨F, c', hBF, ?_, ?_, ?_, ?_⟩
  · intro p hp t
    have hpNot : p ∉ Q := by
      intro hpQ
      have := hAfter p hpQ
      omega
    simp [c', supportBlockGappedColumn, supportBlockOldColumn,
      delayedOldColumn, hpNot, hp]
  · intro U
    rw [hUpdate]
    split_ifs with hUT
    · exact le_min (hBelow U) (integerGraphAge_monotone d ell C hAge U T hUT)
    · exact hBelow U
  · rw [hUpdate]
    simp only [Finset.Subset.refl, if_true]
    exact min_eq_right (hBelow T)
  · intro U
    rw [hUpdate]
    split_ifs
    · exact min_le_left _ _
    · exact le_rfl

/-- Process any finite family of target supports. Previously attained values
cannot be lost: the raw bound only decreases and always stays above C.
The construction fixes the entire original prefix and all its columns. -/
theorem henson_leftDense_normalizes_finite_supports
    (E : Nat → Nat → Bool) (d ell : Nat) (hell : 2 ≤ ell)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (C : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell C)
    (A : Finset (IntegerGraphSupport d ell))
    (b : Nat) (c : Nat → Fin d → Bool)
    (hBelow : AgeLe C (finiteOldColumnRawBound E ell d (Finset.range b) c)) :
    ∃ (F : Nat) (c' : Nat → Fin d → Bool),
      b ≤ F ∧
      (∀ p, p < b → ∀ t, c' p t = c p t) ∧
      AgeLe C (finiteOldColumnRawBound E ell d (Finset.range F) c') ∧
      (∀ U ∈ A, finiteOldColumnRawBound E ell d (Finset.range F) c' U = C U) ∧
      AgeLe (finiteOldColumnRawBound E ell d (Finset.range F) c')
        (finiteOldColumnRawBound E ell d (Finset.range b) c) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      exact ⟨b, c, le_rfl, (by intros; rfl), hBelow,
        (by simp), (by intro U; exact le_rfl)⟩
  | @insert T A hNot ih =>
      obtain ⟨F, c', hBF, hOld, hTarget, hDone, hLower⟩ := ih
      obtain ⟨G, c'', hFG, hOld', hTarget', hT, hLower'⟩ :=
        henson_leftDense_cap_finite_target_support
          E d ell F hell hAvoid hDense c' C hAge hTarget T
      refine ⟨G, c'', hBF.trans hFG, ?_, hTarget', ?_, ?_⟩
      · intro p hp t
        exact (hOld' p (lt_of_lt_of_le hp hBF) t).trans (hOld p hp t)
      · intro U hU
        rcases Finset.mem_insert.mp hU with hEq | hMem
        · subst U
          exact hT
        · apply Nat.le_antisymm
          · exact (hLower' U).trans_eq (hDone U hMem)
          · exact hTarget' U
      · intro U
        exact (hLower' U).trans (hLower U)

/-- Any genuine finite target below the complete old raw bound is realized
as the EXACT complete raw and canonical age after finite preparation in the
same fixed Henson graph. All previously committed originals and columns are
retained. Empty sort sets are allowed. No prescribed cover order is claimed. -/
theorem henson_leftDense_normalizes_finite_target_age
    (E : Nat → Nat → Bool) (d ell b : Nat) (hell : 2 ≤ ell)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool)
    (C : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell C)
    (hBelow : AgeLe C (finiteOldColumnRawBound E ell d (Finset.range b) c)) :
    ∃ (F : Nat) (c' : Nat → Fin d → Bool),
      b ≤ F ∧
      (∀ p, p < b → ∀ t, c' p t = c p t) ∧
      finiteOldColumnRawBound E ell d (Finset.range F) c' = C ∧
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range F) c') = C := by
  classical
  obtain ⟨F, c', hBF, hOld, _, hAll, _⟩ :=
    henson_leftDense_normalizes_finite_supports E d ell hell hAvoid hDense
      C hAge Finset.univ b c hBelow
  have hRaw : finiteOldColumnRawBound E ell d (Finset.range F) c' = C := by
    funext U
    exact hAll U (Finset.mem_univ U)
  refine ⟨F, c', hBF, hOld, hRaw, ?_⟩
  rw [hRaw]
  funext U
  exact Nat.le_antisymm (integerGraphAgeCanonical_le_raw d ell C U)
    (integerGraphAgeCanonical_greatest d ell C C hAge (fun _ => le_rfl) U)

end Kk
