import Kk.ControlledPivotBudget
import Kk.PhysicalCanonicalSortTransport
import Kk.ProtectedActivePivotRealization
import Mathlib.Tactic

/-!
# Controlled coding at the same selected nonfree original

The English proof and independent adversarial review preceded this source:
`docs/track_b_nonfree_pivot_residual_english_audit_20261121.md`, Section 6.

The complete nonpivot original pool supplies the old age, and its pivot-sort
column describes the SAME actual original in both directions. The controlled
cap and growth conditions imply the full joint continuation budgets, including
the maximal-cardinality support case. No desired pivot budget is assumed.
Arbitrary parent maps retain every protected column, with repeated parents and
different passing bits permitted. The full finite Henson stage uses one f,M.

This does not construct controlled-pre-age normalization around a protected
pivot, transport dependent Kpt records, or construct an infinite diary.
-/

namespace Kk

/-- The second controlled-coding axiom suffices to preserve the entire
canonical survivor age at an actual nonfree pivot. Its full old type and
EVERY protected original column are retained. Positive children have parents
in X; zero children may even retain the pivot sort. -/
theorem protectedPivot_canonical_eq_of_controlled
    (E : Nat → Nat → Bool) (d e ell v H : Nat)
    (hell : 2 ≤ ell) (hvH : v < H)
    (c : Nat → Fin d → Bool) (s : Fin d)
    (hColumn : ∀ p ∈ (Finset.range H).erase v,
      E p v = c p s ∧ E v p = c p s)
    (F : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell F)
    (hOld : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d ((Finset.range H).erase v) c) = F)
    (X : Finset (Fin d))
    (hCap : ∀ U : IntegerGraphSupport d ell, U.1 ⊆ X → F U ≤ ell - 2)
    (hGrowth : ∀ U V : IntegerGraphSupport d ell,
      U.1 ⊆ X → V.1 = insert s U.1 → F V = F U + 1)
    (pi : Fin e → Fin d) (beta : Fin e → Bool)
    (hPositive : ∀ u, beta u = true → pi u ∈ X) :
    integerGraphAgeCanonical e ell
      (finiteOldColumnRawBound E ell e (Finset.range H)
        (protectedPivotColumn v (fun p u => c p (pi u)) beta)) =
      fun U => F (integerGraphSupportImage pi U) := by
  classical
  let P := (Finset.range H).erase v
  let a : Nat → Fin e → Bool := fun p u => c p (pi u)
  let B := finiteOldColumnRawBound E ell e P a
  let Bnew := finiteOldColumnRawBound E ell e (Finset.range H)
    (protectedPivotColumn v a beta)
  let F' := fun U : IntegerGraphSupport e ell => F (integerGraphSupportImage pi U)
  have hEll : 0 < ell := by omega
  have hBelow : AgeLe F (finiteOldColumnRawBound E ell d P c) := by
    rw [← hOld]
    exact integerGraphAgeCanonical_le_raw d ell _
  have hAge' : IsIntegerGraphAge e ell F' :=
    isIntegerGraphAge_pullback pi hEll F hAge
  have hBase : integerGraphAgeCanonical e ell B = F' := by
    funext U
    calc
      integerGraphAgeCanonical e ell B U =
          integerGraphAgeCanonical d ell
            (finiteOldColumnRawBound E ell d P c)
            (integerGraphSupportImage pi U) :=
        finiteOldColumnCanonical_reindex E P c pi hEll U
      _ = F' U := by rw [hOld]
  have hTarget : AgeLe F' (integerGraphAgeCanonical e ell Bnew) := by
    apply (protectedPivot_targetAge_le_canonical_iff_budgets
      E ell v H hvH a beta F' hAge').mpr
    intro U
    dsimp only
    rw [oldSupportCommonNeighbourPool_reindex]
    let T := integerGraphSupportImage pi U
    have hRaw := hBelow T
    have hPos : 1 ≤ F T := (hAge.1 T).1
    change F T ≤ ell - 1 - finiteDirectedCliqueCapacity E
      (oldSupportCommonNeighbourPool P c T.1) at hRaw
    constructor
    · change finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool P c T.1) + F T ≤ ell - 1
      omega
    · intro hAll
      have hTX : T.1 ⊆ X := by
        intro t ht
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
        exact hPositive u (hAll u hu)
      exact controlledPivot_linked_budget E d ell hell P c s v
        hColumn F hAge hBelow X hCap hGrowth T hTX
  have hNewBelow : AgeLe F' Bnew := by
    intro U
    exact (hTarget U).trans (integerGraphAgeCanonical_le_raw e ell Bnew U)
  have hNewLe : AgeLe Bnew B := by
    intro U
    change finiteOldColumnRawBound E ell e (Finset.range H)
        (protectedPivotColumn v a beta) U ≤
      ell - 1 - finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool P a U.1)
    rw [protectedPivotRaw_eq_actual E ell v H hvH a beta]
    unfold protectedPivotRaw
    split_ifs
    · have hMax := le_max_left
        (finiteDirectedCliqueCapacity E (oldSupportCommonNeighbourPool P a U.1))
        (1 + finiteDirectedCliqueCapacity E
          (mutualLinkedNeighbours E (oldSupportCommonNeighbourPool P a U.1) v))
      change ell - 1 - max
          (finiteDirectedCliqueCapacity E (oldSupportCommonNeighbourPool P a U.1))
          (1 + finiteDirectedCliqueCapacity E
            (mutualLinkedNeighbours E (oldSupportCommonNeighbourPool P a U.1) v)) ≤ _
      omega
    · exact le_rfl
  have hNewAge := integerGraphAgeCanonical_is_age e ell Bnew F' hAge' hNewBelow
  have hUpper : AgeLe (integerGraphAgeCanonical e ell Bnew) F' := by
    rw [← hBase]
    apply integerGraphAgeCanonical_greatest e ell B
      (integerGraphAgeCanonical e ell Bnew) hNewAge
    intro U
    exact (integerGraphAgeCanonical_le_raw e ell Bnew U).trans (hNewLe U)
  funext U
  exact Nat.le_antisymm (hUpper U) (hTarget U)

/-- A controlled event has a complete finite numerical Henson stage with
the same protected pivot. The actual canonical age equality, full stage,
fixed prefix and every positive/negative original column share one f and M.
There is no separately assumed mixed-support capacity budget. -/
theorem henson_leftDense_realizes_controlledPivot_stage
    (E : Nat → Nat → Bool) (d e ell v H k : Nat)
    (hell : 2 ≤ ell) (he : 0 < e) (hvH : v < H)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool) (s : Fin d)
    (hColumn : ∀ p ∈ (Finset.range H).erase v,
      E p v = c p s ∧ E v p = c p s)
    (F : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell F)
    (hOld : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d ((Finset.range H).erase v) c) = F)
    (X : Finset (Fin d))
    (hCap : ∀ U : IntegerGraphSupport d ell, U.1 ⊆ X → F U ≤ ell - 2)
    (hGrowth : ∀ U V : IntegerGraphSupport d ell,
      U.1 ⊆ X → V.1 = insert s U.1 → F V = F U + 1)
    (pi : Fin e → Fin d) (beta : Fin e → Bool)
    (hPositive : ∀ u, beta u = true → pi u ∈ X) :
    let C := protectedPivotColumn v (fun p u => c p (pi u)) beta
    let B := finiteOldColumnRawBound E ell e (Finset.range H) C
    let V := RelativeUniversalTaggedVertex e ell B
    let W := finiteTaggedFuturePool (V := V) H
    let tau := finiteTaggedFutureSort he (relativeUniversalTaggedSort e ell B) H
    integerGraphAgeCanonical e ell B =
        (fun U => F (integerGraphSupportImage pi U)) ∧
    ∃ (f : Nat → Nat) (M : Nat),
      FiniteNumericStageWitness E e ell H k he C f M ∧
      (∀ p, p < H → f p = p) ∧
      (∀ p ∈ (Finset.range H).erase v, ∀ w ∈ W,
        E p (f w) = c p (pi (tau w)) ∧
        E (f w) p = c p (pi (tau w))) ∧
      (∀ w ∈ W,
        E v (f w) = beta (tau w) ∧ E (f w) v = beta (tau w)) := by
  classical
  let C := protectedPivotColumn v (fun p u => c p (pi u)) beta
  let B := finiteOldColumnRawBound E ell e (Finset.range H) C
  let V := RelativeUniversalTaggedVertex e ell B
  let W := finiteTaggedFuturePool (V := V) H
  let tau := finiteTaggedFutureSort he (relativeUniversalTaggedSort e ell B) H
  have hCanonical := protectedPivot_canonical_eq_of_controlled
    E d e ell v H hell hvH c s hColumn F hAge hOld X hCap hGrowth pi beta hPositive
  obtain ⟨f, M, hStage⟩ := henson_leftDense_finite_numeric_stage_witness
    E e ell H k hell he hAvoid hDense C
  have hSym : ∀ p q, E p q = E q p :=
    hensonForbiddenFamily_symmetric ell hell E hAvoid
  have hActual := finiteNumericStageWitness_original_columns
    E e ell H k he C f M hSym hStage
  refine ⟨hCanonical, f, M, hStage, hStage.1, ?_, ?_⟩
  · intro p hp w hw
    have hpv : p ≠ v := (Finset.mem_erase.mp hp).1
    have hpH : p < H := Finset.mem_range.mp (Finset.mem_erase.mp hp).2
    have h := hActual p hpH w hw
    simpa only [C, protectedPivotColumn, if_neg hpv] using h
  · intro w hw
    have h := hActual v hvH w hw
    simpa only [C, protectedPivotColumn, if_pos rfl] using h

end Kk
