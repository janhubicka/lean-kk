import Kk.ProtectedActivePivotCapacity
import Kk.PhysicalPointedContinuation
import Mathlib.Tactic

/-!
# Track B: actual finite Henson next stage with arbitrary protected gap bits

English-first proof and hostile audit:
docs/track_b_protected_active_pointed_english_audit.md.

Every old original below H remains the SAME graph vertex. In contrast to
the previous zero-gap construction, every protected nonpivot original
p in [b,H) now has the exact explicitly prescribed g(p,u) column toward
the NEW finite universal future. All new profiles, original edges and
numeric-H columns belong to ONE shared stage certificate and cutoff.

This preserves prescribed ordinary-L passing data, NOT old Kpt names,
auxiliary E histories or the full active-front diary source.
-/
namespace Kk

/-- One fixed genuine pivot and arbitrary protected nonzero gap columns
can be realized simultaneously in the fixed left-dense Henson original.
The complete new raw function is the exact protected-pivot capacity,
not a zero-gap approximation. All old originals are fixed as vertices. -/
theorem henson_leftDense_realizes_activeGap_pointed
    (E : Nat → Nat → Bool) (d e ell b v H k : Nat)
    (hell : 2 ≤ ell) (he : 0 < e)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool) (pi : Fin e → Fin d)
    (beta : Fin e → Bool) (gap : Nat → Fin e → Bool)
    (hbv : b ≤ v) (hvH : v < H) :
    let C := activeGapPointedColumn b v c pi beta gap
    let B := finiteOldColumnRawBound E ell e (Finset.range H) C
    let V := RelativeUniversalTaggedVertex e ell B
    let W := finiteTaggedFuturePool (V := V) H
    let tau := finiteTaggedFutureSort he
      (relativeUniversalTaggedSort e ell B) H
    B = protectedPivotRaw E ell v H
      (fun p u => if p < b then c p (pi u) else gap p u) beta ∧
    ∃ (f : Nat → Nat) (M : Nat),
      FiniteNumericStageWitness E e ell H k he C f M ∧
      (∀ p, p < H → f p = p) ∧
      (∀ p, p < b → ∀ w ∈ W,
        E p (f w) = c p (pi (tau w)) ∧
        E (f w) p = c p (pi (tau w))) ∧
      (∀ w ∈ W,
        E v (f w) = beta (tau w) ∧
        E (f w) v = beta (tau w)) ∧
      (∀ p, b ≤ p → p < H → p ≠ v → ∀ w ∈ W,
        E p (f w) = gap p (tau w) ∧
        E (f w) p = gap p (tau w)) := by
  classical
  let C := activeGapPointedColumn b v c pi beta gap
  let B := finiteOldColumnRawBound E ell e (Finset.range H) C
  let V := RelativeUniversalTaggedVertex e ell B
  let W := finiteTaggedFuturePool (V := V) H
  let tau : Nat → Fin e :=
    finiteTaggedFutureSort he (relativeUniversalTaggedSort e ell B) H
  have hRaw : B = protectedPivotRaw E ell v H
      (fun p u => if p < b then c p (pi u) else gap p u) beta :=
    activeGapPointedRaw_eq_actual E ell b v H hbv hvH c pi beta gap
  obtain ⟨f, M, hStage⟩ :=
    henson_leftDense_finite_numeric_stage_witness
      E e ell H k hell he hAvoid hDense C
  have hSym : ∀ p q, E p q = E q p :=
    hensonForbiddenFamily_symmetric ell hell E hAvoid
  have hActual := finiteNumericStageWitness_original_columns
    E e ell H k he C f M hSym hStage
  have hParts := hStage
  unfold FiniteNumericStageWitness at hParts
  rcases hParts with ⟨hFix, _hMono, _hGraph, _hGap, _hAfter,
      _hCut, _hCarrier1, _hCarrier2, _hCarrier3, _hProfile,
      _hColumns, _hZero, _hDummy⟩
  refine ⟨hRaw, f, M, hStage, hFix, ?_, ?_, ?_⟩
  · intro p hp w hw
    have hpH : p < H := by omega
    have h := hActual p hpH w hw
    have hOld := activeGapPointedColumn_old b v c pi beta gap p hp (tau w)
    exact ⟨h.1.trans hOld, h.2.trans hOld⟩
  · intro w hw
    have h := hActual v hvH w hw
    have hPivot := activeGapPointedColumn_pivot b v c pi beta gap hbv (tau w)
    exact ⟨h.1.trans hPivot, h.2.trans hPivot⟩
  · intro p hbp hpH hpv w hw
    have h := hActual p hpH w hw
    have hGap := activeGapPointedColumn_gap b v c pi beta gap p hbp hpv (tau w)
    exact ⟨h.1.trans hGap, h.2.trans hGap⟩

#print axioms Kk.henson_leftDense_realizes_activeGap_pointed
end Kk
