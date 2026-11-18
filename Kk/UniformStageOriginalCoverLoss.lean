import Kk.PhysicalCoverStrictCanonicalLoss
import Kk.PhysicalIsolatedSupportStage
import Kk.FiniteUniformNumericTopAge
import Mathlib.Tactic

/-!
# Track B: finite numerical-H top-stage witnesses have genuine original E links

English proof and twelve hostile checks were committed FIRST in
docs/track_b_uniform_stage_selected_original_loss_english_audit.md.

The one SAME f,M supplied by HasUniformPositiveSupportStage specifies
all actual reserved-to-selected numerical-H L columns at ALL generations.
The previously checked top-to-top exact-original-edge theorem converts
these columns into genuine, both-directed ORIGINAL E edges: for every
reserved q and every finite selected witness w, E(q,f(w)) and
E(f(w),q) both equal decide(tau(w) belongs to T).

Consequently, if a COMPLETE FUTURE continuation column is additionally
chosen to remain T-positive at such a selected physical original
v=f(w), the previously verified source-exact strict canonical-loss
theorem applies WITHOUT an independent original-E linkage premise.
Existence of that next full continuation column with its desired
diary/sort history is NOT proved. No unbounded resolved embedding,
dependent Kpt B3 source, inverse monoid orbit or exact BRD claimed.
-/

namespace Kk

/-- Unpack ONE actual finite Henson/numerical-H uniform positive stage.
For all selected tagged future vertices w and all reserved originals
q, the complete original E column in BOTH directions equals the
actual future sort membership predicate tau(w) ∈ T.

The same physical f,M witness ALL these equations; no artificial
second embedding, selected-only macrofront, or source-index renaming. -/
theorem uniform_positive_stage_reserved_original_E_column
    (E : Nat → Nat → Bool)
    (hSym : ∀ x y, E x y = E y x)
    (d ell b F k : Nat) (hd : 0 < d)
    (c : Nat → Fin d → Bool)
    (Q : Finset Nat) (T : IntegerGraphSupport d ell)
    (hWithin : ∀ q ∈ Q, b ≤ q ∧ q < F)
    (hStage : HasUniformPositiveSupportStage
      E d ell b F k hd c Q T) :
    let B := finiteOldColumnRawBound E ell d
      (Finset.range b ∪ Q) (supportBlockOldColumn Q T.1 c)
    let V := RelativeUniversalTaggedVertex d ell B
    let W : Finset Nat := finiteTaggedFuturePool (V := V) F
    let tau := finiteTaggedFutureSort hd
      (relativeUniversalTaggedSort d ell B) F
    ∃ (f : Nat → Nat) (M : Nat),
      (∀ w ∈ W, F ≤ f w) ∧
      (∀ q ∈ Q, ∀ w ∈ W,
        E q (f w) = decide (tau w ∈ T.1) ∧
        E (f w) q = decide (tau w ∈ T.1)) := by
  classical
  unfold HasUniformPositiveSupportStage at hStage
  obtain ⟨f, M, _hFix, _hMono, _hGraph, hAfter, _hCut,
      _hProfile, _hOldCol, hReservedCol, _hGapCol,
      _hGapNumeric, _hDummy⟩ := hStage
  refine ⟨f, M, hAfter, ?_⟩
  intro q hq w hw
  have hqBefore : q < F := (hWithin q hq).2
  have hfwAfter : F ≤ f w := hAfter w hw
  have hDifferent : q ≠ f w := by omega
  have hTopEdge :=
    finiteNumericH_top_exact_original_edge
      E hSym k M q (f w) hDifferent
  have hNumeric := (hReservedCol q hq w hw k le_rfl).1
  have hForward : E q (f w) = decide (tau w ∈ T.1) :=
    hTopEdge.symm.trans hNumeric
  exact ⟨hForward, (hSym (f w) q).trans hForward⟩

/-- A FIRST physically realized canonical cover gives one finite
uniform selected top-stage f. Every selected top witness of a
sort tau(w) ∈ T ALREADY has genuine both-directed E links to the
whole reserved cover clique Q. Therefore any subsequently chosen
COMPLETE typed continuation column with positive future T bits
at that selected real original forces a strict CANONICAL age loss
at T over its ENTIRE actual original prefix [0,f(w)+1).

The full continuation column and its T-positivity remain EXPLICIT
premises. The finite stage only controls PAST-to-selected columns,
not the selected witness's own passing bits to future sorts. -/
theorem uniform_positive_stage_selected_full_T_successor_canonical_drop
    (E : Nat → Nat → Bool)
    (hSym : ∀ x y, E x y = E y x)
    (ell d b F k r : Nat) (hd : 0 < d)
    (c : Nat → Fin d → Bool)
    (Q : Finset Nat) (T : IntegerGraphSupport d ell)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hBF : b ≤ F)
    (hWithin : ∀ q ∈ Q, b ≤ q ∧ q < F)
    (hClique : IsDirectedCliqueOn E Q)
    (hCard : Q.card = r)
    (hIso : ∀ p, p < b → ∀ q ∈ Q,
      E p q = false ∧ E q p = false)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (hEll : ell = lower T + r + 1)
    (hAt : upper T = lower T + 1)
    (hPrior : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) = upper)
    (hStage : HasUniformPositiveSupportStage
      E d ell b F k hd c Q T) :
    let B := finiteOldColumnRawBound E ell d
      (Finset.range b ∪ Q) (supportBlockOldColumn Q T.1 c)
    let V := RelativeUniversalTaggedVertex d ell B
    let W : Finset Nat := finiteTaggedFuturePool (V := V) F
    let tau := finiteTaggedFutureSort hd
      (relativeUniversalTaggedSort d ell B) F
    ∃ (f : Nat → Nat) (M : Nat),
      (∀ w ∈ W, F ≤ f w) ∧
      (∀ w ∈ W, tau w ∈ T.1 →
        ∀ (cNext : Nat → Fin d → Bool),
          (∀ p, p < F → ∀ t,
            cNext p t = supportBlockGappedColumn b Q T.1 c p t) →
          (∀ t ∈ T.1, cNext (f w) t = true) →
          integerGraphAgeCanonical d ell
            (finiteOldColumnRawBound E ell d
              (Finset.range (f w + 1)) cNext) T <
          integerGraphAgeCanonical d ell
            (finiteOldColumnRawBound E ell d
              (Finset.range F) cNext) T) := by
  classical
  obtain ⟨f, M, hAfter, hColumn⟩ :=
    uniform_positive_stage_reserved_original_E_column
      E hSym d ell b F k hd c Q T hWithin hStage
  refine ⟨f, M, hAfter, ?_⟩
  intro w hw hwSort cNext hPrefix hPos
  have hLinks : ∀ q ∈ Q,
      E q (f w) = true ∧ E (f w) q = true := by
    intro q hq
    have hColumnBits := hColumn q hq w hw
    have hDec : decide (tau w ∈ T.1) = true := by
      simp [hwSort]
    exact ⟨hColumnBits.1.trans hDec, hColumnBits.2.trans hDec⟩
  exact (real_cover_later_full_link_forces_strict_canonical_T_drop
    E ell d b F r c cNext T Q lower upper
    hBF hWithin hClique hCard hIso hCover hEll hAt hPrior
    (f w) (hAfter w hw) hPrefix hPos hLinks).1

#print axioms Kk.uniform_positive_stage_reserved_original_E_column
#print axioms Kk.uniform_positive_stage_selected_full_T_successor_canonical_drop

end Kk
