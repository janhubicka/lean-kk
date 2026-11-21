import Kk.TwoPhysicalCanonicalCovers
import Mathlib.Tactic

/-!
# Track B: any supplied finite chain of actual Henson canonical-age covers

English proof and adversarial audit were committed FIRST in
\`docs/track_b_finite_cover_sequence_english_audit_20261121.md\`.

Each step uses the previously kernel-verified complete-prefix physical
cover theorem. The prior-age premise for the next step is DERIVED from
the previous stage, and every original column below the *initial*
cutoff is preserved. This handles arbitrarily many finite covers in one
unchanged Henson original graph; it does NOT retain previous tagged top
future witnesses, give one global numerical-H embedding, or prove the
parameter-closed Kpt diary / BRDs.
-/

namespace Kk

/-- Given an explicit finite chain of genuine normalized graph-age covers,
construct the terminal age in the same actual Henson original enumeration.

Each transition is implemented by a real isolated reserved original clique
and a full literal gap-inclusive column. Earlier complete original columns
are untouched. The induction does not pretend the separate finite tagged
top-front witnesses from successive stages form one coherent copy. -/
theorem henson_leftDense_realizes_finite_physical_cover_chain
    (d ell b steps : Nat) (hell : 2 ≤ ell) (hd : 0 < d)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool)
    (ages : Nat → IntegerGraphSupport d ell → Nat)
    (supports : Nat → IntegerGraphSupport d ell)
    (blockSizes generations : Nat → Nat)
    (hCover : ∀ i, i < steps →
      AgeCover (IsIntegerGraphAge d ell) (ages (i + 1)) (ages i))
    (hEll : ∀ i, i < steps →
      ell = ages (i + 1) (supports i) + blockSizes i + 1)
    (hStep : ∀ i, i < steps →
      ages i (supports i) = ages (i + 1) (supports i) + 1)
    (hPrior : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) = ages 0) :
    ∃ (F : Nat) (cFinal : Nat → Fin d → Bool),
      b ≤ F ∧
      (∀ p, p < b → ∀ t, cFinal p t = c p t) ∧
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range F) cFinal) =
          ages steps := by
  classical
  have hAux : ∀ (n i b' : Nat) (c' : Nat → Fin d → Bool),
      i + n ≤ steps →
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range b') c') = ages i →
      ∃ (F : Nat) (cFinal : Nat → Fin d → Bool),
        b' ≤ F ∧
        (∀ p, p < b' → ∀ t, cFinal p t = c' p t) ∧
        integerGraphAgeCanonical d ell
          (finiteOldColumnRawBound E ell d (Finset.range F) cFinal) =
            ages (i + n) := by
    intro n
    induction n with
    | zero =>
        intro i b' c' _ hCurrent
        refine ⟨b', c', le_refl _, ?_, ?_⟩
        · intro p hp t
          rfl
        · simpa using hCurrent
    | succ n ih =>
        intro i b' c' hBound hCurrent
        have hi : i < steps := by omega
        have hLater : (i + 1) + n ≤ steps := by omega
        have hUpper : ages i (supports i) ≤ ell - 1 :=
          ((hCover i hi).upper_age.1 (supports i)).2
        have hBlockPos : 0 < blockSizes i := by
          have hEllI := hEll i hi
          have hStepI := hStep i hi
          omega
        obtain ⟨Q, F0, hCard, hWithin, _hClique, _hIso,
          hAge, _hFeasible, _hStage⟩ :=
          henson_leftDense_exists_physical_finite_canonical_cover_stage
            d ell b' (generations i) (blockSizes i) hell hd E
            hAvoid hDense c' (supports i)
            (ages (i + 1)) (ages i)
            (hCover i hi) (hEll i hi) (hStep i hi) hCurrent
        have hCardPos : 0 < Q.card := by omega
        obtain ⟨q, hq⟩ := Finset.card_pos.mp hCardPos
        have hBF : b' ≤ F0 :=
          (hWithin q hq).1.trans (Nat.le_of_lt (hWithin q hq).2)
        let c1 : Nat → Fin d → Bool :=
          supportBlockGappedColumn b' Q (supports i).1 c'
        obtain ⟨F, cFinal, hF0F, hKeep, hResult⟩ :=
          ih (i + 1) F0 c1 hLater (by simpa [c1] using hAge)
        refine ⟨F, cFinal, hBF.trans hF0F, ?_, ?_⟩
        · intro p hp t
          calc
            cFinal p t = c1 p t :=
              hKeep p (lt_of_lt_of_le hp hBF) t
            _ = c' p t := by
              have hpNotQ : p ∉ Q := by
                intro hpQ
                have hAfter := (hWithin p hpQ).1
                omega
              simp [c1, supportBlockGappedColumn,
                supportBlockOldColumn, delayedOldColumn, hpNotQ, hp]
        · have hIdx : (i + 1) + n = i + (n + 1) := by omega
          simpa only [Nat.succ_eq_add_one, hIdx] using hResult
  obtain ⟨F, cFinal, hBF, hKeep, hResult⟩ :=
    hAux steps 0 b c (by omega) hPrior
  refine ⟨F, cFinal, hBF, hKeep, ?_⟩
  simpa using hResult

#print axioms Kk.henson_leftDense_realizes_finite_physical_cover_chain

end Kk
