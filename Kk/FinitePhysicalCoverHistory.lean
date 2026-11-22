import Kk.FinitePhysicalCoverChain
import Mathlib.Tactic

/-!
# Track B: a genuinely chronological finite physical cover history

English-first proof and twenty hostile checks:
  docs/audits/2026-11-22-adversarial-finite-history-main.md

A supplied finite sequence of ordinary-L canonical age covers can be realized
as a chain of REAL old-original Henson stages. Unlike the earlier
terminal-age-only theorem, the inductive certificate records EACH physical
reserved clique, cutoff, complete gapped typed column, actual stage canonical
age, and independently obtained finite numerical-H top witness.

This does NOT identify those separate top witnesses across stages, prove the
parameter-closed Kpt/I1/I2/I3/B3 history, or construct a resolved infinite
copy/BRD structure.
-/

namespace Kk

/-- One full chronological list of physical original-column cover stages.
All constructors carry the true graph E, not abstract age data alone.

The advance constructor retains actual reserved-clique geometry, the exact
new original column (with all gaps), and its finite numerical-H witness.
The tail starts from the very same updated complete column and cutoff.
This is a Prop-level certificate, not a claimed algorithm enumerating a
single coherent system of top-future embeddings. -/
inductive PhysicalCanonicalCoverHistory
    (E : Nat → Nat → Bool) (d ell : Nat)
    (ages : Nat → IntegerGraphSupport d ell → Nat)
    (supports : Nat → IntegerGraphSupport d ell)
    (sizes heights : Nat → Nat) (hd : 0 < d) :
    Nat → Nat → Nat → (Nat → Fin d → Bool) →
      Nat → (Nat → Fin d → Bool) → Prop where
  | stop (i b : Nat) (c : Nat → Fin d → Bool) :
      PhysicalCanonicalCoverHistory E d ell ages supports sizes heights hd
        i 0 b c b c
  | advance (i n b mid finish : Nat)
      (c cmid cfinal : Nat → Fin d → Bool)
      (Q : Finset Nat)
      (hCut : b ≤ mid)
      (hSize : Q.card = sizes i)
      (hWithin : ∀ q ∈ Q, b ≤ q ∧ q < mid)
      (hClique : IsDirectedCliqueOn E Q)
      (hIsolated : ∀ p, p < b → ∀ q ∈ Q,
        E p q = false ∧ E q p = false)
      (hColumn : cmid =
        supportBlockGappedColumn b Q (supports i).1 c)
      (hOld : ∀ p, p < b → ∀ t, cmid p t = c p t)
      (hAge : integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range mid) cmid) =
          ages (i + 1))
      (hStage : HasUniformPositiveSupportStage
        E d ell b mid (heights i) hd c Q (supports i))
      (tail : PhysicalCanonicalCoverHistory
        E d ell ages supports sizes heights hd
        (i + 1) n mid cmid finish cfinal) :
      PhysicalCanonicalCoverHistory E d ell ages supports sizes heights hd
        i (n + 1) b c finish cfinal

/-- The certificate preserves the initial complete old columns
and reaches the announced terminal age, provided the initial age is correct.
The theorem is independent of the number of stages. -/
theorem PhysicalCanonicalCoverHistory.terminal
    {E : Nat → Nat → Bool} {d ell : Nat}
    {ages : Nat → IntegerGraphSupport d ell → Nat}
    {supports : Nat → IntegerGraphSupport d ell}
    {sizes heights : Nat → Nat} {hd : 0 < d}
    {i n b F : Nat}
    {c cFinal : Nat → Fin d → Bool}
    (h : PhysicalCanonicalCoverHistory
      E d ell ages supports sizes heights hd i n b c F cFinal) :
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) = ages i →
    b ≤ F ∧
      (∀ p, p < b → ∀ t, cFinal p t = c p t) ∧
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range F) cFinal) =
          ages (i + n) := by
  induction h with
  | stop i b c =>
      intro hStart
      refine ⟨le_refl _, ?_, ?_⟩
      · intro p hp t
        rfl
      · simpa using hStart
  | advance i n b mid finish c cmid cfinal Q hCut hSize hWithin
      hClique hIsolated hColumn hOld hAge hStage tail ih =>
      intro hStart
      obtain ⟨hMidFinal, hKeep, hFinal⟩ := ih hAge
      refine ⟨hCut.trans hMidFinal, ?_, ?_⟩
      · intro p hp t
        calc
          cfinal p t = cmid p t :=
            hKeep p (lt_of_lt_of_le hp hCut) t
          _ = c p t := hOld p hp t
      · simpa [Nat.add_succ, Nat.add_assoc] using hFinal

/-- All stages exist simultaneously as one physical history in the SAME
actual Henson original graph, rather than only the final age.

The proof proceeds by finite induction, using the previously exact-head
verified genuine complete-prefix physical one-cover theorem at EACH stage.
The left-density and avoidance hypotheses are explicitly inherited.
Distinct stage-local numerical-H top embeddings are not identified. -/
theorem henson_leftDense_constructs_finite_physical_cover_history
    (d ell b steps : Nat) (hell : 2 ≤ ell) (hd : 0 < d)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool)
    (ages : Nat → IntegerGraphSupport d ell → Nat)
    (supports : Nat → IntegerGraphSupport d ell)
    (sizes heights : Nat → Nat)
    (hCover : ∀ i, i < steps →
      AgeCover (IsIntegerGraphAge d ell) (ages (i + 1)) (ages i))
    (hEll : ∀ i, i < steps →
      ell = ages (i + 1) (supports i) + sizes i + 1)
    (hStep : ∀ i, i < steps →
      ages i (supports i) = ages (i + 1) (supports i) + 1)
    (hPrior : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) = ages 0) :
    ∃ (F : Nat) (cFinal : Nat → Fin d → Bool),
      PhysicalCanonicalCoverHistory
        E d ell ages supports sizes heights hd
        0 steps b c F cFinal := by
  classical
  have hAux : ∀ (n i b' : Nat) (c' : Nat → Fin d → Bool),
      i + n ≤ steps →
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range b') c') = ages i →
      ∃ (F : Nat) (cFinal : Nat → Fin d → Bool),
        PhysicalCanonicalCoverHistory
          E d ell ages supports sizes heights hd
          i n b' c' F cFinal := by
    intro n
    induction n with
    | zero =>
        intro i b' c' _hBound _hAge
        exact ⟨b', c', .stop i b' c'⟩
    | succ n ih =>
        intro i b' c' hBound hCurrent
        have hi : i < steps := by omega
        have hNext : (i + 1) + n ≤ steps := by omega
        have hUpper : ages i (supports i) ≤ ell - 1 :=
          ((hCover i hi).upper_age.1 (supports i)).2
        have hPositive : 0 < sizes i := by
          have hOne := hStep i hi
          have hBlock := hEll i hi
          omega
        obtain ⟨Q, mid, hSize, hWithin, hClique, hIso,
          hAge, _hFeasible, hStage⟩ :=
          henson_leftDense_exists_physical_finite_canonical_cover_stage
            d ell b' (heights i) (sizes i) hell hd E
            hAvoid hDense c' (supports i)
            (ages (i + 1)) (ages i)
            (hCover i hi) (hEll i hi) (hStep i hi) hCurrent
        have hQPos : 0 < Q.card := by omega
        obtain ⟨q, hq⟩ := Finset.card_pos.mp hQPos
        have hBMid : b' ≤ mid :=
          (hWithin q hq).1.trans (Nat.le_of_lt (hWithin q hq).2)
        let cmid : Nat → Fin d → Bool :=
          supportBlockGappedColumn b' Q (supports i).1 c'
        have hKeep : ∀ p, p < b' → ∀ t, cmid p t = c' p t := by
          intro p hp t
          have hNotQ : p ∉ Q := by
            intro hqP
            have hpAfter := (hWithin p hqP).1
            omega
          simp [cmid, supportBlockGappedColumn,
            supportBlockOldColumn, delayedOldColumn, hNotQ, hp]
        have hAgeMid : integerGraphAgeCanonical d ell
            (finiteOldColumnRawBound E ell d
              (Finset.range mid) cmid) = ages (i + 1) := by
          simpa only [cmid] using hAge
        obtain ⟨F, cFinal, hTail⟩ :=
          ih (i + 1) mid cmid hNext hAgeMid
        exact ⟨F, cFinal,
          .advance i n b' mid F c' cmid cFinal Q
            hBMid hSize hWithin hClique hIso rfl hKeep hAgeMid
            hStage hTail⟩
  exact hAux steps 0 b c (by omega) hPrior

#print axioms Kk.PhysicalCanonicalCoverHistory.terminal
#print axioms Kk.henson_leftDense_constructs_finite_physical_cover_history

end Kk
