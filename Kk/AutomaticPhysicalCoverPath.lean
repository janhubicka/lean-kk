import Kk.IntegerAgeCoverUnitDrop
import Kk.FinitePhysicalCoverHistory
import Mathlib.Tactic

/-!
# Track B: automatic finite physical saturated-cover histories

English proof and hostile audit:
`docs/track_b_automatic_cover_chain_english_audit_20261122.md`.

This module builds an actual chronological Prop-level history from a genuine
lower age, not a pre-supplied chain of covers. Each step has its genuine
isolated Henson clique, complete columns, true gaps and a STAGE-LOCAL
numerical-H future. It does NOT identify those numerical-H futures
across stages or transport full dependent Kpt/L+/E records.
-/

namespace Kk

/-- A finite physically realized path of genuine canonical-age covers.
The internal ages and supports are *chosen*, not supplied as a list. -/
inductive PhysicalGeneratedCoverPath
    (E : Nat → Nat → Bool) (d ell k : Nat) (hd : 0 < d) :
      (IntegerGraphSupport d ell → Nat) →
      Nat → (Nat → Fin d → Bool) →
      (IntegerGraphSupport d ell → Nat) →
      Nat → (Nat → Fin d → Bool) → Prop where
  | stop (A : IntegerGraphSupport d ell → Nat)
      (b : Nat) (c : Nat → Fin d → Bool) :
      PhysicalGeneratedCoverPath E d ell k hd A b c A b c
  | advance {upper middle lower : IntegerGraphSupport d ell → Nat}
      (b cutoff finish : Nat)
      (c cmid cfinal : Nat → Fin d → Bool)
      (Q : Finset Nat) (T : IntegerGraphSupport d ell) (r : Nat)
      (hCover : AgeCover (IsIntegerGraphAge d ell) middle upper)
      (hAt : upper T = middle T + 1)
      (hEll : ell = middle T + r + 1)
      (hSize : Q.card = r)
      (hWithin : ∀ q ∈ Q, b ≤ q ∧ q < cutoff)
      (hClique : IsDirectedCliqueOn E Q)
      (hIsolated : ∀ p, p < b → ∀ q ∈ Q,
        E p q = false ∧ E q p = false)
      (hColumn : cmid = supportBlockGappedColumn b Q T.1 c)
      (hOld : ∀ p, p < b → ∀ t, cmid p t = c p t)
      (hAge : integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range cutoff) cmid) =
          middle)
      (hStage : HasUniformPositiveSupportStage
        E d ell b cutoff k hd c Q T)
      (tail : PhysicalGeneratedCoverPath
        E d ell k hd middle cutoff cmid lower finish cfinal) :
      PhysicalGeneratedCoverPath
        E d ell k hd upper b c lower finish cfinal

/-- Each constructed chronological cover path preserves the complete
initial original table, reaches the claimed final canonical age, and
never moves an original index backwards. -/
theorem PhysicalGeneratedCoverPath.terminal
    {E : Nat → Nat → Bool} {d ell k : Nat} {hd : 0 < d}
    {upper lower : IntegerGraphSupport d ell → Nat}
    {b finish : Nat} {c cfinal : Nat → Fin d → Bool}
    (history : PhysicalGeneratedCoverPath
      E d ell k hd upper b c lower finish cfinal) :
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) = upper →
    b ≤ finish ∧
      (∀ p, p < b → ∀ t, cfinal p t = c p t) ∧
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range finish) cfinal) =
          lower := by
  induction history with
  | stop A b c =>
      intro h
      exact ⟨le_rfl, (by intros; rfl), h⟩
  | advance b cutoff finish c cmid cfinal Q T r hCover hAt hEll
        hSize hWithin hClique hIsolated hColumn hOld hAge hStage tail ih =>
      intro hPrior
      obtain ⟨hNext, hKeep, hFinal⟩ := ih hAge
      have hBound := (hCover.upper_age.1 T).2
      have hQPos : 0 < Q.card := by
        rw [hSize]
        omega
      obtain ⟨q,hq⟩ := Finset.card_pos.mp hQPos
      have hBF : b ≤ cutoff :=
        (hWithin q hq).1.trans (Nat.le_of_lt (hWithin q hq).2)
      refine ⟨hBF.trans hNext, ?_, hFinal⟩
      intro p hp t
      calc
        cfinal p t = cmid p t := hKeep p (lt_of_lt_of_le hp hBF) t
        _ = c p t := hOld p hp t

/-- Given an actual finite Henson old-column prefix and a cover chain,
construct a single Prop-level chronological history of *real* cover
blocks. Every previous cutoff and complete table is used by its successor. -/
theorem henson_leftDense_constructs_physical_age_cover_path
    (E : Nat → Nat → Bool)
    (d ell k : Nat) (hell : 2 ≤ ell) (hd : 0 < d)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    {upper lower : IntegerGraphSupport d ell → Nat}
    (chain : AgeCoverChain (IsIntegerGraphAge d ell) upper lower)
    (b : Nat) (c : Nat → Fin d → Bool)
    (hPrior : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) = upper) :
    ∃ (finish : Nat) (cfinal : Nat → Fin d → Bool),
      PhysicalGeneratedCoverPath
        E d ell k hd upper b c lower finish cfinal := by
  classical
  have hBuild : ∀ {U L : IntegerGraphSupport d ell → Nat},
      AgeCoverChain (IsIntegerGraphAge d ell) U L →
      ∀ (b' : Nat) (col : Nat → Fin d → Bool),
        integerGraphAgeCanonical d ell
          (finiteOldColumnRawBound E ell d (Finset.range b') col) = U →
        ∃ (finish : Nat) (cfinal : Nat → Fin d → Bool),
          PhysicalGeneratedCoverPath
            E d ell k hd U b' col L finish cfinal := by
    intro U L path
    induction path with
    | refl A =>
        intro b' col hAge
        exact ⟨b', col, .stop A b' col⟩
    | @step A M L hCover tail ih =>
        intro b' col hAge
        have hChanged : ∃ T : IntegerGraphSupport d ell,
            M T < A T := by
          by_contra hNo
          push_neg at hNo
          apply hCover.strict
          funext T
          exact Nat.le_antisymm (hCover.le T) (hNo T)
        obtain ⟨T,hChangedT⟩ := hChanged
        let r := ell - 1 - M T
        have hArith := integerGraphAge_cover_changed_support_block_size
          d ell M A hCover T hChangedT
        have hr : 0 < r := hArith.1
        have hEll : ell = M T + r + 1 := hArith.2.2
        have hAt : A T = M T + 1 :=
          integerGraphAge_cover_changed_support_unit_drop
            d ell M A hCover T hChangedT
        obtain ⟨Q,cutoff,hSize,hWithin,hClique,hIsolated,hNextAge,
          _hFeasible,hStage⟩ :=
          henson_leftDense_exists_physical_finite_canonical_cover_stage
            d ell b' k r hell hd E hAvoid hDense col T M A
            hCover hEll hAt hAge
        let cmid := supportBlockGappedColumn b' Q T.1 col
        have hOld : ∀ p, p < b' → ∀ t, cmid p t = col p t := by
          intro p hp t
          have hpNot : p ∉ Q := by
            intro hpQ
            have hAfter := (hWithin p hpQ).1
            omega
          simp [cmid, supportBlockGappedColumn, supportBlockOldColumn,
            delayedOldColumn, hpNot, hp]
        have hAgeMid : integerGraphAgeCanonical d ell
            (finiteOldColumnRawBound E ell d
              (Finset.range cutoff) cmid) = M := by
          simpa only [cmid] using hNextAge
        obtain ⟨finish,cfinal,hTail⟩ :=
          ih cutoff cmid hAgeMid
        exact ⟨finish,cfinal,
          .advance b' cutoff finish col cmid cfinal Q T r
            hCover hAt hEll hSize hWithin hClique hIsolated
            rfl hOld hAgeMid hStage hTail⟩
  exact hBuild chain b c hPrior

/-- The strong finite Track B conclusion: an actual genuine lower target
below the complete old canonical age is reached through a *constructed*
finite path of genuine physically realized canonical covers.

It neither supplies a prescribed diary event order nor a single coherent
family of selected top numerical-H witnesses. -/
theorem henson_leftDense_normalizes_genuine_age_by_covers
    (E : Nat → Nat → Bool)
    (d ell k b : Nat) (hell : 2 ≤ ell) (hd : 0 < d)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool)
    (target : IntegerGraphSupport d ell → Nat)
    (hTargetAge : IsIntegerGraphAge d ell target)
    (hBelow : AgeLe target
      (integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range b) c))) :
    ∃ (F : Nat) (cfinal : Nat → Fin d → Bool),
      PhysicalGeneratedCoverPath E d ell k hd
        (integerGraphAgeCanonical d ell
          (finiteOldColumnRawBound E ell d (Finset.range b) c))
        b c target F cfinal := by
  classical
  let B := finiteOldColumnRawBound E ell d (Finset.range b) c
  let upper := integerGraphAgeCanonical d ell B
  have hBelowRaw : AgeLe target B := by
    intro T
    exact (hBelow T).trans (integerGraphAgeCanonical_le_raw d ell B T)
  have hUpperAge : IsIntegerGraphAge d ell upper :=
    integerGraphAgeCanonical_is_age d ell B target
      hTargetAge hBelowRaw
  have hChain : AgeCoverChain (IsIntegerGraphAge d ell) upper target :=
    integerGraphAge_exists_saturated_chain d ell target upper
      hTargetAge hUpperAge hBelow
  exact henson_leftDense_constructs_physical_age_cover_path
    E d ell k hell hd hAvoid hDense hChain b c rfl

#print axioms Kk.PhysicalGeneratedCoverPath.terminal
#print axioms Kk.henson_leftDense_constructs_physical_age_cover_path
#print axioms Kk.henson_leftDense_normalizes_genuine_age_by_covers

end Kk
