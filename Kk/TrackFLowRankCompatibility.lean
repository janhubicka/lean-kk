import Kk.TrackFNonrootRankUpperContinuation
import Mathlib.Tactic

/-!
# Track F: exact low-rank source/target compatible continuation

The English proof and hostile audit were committed before Lean:
docs/track_f_low_rank_compatible_transport_english_audit.md

The zero-based source rank 0 case (manuscript singleton rank 1)
follows already from the verified actual nonroot continuation
with target rank ≤ source rank. The next rank 1 case will require
the genuine edge-richness theorem from draft PR #300 and a
two-vertex future target clique.

This source contains NO global diary/BRD lower-bound theorem.
-/

namespace Kk.HensonOneType

/-- A rank-zero ACTUAL source coding fibre can always be continued
to an arbitrary later genuine target prefix, retaining exact
EQUALITY of source and target rank zero and actual fibre density.

The index map e is injective and induced but NOT assumed
order-preserving. The target Henson forbidden-family avoidance
is explicit. This is the complete same-rank transport base
case for manuscript singleton rank ONE. -/
theorem sourceCodingFibre_continue_equal_rank_zero
    (ell : Nat) (hell : 2 ≤ ell)
    (Esrc Etgt : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (v0 : HensonOneType ell Etgt)
    (B : Nat) (u : HensonOneType ell Esrc)
    (hu : rank u = 0)
    (hLarge : RankLargeness.Large rank
      (sourceCodingFibre (E := Esrc) Etgt e v0) 0 u) :
    ∃ vH : HensonOneType ell Etgt,
    ∃ uH : HensonOneType ell Esrc,
      v0 ≤ vH ∧ B ≤ vH.level ∧
      u ≤ uH ∧ rank uH = 0 ∧ rank vH = 0 ∧
      RankLargeness.Large rank
        (sourceCodingFibre (E := Esrc) Etgt e vH) 0 uH := by
  have hAtSourceRank :
      RankLargeness.Large rank
        (sourceCodingFibre (E := Esrc) Etgt e v0)
        (rank u) u := by
    simpa only [hu] using hLarge
  obtain ⟨vH, uH, hVExtend, hLevel, hUExtend, hURank,
    hFibreLarge, hTargetLe⟩ :=
    sourceCodingFibre_extend_target_rank_le
      ell hell Esrc Etgt hAvoid e he hInduced
      v0 B u hAtSourceRank
  have hTargetZero : rank vH = 0 := by omega
  refine ⟨vH, uH, hVExtend, hLevel, hUExtend, ?_,
    hTargetZero, ?_⟩
  · exact hURank.trans hu
  · simpa only [hu] using hFibreLarge

end Kk.HensonOneType
