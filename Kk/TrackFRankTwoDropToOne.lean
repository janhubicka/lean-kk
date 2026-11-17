import Kk.TrackFRankOneTargetCompatibility
import Mathlib.Tactic

/-!
# Track F: actual compatible rank two to one target/source drop

English proof and hostile audit committed BEFORE Lean:
docs/track_f_rank_two_drop_to_one_english_audit.md

Here Lean zero-based rank2 means manuscript singleton rank3,
and rank1 means manuscript singleton rank2. The defining
recursive rank2 largeness gives a rank1-large descendant;
the already verified rank1 SAME-RANK target continuation
provides both source and target rank1 after any target cutoff.

No Henson enumeration order preservation, diary theorem,
triangle richness or global BRD assumption is used.
This does not establish same-rank rank2/triangle richness
or full multi-sort profile synchronization.
-/

namespace Kk.HensonOneType

/-- Actual compatible drop from manuscript singleton rank THREE
to rank TWO: from a source rank2-large actual coding-node
target fibre obtain a source rank1 refinement and a genuine
target rank1 type extending the original target prefix, at
any requested later target level, retaining rank1 largeness.

The embedding e is injective and induced, NOT assumed monotone. -/
theorem sourceCodingFibre_drop_rank_two_to_one
    (ell : Nat) (hell : 2 ≤ ell)
    (Esrc Etgt : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (v0 : HensonOneType ell Etgt)
    (B : Nat) (u : HensonOneType ell Esrc)
    (hu : rank u = 2)
    (hLarge : RankLargeness.Large rank
      (sourceCodingFibre (E := Esrc) Etgt e v0) 2 u) :
    ∃ vH : HensonOneType ell Etgt,
    ∃ uH : HensonOneType ell Esrc,
      v0 ≤ vH ∧ B ≤ vH.level ∧
      u ≤ uH ∧ rank uH = 1 ∧ rank vH = 1 ∧
      RankLargeness.Large rank
        (sourceCodingFibre (E := Esrc) Etgt e vH) 1 uH := by
  obtain ⟨w, huw, hwRank, hwLarge⟩ :=
    hLarge u (le_refl u) hu
  obtain ⟨vH, uH, hVExtend, hLevel, hWExtend,
    hURank, hVRank, hNewLarge⟩ :=
    sourceCodingFibre_continue_equal_rank_one
      ell hell Esrc Etgt hAvoid e he hInduced
      v0 B w hwRank hwLarge
  exact ⟨vH, uH, hVExtend, hLevel,
    le_trans huw hWExtend, hURank, hVRank, hNewLarge⟩

end Kk.HensonOneType
