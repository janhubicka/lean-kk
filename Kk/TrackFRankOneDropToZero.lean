import Kk.TrackFLowRankCompatibility
import Mathlib.Tactic

/-!
# Track F: compatible rank-one to rank-zero Henson type transport

The English proof and hostile audit were committed first:
docs/track_f_rank_one_drop_to_zero_english_audit.md

The successor clause of recursive rank largeness supplies a
rank-zero source descendant supporting a rank-zero-large
ACTUAL coding-node target fibre. The already verified rank-zero
same-rank non-root continuation theorem then produces a genuine
target rank-zero type beyond any cutoff and a rank-zero source
refinement with still-large ACTUAL fibre.

This is the manuscript singleton rank-two-to-one DROP case,
not the full arbitrary-rank transport or multi-sort theorem.
-/

namespace Kk.HensonOneType

/-- From a manuscript-rank-two compatible source fibre, decrease
BOTH source and target singleton ranks to manuscript rank one,
and preserve actual source-fibre largeness beyond any target bound.

The source original-index map e is an injective INDUCED graph
embedding, not assumed to preserve chronological enumeration.
No extra one-point or diary unavoidability axiom is used. -/
theorem sourceCodingFibre_drop_rank_one_to_zero
    (ell : Nat) (hell : 2 ≤ ell)
    (Esrc Etgt : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (v0 : HensonOneType ell Etgt)
    (B : Nat) (u : HensonOneType ell Esrc)
    (hu : rank u = 1)
    (hLarge : RankLargeness.Large rank
      (sourceCodingFibre (E := Esrc) Etgt e v0) 1 u) :
    ∃ vH : HensonOneType ell Etgt,
    ∃ uH : HensonOneType ell Esrc,
      v0 ≤ vH ∧ B ≤ vH.level ∧
      u ≤ uH ∧ rank uH = 0 ∧ rank vH = 0 ∧
      RankLargeness.Large rank
        (sourceCodingFibre (E := Esrc) Etgt e vH) 0 uH := by
  obtain ⟨w, huw, hwRank, hwLarge⟩ :=
    hLarge u (le_refl u) hu
  obtain ⟨vH, uH, hVExtend, hLevel, hWExtend,
    hURank, hVRank, hNewLarge⟩ :=
    sourceCodingFibre_continue_equal_rank_zero
      ell hell Esrc Etgt hAvoid e he hInduced
      v0 B w hwRank hwLarge
  exact ⟨vH, uH, hVExtend, hLevel,
    le_trans huw hWExtend, hURank, hVRank, hNewLarge⟩

end Kk.HensonOneType
