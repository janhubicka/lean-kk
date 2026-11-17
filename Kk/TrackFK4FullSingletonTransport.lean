import Kk.TrackFLowRankCompatibility
import Kk.TrackFRankOneTargetCompatibility
import Kk.TrackFRankTwoTargetCompatibility
import Mathlib.Tactic

/-!
# Track F: complete singleton source/target rank transport in K4-free Henson

English proof / hostile audit committed BEFORE Lean:
docs/track_f_k4_full_singleton_transport_english_audit.md

For the ACTUAL finite K4 Henson one-type structure, zero-based
singleton rank belongs to {0,1,2}. The three separately verified
same-rank source-target continuation theorems (#301,#302,#311)
now combine into a single uniform theorem covering EVERY
genuine source and target type compatible through an ACTUAL
rank-large coding-node fibre.

The successor clause of recursive rank largeness then derives
a uniform positive-rank DROP by applying the same-rank theorem
at the immediate lower source rank. This subsumes separate
#303 and #306 with no isolated-neighbour certificate repetition.

The embedding need only be INJECTIVE and INDUCED, not
chronologically monotone. Target normalized Henson avoidance
is explicit. This remains ONE-SOURCE singleton-rank transport,
NOT full simultaneous multi-sort graph-age synchronization or
diary/BRD unavoidability.
-/

namespace Kk.HensonOneType

/-- In a genuine K4-free finite one-type the zero-based singleton
rank cannot exceed 2. This is immediate from its ACTUAL finite
old-neighbour maximum-clique capacity, not from any diary axiom. -/
theorem k4_singleton_rank_le_two
    (E : Nat → Nat → Bool) (u : HensonOneType 4 E) :
    rank u ≤ 2 := by
  unfold rank finiteHensonTypeRank
  omega

/-- COMPLETE K4 SINGLETON SAME-RANK COMPATIBILITY theorem.

If the ACTUAL source coding-node target fibre is rank(u)-large
above any consistent source type u, then for EVERY target cutoff
the target prefix and source type can be jointly refined with
EXACT matching one-coordinate rank, still-large genuine fibre.

This combines three independently verified ranks:
zero (#301), one (#302, true source edge richness),
two (#311, true source triangle richness). Any injective
INDUCED embedding is allowed; no enumeration monotonicity. -/
theorem k4_sourceCodingFibre_continue_equal_rank
    (Esrc Etgt : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily 4 (by decide) →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (v0 : HensonOneType 4 Etgt)
    (B : Nat) (u : HensonOneType 4 Esrc)
    (hLarge : RankLargeness.Large rank
      (sourceCodingFibre (E := Esrc) Etgt e v0)
      (rank u) u) :
    ∃ vH : HensonOneType 4 Etgt,
    ∃ uH : HensonOneType 4 Esrc,
      v0 ≤ vH ∧ B ≤ vH.level ∧
      u ≤ uH ∧ rank uH = rank u ∧ rank vH = rank u ∧
      RankLargeness.Large rank
        (sourceCodingFibre (E := Esrc) Etgt e vH)
        (rank u) uH := by
  have hBound : rank u ≤ 2 := k4_singleton_rank_le_two Esrc u
  by_cases hu0 : rank u = 0
  · have hLarge0 :
        RankLargeness.Large rank
          (sourceCodingFibre (E := Esrc) Etgt e v0) 0 u := by
      simpa only [hu0] using hLarge
    obtain ⟨vH, uH, hV, hCut, hU, hURank, hVRank, hNewLarge⟩ :=
      sourceCodingFibre_continue_equal_rank_zero
        4 (by decide) Esrc Etgt hAvoid e he hInduced
        v0 B u hu0 hLarge0
    exact ⟨vH, uH, hV, hCut, hU,
      by simpa only [hu0] using hURank,
      by simpa only [hu0] using hVRank,
      by simpa only [hu0] using hNewLarge⟩
  by_cases hu1 : rank u = 1
  · have hLarge1 :
        RankLargeness.Large rank
          (sourceCodingFibre (E := Esrc) Etgt e v0) 1 u := by
      simpa only [hu1] using hLarge
    obtain ⟨vH, uH, hV, hCut, hU, hURank, hVRank, hNewLarge⟩ :=
      sourceCodingFibre_continue_equal_rank_one
        4 (by decide) Esrc Etgt hAvoid e he hInduced
        v0 B u hu1 hLarge1
    exact ⟨vH, uH, hV, hCut, hU,
      by simpa only [hu1] using hURank,
      by simpa only [hu1] using hVRank,
      by simpa only [hu1] using hNewLarge⟩
  have hu2 : rank u = 2 := by omega
  have hLarge2 :
      RankLargeness.Large rank
        (sourceCodingFibre (E := Esrc) Etgt e v0) 2 u := by
    simpa only [hu2] using hLarge
  obtain ⟨vH, uH, hV, hCut, hU, hURank, hVRank, hNewLarge⟩ :=
    sourceCodingFibre_continue_equal_rank_two
      4 (by decide) Esrc Etgt hAvoid e he hInduced
      v0 B u hu2 hLarge2
  exact ⟨vH, uH, hV, hCut, hU,
    by simpa only [hu2] using hURank,
    by simpa only [hu2] using hVRank,
    by simpa only [hu2] using hNewLarge⟩

/-- COMPLETE K4 SINGLETON POSITIVE-RANK DROP theorem.

If the ACTUAL source coding-node fibre is rank(u)-large
at a consistent source type of POSITIVE rank, then beyond
any target cutoff there are source and target refinements
of exactly one lower zero-based singleton rank, with
still-large ACTUAL source coding fibre.

Proof uses the successor-rank definition of largeness ONCE,
then the all-ranks same-rank continuation theorem above.
No separate source clique or isolated certificate construction
is needed at the drop step.

This is NOT the paper's full tuple/profile synchronization. -/
theorem k4_sourceCodingFibre_continue_drop_rank
    (Esrc Etgt : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily 4 (by decide) →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (v0 : HensonOneType 4 Etgt)
    (B : Nat) (u : HensonOneType 4 Esrc)
    (hPositive : 0 < rank u)
    (hLarge : RankLargeness.Large rank
      (sourceCodingFibre (E := Esrc) Etgt e v0)
      (rank u) u) :
    ∃ vH : HensonOneType 4 Etgt,
    ∃ uH : HensonOneType 4 Esrc,
      v0 ≤ vH ∧ B ≤ vH.level ∧
      u ≤ uH ∧ rank uH + 1 = rank u ∧
      rank vH = rank uH ∧
      RankLargeness.Large rank
        (sourceCodingFibre (E := Esrc) Etgt e vH)
        (rank uH) uH := by
  let n : Nat := rank u - 1
  have hu : rank u = n + 1 := by
    dsimp [n]
    omega
  have hLargeSucc :
      RankLargeness.Large rank
        (sourceCodingFibre (E := Esrc) Etgt e v0)
        (n + 1) u := by
    simpa only [hu] using hLarge
  obtain ⟨w, huw, hwRank, hwLarge⟩ :=
    hLargeSucc u (le_refl u) hu
  obtain ⟨vH, uH, hV, hCut, hW, hURank, hVRank, hNewLarge⟩ :=
    k4_sourceCodingFibre_continue_equal_rank
      Esrc Etgt hAvoid e he hInduced v0 B w hwLarge
  have hRankDrop : rank uH + 1 = rank u := by
    omega
  have hRanksEqual : rank vH = rank uH := by
    omega
  have hNewLargeUH :
      RankLargeness.Large rank
        (sourceCodingFibre (E := Esrc) Etgt e vH)
        (rank uH) uH := by
    simpa only [hURank] using hNewLarge
  exact ⟨vH, uH, hV, hCut, le_trans huw hW,
    hRankDrop, hRanksEqual, hNewLargeUH⟩

end Kk.HensonOneType
