import Kk.TrackFRankLargeFiniteFan
import Mathlib.Tactic

/-!
# Track F: finite-colour large Henson fans with chronological bounds

English proof and adversarial scope audit were committed before Lean:
docs/track_f_coloured_fan_english_audit.md

A genuinely rank-large finite one-type set has, beyond any prescribed
old height, a rank-large colour class whose finite fans contain
arbitrarily many mutually incompatible lower-rank daughter cones
with pairwise disjoint fresh positive-neighbour markers.

The second theorem removes finitely many source coding nodes before
choosing a colour and extracts one actual member in every daughter
cone. No source-target rank equality, embedding-induced prefix
colour or global BRD statement is assumed or concluded.
-/

namespace Kk.HensonOneType

universe v

variable {ell : Nat} {E : Nat → Nat → Bool}
variable {Colour : Type v} [Fintype Colour]

/-- After an arbitrary finite colouring of actual finite Henson
one-types, one monochromatic rank-large cone remains above any
height bound, and it has an arbitrary finite fan of rank-large
lower-rank daughters. The all-support marker disjointness is the
EXACT one supplied by the verified finite-fan theorem. -/
theorem rank_large_coloured_finite_fan
    (S : Set (HensonOneType ell E))
    (colour : HensonOneType ell E → Colour)
    (n : Nat) (u : HensonOneType ell E)
    (hu : rank u = n + 1)
    (hLarge : RankLargeness.Large rank S (n + 1) u)
    (height k : Nat) :
    ∃ j : Colour, ∃ v : HensonOneType ell E,
      ∃ F : Finset (HensonOneType ell E),
      u ≤ v ∧ height ≤ v.level ∧ rank v = n + 1 ∧
      RankLargeness.Large rank
        {x | x ∈ S ∧ colour x = j} (n + 1) v ∧
      F.card = k ∧
      (∀ w ∈ F, v ≤ w ∧ rank w = n ∧
        RankLargeness.Large rank
          {x | x ∈ S ∧ colour x = j} n w) ∧
      (∀ w ∈ F, ∀ z ∈ F, w ≠ z →
        (¬ ∃ t : HensonOneType ell E, w ≤ t ∧ z ≤ t) ∧
        Disjoint (w.neighbours \ v.neighbours)
          (z.neighbours \ v.neighbours)) := by
  classical
  let m : Nat := max u.level height
  let t : HensonOneType ell E :=
    zeroPad u m (le_max_left _ _)
  have hut : u ≤ t := le_zeroPad u m (le_max_left _ _)
  have htRank : rank t = n + 1 := by
    calc
      rank t = rank u := rank_zeroPad u m (le_max_left _ _)
      _ = n + 1 := hu
  have htLarge : RankLargeness.Large rank S (n + 1) t :=
    RankLargeness.large_mono_cone rank S (n + 1)
      u t hut hLarge
  obtain ⟨j, w, htw, hwRank, hwLarge⟩ :=
    RankLargeness.large_finite_colour_partition
      rank rank_antitone S colour (n + 1) t htRank htLarge
  obtain ⟨F, hCard, hMembers, hSeparated⟩ :=
    rank_large_finite_fan
      {x : HensonOneType ell E | x ∈ S ∧ colour x = j}
      n w hwRank hwLarge k
  have huw : u ≤ w := le_trans hut htw
  have hHeight : height ≤ w.level := by
    have hm : height ≤ m := le_max_right _ _
    exact hm.trans htw.1
  exact ⟨j, w, F, huw, hHeight, hwRank,
    hwLarge, hCard, hMembers, hSeparated⟩

/-- Remove a finite set of bad coding nodes, select one colour above
a prescribed old level, and obtain k incompatible large daughter
cones plus an ACTUAL coding-type member of the selected colour in
each daughter cone. No freshness/disjointness claim is made about
the later witnesses' own positive markers, only the daughters'. -/
theorem rank_large_coloured_finite_fan_avoiding
    (S : Set (HensonOneType ell E))
    (bad : Finset (HensonOneType ell E))
    (colour : HensonOneType ell E → Colour)
    (n : Nat) (u : HensonOneType ell E)
    (hu : rank u = n + 1)
    (hLarge : RankLargeness.Large rank S (n + 1) u)
    (height k : Nat) :
    ∃ j : Colour, ∃ v : HensonOneType ell E,
      ∃ F : Finset (HensonOneType ell E),
      u ≤ v ∧ height ≤ v.level ∧ rank v = n + 1 ∧
      F.card = k ∧
      (∀ w ∈ F, v ≤ w ∧ rank w = n ∧
        RankLargeness.Large rank
          {x | x ∈ (S \ (↑bad : Set (HensonOneType ell E))) ∧
            colour x = j} n w) ∧
      (∀ w ∈ F, ∃ x : HensonOneType ell E,
        w ≤ x ∧ x ∈ S ∧ x ∉ bad ∧ colour x = j) ∧
      (∀ w ∈ F, ∀ z ∈ F, w ≠ z →
        (¬ ∃ t : HensonOneType ell E, w ≤ t ∧ z ≤ t) ∧
        Disjoint (w.neighbours \ v.neighbours)
          (z.neighbours \ v.neighbours)) := by
  classical
  have hOrig : RankLargeness.Large rank S (rank u) u := by
    simpa only [hu] using hLarge
  obtain ⟨u', huu', hu'Rank, hDiff⟩ :=
    large_difference_finite S bad u hOrig
  have hu' : rank u' = n + 1 := hu'Rank.trans hu
  have hDiff' :
      RankLargeness.Large rank
        (S \ (↑bad : Set (HensonOneType ell E))) (n + 1) u' := by
    simpa only [hu] using hDiff
  obtain ⟨j, w, F, hu'w, hHeight, hwRank,
    _hwFibre, hCard, hMembers, hSeparated⟩ :=
    rank_large_coloured_finite_fan
      (S \ (↑bad : Set (HensonOneType ell E))) colour
      n u' hu' hDiff' height k
  refine ⟨j, w, F, le_trans huu' hu'w,
    hHeight, hwRank, hCard, hMembers, ?_, hSeparated⟩
  intro d hd
  obtain ⟨_hwd, hRankD, hLargeD⟩ := hMembers d hd
  obtain ⟨x, hdx, hx⟩ :=
    RankLargeness.large_has_member rank
      {x : HensonOneType ell E |
        x ∈ (S \ (↑bad : Set (HensonOneType ell E))) ∧
        colour x = j}
      n d hRankD hLargeD
  have hxS : x ∈ S := hx.1.1
  have hxBad : x ∉ bad := by
    simpa using hx.1.2
  exact ⟨x, hdx, hxS, hxBad, hx.2⟩

end Kk.HensonOneType
