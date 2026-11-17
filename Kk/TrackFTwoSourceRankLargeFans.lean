import Kk.TrackFRankLargeFiniteFan
import Mathlib.Tactic

/-!
# Track F: disjoint fresh-marker fans for TWO rank-large Henson sources

English-first proof / hostile audit:
docs/track_f_two_source_fan_english_audit.md

The theorem is about ACTUAL chronological finite Henson one-types.
It constructs a finite fan for the first rank-large source, then
zero-pads the SECOND source beyond every first-fan daughter level
before selecting its own finite fan. The new positive-neighbour
marker sets are disjoint across source families.

It does NOT prove a prescribed finite graph can be jointly realized
by coding vertices in these cones, nor source-target compatible
fibre synchronization under an embedding.
-/

namespace Kk.HensonOneType

variable {ell : Nat} {E : Nat → Nat → Bool}

/-- Disjointness of positive markers for two DIFFERENT source roots:
the first finite type a ends at or before H; the second type b
extends the all-zero continuation of its own (possibly unrelated)
root v to H. Therefore b has no NEW positive marker below H.

There is no assumption that a extends v, or that the two roots
have the same singleton rank or identical old neighbourhoods. -/
theorem fresh_markers_disjoint_of_later_zeroPad
    (u a v b : HensonOneType ell E)
    (H : Nat)
    (haH : a.level ≤ H)
    (hvH : v.level ≤ H)
    (hzb : zeroPad v H hvH ≤ b) :
    Disjoint (a.neighbours \ u.neighbours)
      (b.neighbours \ v.neighbours) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxa hxb
  have hxInA : x ∈ a.neighbours :=
    (Finset.mem_sdiff.mp hxa).1
  have hxlt : x < H :=
    lt_of_lt_of_le (a.below x hxInA) haH
  have hxInB : x ∈ b.neighbours :=
    (Finset.mem_sdiff.mp hxb).1
  have hxInV : x ∈ v.neighbours :=
    (hzb.2 x hxlt).mpr hxInB
  exact (Finset.mem_sdiff.mp hxb).2 hxInV

/-- Finite fans of TWO independently rank-large actual Henson
one-types can be selected with pairwise disjoint fresh positive
markers ACROSS the two source families.

Each family's own finite-fan theorem also supplies internal
incompatibility and marker disjointness; both facts are retained
in the conclusion. The source ranks may differ. -/
theorem rank_large_two_source_fans
    (S T : Set (HensonOneType ell E))
    (r s : Nat)
    (u v : HensonOneType ell E)
    (hu : rank u = r + 1)
    (hv : rank v = s + 1)
    (hS : RankLargeness.Large rank S (r + 1) u)
    (hT : RankLargeness.Large rank T (s + 1) v)
    (k l : Nat) :
    ∃ F G : Finset (HensonOneType ell E),
      F.card = k ∧ G.card = l ∧
      (∀ a ∈ F, u ≤ a ∧ rank a = r ∧
        RankLargeness.Large rank S r a) ∧
      (∀ b ∈ G, v ≤ b ∧ rank b = s ∧
        RankLargeness.Large rank T s b) ∧
      (∀ a ∈ F, ∀ a' ∈ F, a ≠ a' →
        (¬ ∃ t : HensonOneType ell E, a ≤ t ∧ a' ≤ t) ∧
        Disjoint (a.neighbours \ u.neighbours)
          (a'.neighbours \ u.neighbours)) ∧
      (∀ b ∈ G, ∀ b' ∈ G, b ≠ b' →
        (¬ ∃ t : HensonOneType ell E, b ≤ t ∧ b' ≤ t) ∧
        Disjoint (b.neighbours \ v.neighbours)
          (b'.neighbours \ v.neighbours)) ∧
      (∀ a ∈ F, ∀ b ∈ G,
        Disjoint (a.neighbours \ u.neighbours)
          (b.neighbours \ v.neighbours)) := by
  classical
  obtain ⟨F, hFcard, hFmembers, hFsep⟩ :=
    rank_large_finite_fan S r u hu hS k
  let m : Nat := max v.level (F.sup (fun a => a.level) + 1)
  let z : HensonOneType ell E :=
    zeroPad v m (le_max_left _ _)
  have hvz : v ≤ z := le_zeroPad v m (le_max_left _ _)
  have hzRank : rank z = s + 1 := by
    calc
      rank z = rank v := rank_zeroPad v m (le_max_left _ _)
      _ = s + 1 := hv
  have hTz : RankLargeness.Large rank T (s + 1) z :=
    RankLargeness.large_mono_cone rank T (s + 1)
      v z hvz hT
  obtain ⟨G, hGcard, hGmembers, hGsep⟩ :=
    rank_large_finite_fan T s z hzRank hTz l
  have hGmembersV : ∀ b ∈ G, v ≤ b ∧ rank b = s ∧
      RankLargeness.Large rank T s b := by
    intro b hb
    obtain ⟨hzb, hbr, hbLarge⟩ := hGmembers b hb
    exact ⟨le_trans hvz hzb, hbr, hbLarge⟩
  have hGsepV : ∀ b ∈ G, ∀ b' ∈ G, b ≠ b' →
      (¬ ∃ t : HensonOneType ell E, b ≤ t ∧ b' ≤ t) ∧
      Disjoint (b.neighbours \ v.neighbours)
        (b'.neighbours \ v.neighbours) := by
    intro b hb b' hb' hne
    obtain ⟨hNo, hDisj⟩ := hGsep b hb b' hb' hne
    refine ⟨hNo, ?_⟩
    simpa only [z, zeroPad] using hDisj
  refine ⟨F, G, hFcard, hGcard,
    hFmembers, hGmembersV, hFsep, hGsepV, ?_⟩
  intro a ha b hb
  have haBound : a.level ≤ m := by
    have hSup : a.level ≤ F.sup (fun t => t.level) :=
      Finset.le_sup (f := fun t : HensonOneType ell E => t.level) ha
    have hLe : F.sup (fun t => t.level) + 1 ≤ m :=
      le_max_right _ _
    omega
  have hzb : z ≤ b := (hGmembers b hb).1
  exact fresh_markers_disjoint_of_later_zeroPad
    u a v b m haBound (le_max_left _ _) hzb

end Kk.HensonOneType
