import Kk.TrackFTwoSourceRankLargeFans
import Mathlib.Tactic

/-!
# Track F: new rank-large daughter fans after arbitrary finite history

English proof and hostile checks were committed before Lean:
docs/track_f_finite_history_new_fan_english_audit.md

The previous selected source type nodes may have unrelated roots,
singleton ranks, and coding fibres. Zero padding the NEW root
u beyond all their chronological heights ensures the fresh
positive-neighbour markers of every new daughter are disjoint
from every previous node's marker set, relative to ANY
user-specified roots for those previous nodes.

The new daughters also retain their own rank-large S fibres,
pairwise incompatible future cones and internally disjoint
fresh positive markers.

No global multi-sort graph-age compatibility, target embedding,
or diary/BRD theorem is assumed or concluded.
-/

namespace Kk.HensonOneType

variable {ell : Nat} {E : Nat → Nat → Bool}

/-- Extend ANY finite chronological source-type history by an
arbitrarily large finite fan of rank-lowered, rank-large
daughter cones, with fresh positive-neighbour marker sets
disjoint from the markers of all previous nodes.

Every old history node a may have its own completely arbitrary
reference root oldRoot(a); NO agreement of these roots, ranks,
or old positive neighbourhoods is assumed. The cross-family
marker disjointness is purely chronological and uses the
exact preservation of negative bits under zero padding.

The newly selected fan is NOT asserted to realize any
prescribed graph edges between future coding originals. -/
theorem rank_large_new_fan_after_finite_history
    (S : Set (HensonOneType ell E))
    (n : Nat) (u : HensonOneType ell E)
    (hu : rank u = n + 1)
    (hLarge : RankLargeness.Large rank S (n + 1) u)
    (old : Finset (HensonOneType ell E))
    (oldRoot : HensonOneType ell E → HensonOneType ell E)
    (k : Nat) :
    ∃ G : Finset (HensonOneType ell E),
      G.card = k ∧
      (∀ g ∈ G, u ≤ g ∧ rank g = n ∧
        RankLargeness.Large rank S n g) ∧
      (∀ g ∈ G, ∀ h ∈ G, g ≠ h →
        (¬ ∃ t : HensonOneType ell E, g ≤ t ∧ h ≤ t) ∧
        Disjoint (g.neighbours \ u.neighbours)
          (h.neighbours \ u.neighbours)) ∧
      (∀ a ∈ old, ∀ g ∈ G,
        Disjoint (a.neighbours \ (oldRoot a).neighbours)
          (g.neighbours \ u.neighbours)) := by
  classical
  let cap : Nat := old.sup (fun a => a.level)
  let H : Nat := max u.level (cap + 1)
  let z : HensonOneType ell E :=
    zeroPad u H (le_max_left _ _)
  have huz : u ≤ z := le_zeroPad u H (le_max_left _ _)
  have hzRank : rank z = n + 1 := by
    calc
      rank z = rank u := rank_zeroPad u H (le_max_left _ _)
      _ = n + 1 := hu
  have hzLarge : RankLargeness.Large rank S (n + 1) z :=
    RankLargeness.large_mono_cone rank S (n + 1)
      u z huz hLarge
  obtain ⟨G, hCard, hMembers, hSep⟩ :=
    rank_large_finite_fan S n z hzRank hzLarge k
  have hMembersU : ∀ g ∈ G, u ≤ g ∧ rank g = n ∧
      RankLargeness.Large rank S n g := by
    intro g hg
    obtain ⟨hzg,hgr,hgLarge⟩ := hMembers g hg
    exact ⟨le_trans huz hzg,hgr,hgLarge⟩
  have hSepU : ∀ g ∈ G, ∀ h ∈ G, g ≠ h →
      (¬ ∃ t : HensonOneType ell E, g ≤ t ∧ h ≤ t) ∧
      Disjoint (g.neighbours \ u.neighbours)
        (h.neighbours \ u.neighbours) := by
    intro g hg h hh hne
    obtain ⟨hNo,hDisjoint⟩ := hSep g hg h hh hne
    refine ⟨hNo, ?_⟩
    simpa only [z, zeroPad] using hDisjoint
  refine ⟨G, hCard, hMembersU, hSepU, ?_⟩
  intro a ha g hg
  have haBound : a.level ≤ H := by
    have hA : a.level ≤ cap :=
      Finset.le_sup (f := fun t : HensonOneType ell E => t.level) ha
    have hCap : cap + 1 ≤ H := le_max_right _ _
    omega
  have hzg : z ≤ g := (hMembers g hg).1
  exact fresh_markers_disjoint_of_later_zeroPad
    (oldRoot a) a u g H haBound (le_max_left _ _) hzg

end Kk.HensonOneType
