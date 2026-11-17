import Kk.TrackFFiniteHistoryFan
import Kk.TrackFTwoSourceRankLargeFans
import Mathlib.Tactic

/-!
# Track F: rank-large daughter fan after a LABELLED finite source history

English proof and hostile audit committed BEFORE Lean:
docs/track_f_labelled_history_fan_english_audit.md

Previous source-history entries are PAIRS (old node, old root),
not just old nodes. This matters when the SAME previously
selected finite type may be used under different old source
roots, so its fresh positive marker sets differ depending
on the source sort label.

The new daughter family is chosen after zero-padding beyond
the FIRST component's height of EVERY old pair, preserving
rank/largeness and avoiding EVERY labelled previous marker
set simultaneously. No graph-age/target-fibre synchronization
or diary/BRD theorem is assumed.
-/

namespace Kk.HensonOneType

variable {ell : Nat} {E : Nat → Nat → Bool}

/-- Choose a genuinely rank-large finite fan of k lower-rank
daughters whose positive fresh markers avoid EVERY labelled
prior finite source-type marker pair (oldNode,oldRoot).

Unlike an unlabelled old-node history, this allows the SAME
oldNode to appear with DIFFERENT oldRoot values, and it
guarantees disjointness for EACH such pair individually.
Ranks and roots of old history nodes are unrestricted.

The produced daughters are consistent Henson finite TYPES,
not necessarily actual originals; their S-large cones later
carry actual coding vertices when S is restricted to coding
nodes. No claim about prescribed edges between them. -/
theorem rank_large_new_fan_after_labelled_history
    (S : Set (HensonOneType ell E))
    (n : Nat) (u : HensonOneType ell E)
    (hu : rank u = n + 1)
    (hLarge : RankLargeness.Large rank S (n + 1) u)
    (old : Finset
      (HensonOneType ell E × HensonOneType ell E))
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
        Disjoint (a.1.neighbours \ a.2.neighbours)
          (g.neighbours \ u.neighbours)) := by
  classical
  let cap : Nat := old.sup (fun p => p.1.level)
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
    obtain ⟨hzg, hgr, hgLarge⟩ := hMembers g hg
    exact ⟨le_trans huz hzg, hgr, hgLarge⟩
  have hSepU : ∀ g ∈ G, ∀ h ∈ G, g ≠ h →
      (¬ ∃ t : HensonOneType ell E, g ≤ t ∧ h ≤ t) ∧
      Disjoint (g.neighbours \ u.neighbours)
        (h.neighbours \ u.neighbours) := by
    intro g hg h hh hne
    obtain ⟨hNo, hDisjoint⟩ := hSep g hg h hh hne
    refine ⟨hNo, ?_⟩
    simpa only [z, zeroPad] using hDisjoint
  refine ⟨G, hCard, hMembersU, hSepU, ?_⟩
  intro a ha g hg
  have haBound : a.1.level ≤ H := by
    have hA : a.1.level ≤ cap :=
      Finset.le_sup
        (f := fun t :
          HensonOneType ell E × HensonOneType ell E =>
          t.1.level) ha
    have hCap : cap + 1 ≤ H := le_max_right _ _
    omega
  have hzg : z ≤ g := (hMembers g hg).1
  exact fresh_markers_disjoint_of_later_zeroPad
    a.2 a.1 u g H haBound (le_max_left _ _) hzg

end Kk.HensonOneType
