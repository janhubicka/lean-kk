import Kk.TrackFRealHensonTypeTree
import Mathlib.Tactic

/-!
# Track F: finite fans of mutually incompatible rank-large daughter cones

English-first proof and hostile audit:
docs/track_f_finite_rank_large_fan_english_audit.md

The underlying nodes are ACTUAL chronological Henson finite one-types.
The conclusion is a finite family of lower-rank rank-large cones that
are pairwise incompatible and whose positive old-neighbour markers
beyond the common root are pairwise disjoint. This uses zero-padding
and recursive largeness, NOT any published diary BRD characterization.

The rich finite multi-SORT gluing and source-target synchronization
remain separate open geometric obligations.
-/

namespace Kk.HensonOneType

variable {ell : Nat} {E : Nat → Nat → Bool}

/-- If two finite Henson types have the same chronological level
and a common later type, their complete old bit-columns coincide.
Their actual singleton ranks therefore agree. This uses both
positive and negative prefix preservation, not just set inclusion. -/
theorem rank_eq_of_same_level_common_extension
    (a b t : HensonOneType ell E)
    (hLevel : a.level = b.level)
    (hat : a ≤ t) (hbt : b ≤ t) :
    rank a = rank b := by
  have hab : a ≤ b := by
    refine ⟨by omega, ?_⟩
    intro x hx
    have hxb : x < b.level := by omega
    exact (hat.2 x hx).trans (hbt.2 x hxb).symm
  have hba : b ≤ a := by
    refine ⟨by omega, ?_⟩
    intro x hx
    have hxa : x < a.level := by omega
    exact (hbt.2 x hx).trans (hat.2 x hxa).symm
  exact Nat.le_antisymm (rank_antitone hba) (rank_antitone hab)

/-- Any lower-rank descendant v diverges from the all-zero
continuation of its ancestor u at the SAME height. Their cones
have no common extension; this is stronger than just v ≠ pad(u). -/
theorem zeroPad_incompatible_of_rank_drop
    (u v : HensonOneType ell E)
    (huv : u ≤ v) (hDrop : rank v < rank u) :
    ¬ ∃ t : HensonOneType ell E,
      v ≤ t ∧ zeroPad u v.level huv.1 ≤ t := by
  rintro ⟨t, hvt, hzt⟩
  have hEq :
      rank v = rank (zeroPad u v.level huv.1) :=
    rank_eq_of_same_level_common_extension
      v (zeroPad u v.level huv.1) t rfl hvt hzt
  rw [rank_zeroPad] at hEq
  omega

/-- Padding one fixed actual type to larger heights gives
compatible zero nodes, preserving every old positive and negative
bit. The two proof witnesses of the bounds are irrelevant. -/
theorem zeroPad_mono
    (u : HensonOneType ell E)
    (m n : Nat) (hum : u.level ≤ m)
    (hmn : m ≤ n) :
    zeroPad u m hum ≤ zeroPad u n (hum.trans hmn) := by
  exact ⟨hmn, fun _ _ => Iff.rfl⟩

/-- If w extends the zero-padding of u beyond the entire old
height of v, then v's positive markers *outside u* are disjoint
from w's new positive markers. The ranks of v,w are irrelevant. -/
theorem fresh_markers_disjoint_of_zeroPad
    (u v w : HensonOneType ell E)
    (m : Nat) (hvm : v.level ≤ m)
    (hum : u.level ≤ m)
    (hzw : zeroPad u m hum ≤ w) :
    Disjoint (v.neighbours \ u.neighbours)
      (w.neighbours \ u.neighbours) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxv hxw
  have hxvold : x ∈ v.neighbours := (Finset.mem_sdiff.mp hxv).1
  have hxnotu : x ∉ u.neighbours := (Finset.mem_sdiff.mp hxv).2
  have hxlt : x < m := lt_of_lt_of_le (v.below x hxvold) hvm
  have hxwnew : x ∈ w.neighbours := (Finset.mem_sdiff.mp hxw).1
  have hxpad : x ∈ (zeroPad u m hum).neighbours :=
    (hzw.2 x hxlt).mpr hxwnew
  change x ∈ u.neighbours at hxpad
  exact hxnotu hxpad

/-- Recursive largeness produces a NEW lower-rank large descendant,
avoiding the entire cones of any finite previously chosen lower-rank
family AND using disjoint fresh positive-neighbour markers.

The source set S need not be dense: its explicit positive-rank Large
hypothesis is the exact requirement. -/
theorem rank_large_fresh_daughter
    (S : Set (HensonOneType ell E))
    (n : Nat) (u : HensonOneType ell E)
    (hu : rank u = n + 1)
    (hLarge : RankLargeness.Large
      (fun t : HensonOneType ell E => rank t) S (n + 1) u)
    (F : Finset (HensonOneType ell E))
    (hFamily : ∀ v ∈ F, u ≤ v ∧ rank v = n) :
    ∃ w : HensonOneType ell E,
      u ≤ w ∧ rank w = n ∧
      RankLargeness.Large
        (fun t : HensonOneType ell E => rank t) S n w ∧
      (∀ v ∈ F, ¬ ∃ t : HensonOneType ell E,
        v ≤ t ∧ w ≤ t) ∧
      (∀ v ∈ F, Disjoint
        (v.neighbours \ u.neighbours)
        (w.neighbours \ u.neighbours)) := by
  classical
  let cap : Nat := F.sup (fun t => t.level)
  let m : Nat := max u.level (cap + 1)
  let z : HensonOneType ell E :=
    zeroPad u m (le_max_left _ _)
  have huz : u ≤ z :=
    le_zeroPad u m (le_max_left _ _)
  have hzrank : rank z = n + 1 := by
    calc
      rank z = rank u := rank_zeroPad u m (le_max_left _ _)
      _ = n + 1 := hu
  obtain ⟨w, hzw, hwrank, hwLarge⟩ := hLarge z huz hzrank
  have huw : u ≤ w := le_trans huz hzw
  refine ⟨w, huw, hwrank, hwLarge, ?_, ?_⟩
  · intro v hvF
    obtain ⟨huv, hvrank⟩ := hFamily v hvF
    have hvm : v.level ≤ m := by
      have hc : v.level ≤ cap :=
        Finset.le_sup
          (f := fun t : HensonOneType ell E => t.level) hvF
      have hmcap : cap + 1 ≤ m := le_max_right _ _
      omega
    have hPadLe :
        zeroPad u v.level huv.1 ≤ z := by
      exact ⟨hvm, fun _ _ => Iff.rfl⟩
    intro hCommon
    obtain ⟨t, hvt, hwt⟩ := hCommon
    have hPadT :
        zeroPad u v.level huv.1 ≤ t :=
      le_trans hPadLe (le_trans hzw hwt)
    have hDrop : rank v < rank u := by omega
    exact (zeroPad_incompatible_of_rank_drop u v huv hDrop)
      ⟨t, hvt, hPadT⟩
  · intro v hvF
    have hvm : v.level ≤ m := by
      have hc : v.level ≤ cap :=
        Finset.le_sup
          (f := fun t : HensonOneType ell E => t.level) hvF
      have hmcap : cap + 1 ≤ m := le_max_right _ _
      omega
    exact fresh_markers_disjoint_of_zeroPad
      u v w m hvm (le_max_left _ _) hzw

/-- Arbitrarily many lower-rank rank-large descendants can be
chosen simultaneously: their cones are pairwise incompatible AND
their positive fresh-marker sets are pairwise disjoint.

This is a finite FAN theorem for ONE actual Henson type, not
simultaneous richness of unrelated source types. -/
theorem rank_large_finite_fan
    (S : Set (HensonOneType ell E))
    (n : Nat) (u : HensonOneType ell E)
    (hu : rank u = n + 1)
    (hLarge : RankLargeness.Large
      (fun t : HensonOneType ell E => rank t) S (n + 1) u) :
    ∀ k : Nat, ∃ F : Finset (HensonOneType ell E),
      F.card = k ∧
      (∀ v ∈ F, u ≤ v ∧ rank v = n ∧
        RankLargeness.Large
          (fun t : HensonOneType ell E => rank t) S n v) ∧
      (∀ v ∈ F, ∀ w ∈ F, v ≠ w →
        (¬ ∃ t : HensonOneType ell E, v ≤ t ∧ w ≤ t) ∧
        Disjoint
          (v.neighbours \ u.neighbours)
          (w.neighbours \ u.neighbours)) := by
  classical
  intro k
  induction k with
  | zero =>
      refine ⟨∅, by simp, ?_, ?_⟩
      · intro v hv
        exact False.elim (Finset.not_mem_empty v hv)
      · intro v hv
        exact False.elim (Finset.not_mem_empty v hv)
  | succ k ih =>
      obtain ⟨F, hCard, hMembers, hSep⟩ := ih
      have hFamily : ∀ v ∈ F, u ≤ v ∧ rank v = n := by
        intro v hv
        obtain ⟨huv, hvrank, _⟩ := hMembers v hv
        exact ⟨huv, hvrank⟩
      obtain ⟨w, huw, hwrank, hwLarge, hNo, hMark⟩ :=
        rank_large_fresh_daughter S n u hu hLarge F hFamily
      have hwNot : w ∉ F := by
        intro hwF
        exact (hNo w hwF) ⟨w, le_refl w, le_refl w⟩
      refine ⟨insert w F, ?_, ?_, ?_⟩
      · simp [hwNot, hCard]
      · intro v hv
        rcases Finset.mem_insert.mp hv with hvw | hvF
        · subst v
          exact ⟨huw, hwrank, hwLarge⟩
        · exact hMembers v hvF
      · intro v hv z hz hvz
        rcases Finset.mem_insert.mp hv with hvw | hvF
        · subst v
          rcases Finset.mem_insert.mp hz with hzw | hzF
          · exact False.elim (hvz hzw.symm)
          · constructor
            · rintro ⟨t, hwt, hzt⟩
              exact (hNo z hzF) ⟨t, hzt, hwt⟩
            · exact (hMark z hzF).symm
        · rcases Finset.mem_insert.mp hz with hzw | hzF
          · subst z
            exact ⟨hNo v hvF, hMark v hvF⟩
          · exact hSep v hvF z hzF hvz

end Kk.HensonOneType
