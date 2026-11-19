import Kk.TrackFOriginalRefinedAgeSandwich
import Mathlib.Tactic

/-!
# Track F: private fresh markers preserve all raw source support bounds

The English proof and hostile audit were committed FIRST:
docs/track_f_same_rank_private_marker_raw_profile_english_audit_20261119.md

A source front refined coordinatewise at the SAME singleton rank, with
no newly positive old original shared by two distinct sorts, has
LITERALLY the same RAW clique-capacity bound on every nonempty sort
support. Mixed old common-neighbour pools are IDENTICAL; singleton
capacities agree because valid finite Henson types cannot saturate
rank's natural-number subtraction.

Composed with the verified original/refined target sandwich #399,
this removes a separate abstract raw-profile-equality hypothesis from
the conditional target finite-class/canonical-test transfer. The
actual construction of compatible target fronts with private markers
remains open. No global diary persistence or BRD lower bound.
-/

namespace Kk

/-- For genuine SAFE Henson types, equality of the zero-based singleton
rank forces equality of the ACTUAL old-neighbour directed clique
capacities. Safe types are crucial: both capacities are < ell-1,
so rank's Nat subtraction is not truncated at zero. -/
theorem trackFSameRank_oldNeighbourCapacity_eq
    (ell : Nat) (E : Nat → Nat → Bool)
    (u w : HensonOneType ell E)
    (hRank : HensonOneType.rank u = HensonOneType.rank w) :
    finiteDirectedCliqueCapacity E u.neighbours =
      finiteDirectedCliqueCapacity E w.neighbours := by
  have hSafeU :
      finiteDirectedCliqueCapacity E u.neighbours < ell - 1 :=
    (finitePoolCliqueCheck_false_iff_capacity_lt
      E (ell - 1) u.neighbours).mp u.safe
  have hSafeW :
      finiteDirectedCliqueCapacity E w.neighbours < ell - 1 :=
    (finitePoolCliqueCheck_false_iff_capacity_lt
      E (ell - 1) w.neighbours).mp w.safe
  dsimp [HensonOneType.rank, finiteHensonTypeRank] at hRank
  omega

/-- If new positive-neighbour markers are private to each sort,
the old and new actual common-old-neighbour pools on EVERY mixed
support containing at least two different sorts coincide LITERALLY.

The full chronological source-type extension preorder is needed:
it preserves old positive AND negative bits, rather than mere
set inclusion of positive neighbours. -/
theorem trackFCommonNeighbourPool_eq_of_private_new_markers
    (d ell m M : Nat)
    (E : Nat → Nat → Bool)
    (uOld uNew : Fin d → HensonOneType ell E)
    (hOldLevel : ∀ i, (uOld i).level = m)
    (hNewLevel : ∀ i, (uNew i).level = M)
    (hRefine : ∀ i, uOld i ≤ uNew i)
    (hPrivate : ∀ i j : Fin d, i ≠ j →
      ∀ x : Nat, m ≤ x →
        ¬ (x ∈ (uNew i).neighbours ∧
           x ∈ (uNew j).neighbours))
    (S : Finset (Fin d))
    (hMixed : ∃ i ∈ S, ∃ j ∈ S, i ≠ j) :
    trackFCommonNeighbourPool d M
      (fun i => (uNew i).neighbours) S =
    trackFCommonNeighbourPool d m
      (fun i => (uOld i).neighbours) S := by
  classical
  obtain ⟨i, hiS, j, hjS, hij⟩ := hMixed
  have hmM : m ≤ M := by
    have hLe := (hRefine i).1
    simpa only [hOldLevel i, hNewLevel i] using hLe
  ext x
  simp only [trackFCommonNeighbourPool, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨hxM, hAllNew⟩
    have hxOld : x < m := by
      by_contra hxNot
      have hxGe : m ≤ x := Nat.le_of_not_gt hxNot
      exact (hPrivate i j hij x hxGe)
        ⟨hAllNew i hiS, hAllNew j hjS⟩
    refine ⟨hxOld, ?_⟩
    intro k hk
    have hxOldK : x < (uOld k).level := by
      simpa only [hOldLevel k] using hxOld
    exact ((hRefine k).2 x hxOldK).mpr (hAllNew k hk)
  · rintro ⟨hxOld, hAllOld⟩
    refine ⟨lt_of_lt_of_le hxOld hmM, ?_⟩
    intro k hk
    have hxOldK : x < (uOld k).level := by
      simpa only [hOldLevel k] using hxOld
    exact ((hRefine k).2 x hxOldK).mp (hAllOld k hk)

/-- One direct all-support source-profile preservation theorem.
Chronological refinements with unchanged individual ranks and
pairwise-private fresh positive markers leave every NONEMPTY source
RAW support bound unchanged, even for triple and larger supports.

No target embedding, Henson left-density, rank-largeness or diary
geometry is assumed in this finite source-local lemma. -/
theorem trackFCommonRawAge_eq_of_same_rank_private_markers
    (d ell m M : Nat)
    (E : Nat → Nat → Bool)
    (uOld uNew : Fin d → HensonOneType ell E)
    (hOldLevel : ∀ i, (uOld i).level = m)
    (hNewLevel : ∀ i, (uNew i).level = M)
    (hRefine : ∀ i, uOld i ≤ uNew i)
    (hSameRank : ∀ i,
      HensonOneType.rank (uOld i) = HensonOneType.rank (uNew i))
    (hPrivate : ∀ i j : Fin d, i ≠ j →
      ∀ x : Nat, m ≤ x →
        ¬ (x ∈ (uNew i).neighbours ∧
           x ∈ (uNew j).neighbours)) :
    ∀ S : Finset (Fin d), S.Nonempty →
      trackFCommonRawAge d ell m E
        (fun i => (uOld i).neighbours) S =
      trackFCommonRawAge d ell M E
        (fun i => (uNew i).neighbours) S := by
  classical
  have hOldBelow :
      ∀ i x, x ∈ (uOld i).neighbours → x < m := by
    intro i x hx
    have hLt := (uOld i).below x hx
    simpa only [hOldLevel i] using hLt
  have hNewBelow :
      ∀ i x, x ∈ (uNew i).neighbours → x < M := by
    intro i x hx
    have hLt := (uNew i).below x hx
    simpa only [hNewLevel i] using hLt
  intro S hS
  obtain ⟨i, hiS⟩ := hS
  by_cases hSingleton : S = {i}
  · subst S
    have hCapEq :=
      trackFSameRank_oldNeighbourCapacity_eq
        ell E (uOld i) (uNew i) (hSameRank i)
    unfold trackFCommonRawAge
    rw [trackFCommonNeighbourPool_singleton
          d m (fun j => (uOld j).neighbours) hOldBelow i,
        trackFCommonNeighbourPool_singleton
          d M (fun j => (uNew j).neighbours) hNewBelow i,
        hCapEq]
  · have hOther : ∃ j ∈ S, j ≠ i := by
      by_contra hNone
      have hSubset : S ⊆ {i} := by
        intro j hj
        have hji : j = i := by
          by_contra hNe
          exact hNone ⟨j, hj, hNe⟩
        simp only [Finset.mem_singleton]
        exact hji
      have hS : S = {i} :=
        Finset.Subset.antisymm hSubset
          (Finset.singleton_subset_iff.mpr hiS)
      exact hSingleton hS
    obtain ⟨j, hjS, hij⟩ := hOther
    have hPoolEq :=
      trackFCommonNeighbourPool_eq_of_private_new_markers
        d ell m M E uOld uNew
        hOldLevel hNewLevel hRefine hPrivate S
        ⟨i, hiS, j, hjS, hij.symm⟩
    unfold trackFCommonRawAge
    rw [hPoolEq]

/-- The canonical finite-class source/target transfer from PR #399
now needs ONLY genuine same-rank refinements and private fresh positive
markers to preserve the original source profile.

The target prefix must contain images of old ORIGINAL positive
neighbours, not images of NEW markers. Rank-large actual target fibres
remain explicit premises, as does the target K_ell-free condition.

This is conditional on the existence of the refined target-compatible
tuple; it does NOT construct such a tuple or prove diary unavoidability.
-/
theorem trackFOriginalRefined_canonical_iff_of_private_markers
    (d ell m M H N : Nat) (hell : 2 ≤ ell)
    (Esrc Etgt B : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (uOld uNew : Fin d → HensonOneType ell Esrc)
    (v : Fin d → HensonOneType ell Etgt)
    (σ : Nat → Fin d)
    (hOldLevel : ∀ i, (uOld i).level = m)
    (hNewLevel : ∀ i, (uNew i).level = M)
    (hVLevel : ∀ i, (v i).level = H)
    (hRefine : ∀ i, uOld i ≤ uNew i)
    (hSameRank : ∀ i,
      HensonOneType.rank (uOld i) = HensonOneType.rank (uNew i))
    (hPrivate : ∀ i j : Fin d, i ≠ j →
      ∀ x : Nat, m ≤ x →
        ¬ (x ∈ (uNew i).neighbours ∧
           x ∈ (uNew j).neighbours))
    (hImageBelowOld : ∀ i c, c ∈ (uOld i).neighbours → e c < H)
    (hLargeNew : ∀ i,
      RankLargeness.Large HensonOneType.rank
        (HensonOneType.sourceCodingFibre (E := Esrc)
          Etgt e (v i))
        (HensonOneType.rank (uNew i)) (uNew i))
    (hSymB : ∀ i j, B i j = B j i)
    (hBFree : finitePoolCliqueCheck B ell (Finset.range N) = false) :
    (∀ C : Finset Nat,
      C ⊆ Finset.range N →
      IsDirectedCliqueOn B C →
      ∀ T : IntegerGraphSupport d ell,
        (C.filter (fun x => σ x ∈ T.1)).card ≤
          integerGraphAgeCanonical d ell
            (fun Q : IntegerGraphSupport d ell =>
              trackFCommonRawAge d ell m Esrc
                (fun i => (uOld i).neighbours) Q.1) T) ↔
    (∀ C : Finset Nat,
      C ⊆ Finset.range N →
      IsDirectedCliqueOn B C →
      ∀ T : IntegerGraphSupport d ell,
        (C.filter (fun x => σ x ∈ T.1)).card ≤
          integerGraphAgeCanonical d ell
            (fun Q : IntegerGraphSupport d ell =>
              trackFCommonRawAge d ell H Etgt
                (fun i => (v i).neighbours) Q.1) T) := by
  exact trackFOriginalRefined_source_target_canonical_full_support_iff
    d ell m M H N hell Esrc Etgt B hAvoid
    e he hInduced uOld uNew v σ
    hOldLevel hNewLevel hVLevel hRefine
    hImageBelowOld hLargeNew
    (trackFCommonRawAge_eq_of_same_rank_private_markers
      d ell m M Esrc uOld uNew hOldLevel hNewLevel
      hRefine hSameRank hPrivate)
    hSymB hBFree

end Kk
