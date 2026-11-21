import Kk.TrackFExactTargetPrefixRestriction
import Kk.TrackFMultiSortRawIsolation
import Kk.IntegerAgeUniversalProperties
import Mathlib.Tactic

/-!
# Track F: zero at the actual code cut preserves the survivor graph age

English-first mathematical proof and 15 hostile checks:
docs/track_f_immediate_postcode_zero_survivor_age_english_audit_20261121.md

If EVERY genuine surviving target one-type has ZERO ordinary bit
at the coded target original cut c, its true prefixes immediately
before and after that cut have the SAME old positive-neighbour
sets. Thus on every nonempty support their old common-neighbour
pools, raw clique capacities and normalized integer canonical ages
are exactly the same. This rules out a concealed mixed/triple
survivor age jump AT the code coordinate.

The zero target bits themselves are provided by verified #433.
This is NOT precode full-age identification, split/cover history,
diary unavoidability or a BRD statement.
-/

namespace Kk

/-- If the true target old bit at c is zero, the positive-neighbour
sets of the exact genuine prefix types at c and c+1 are IDENTICAL. -/
theorem trackFRestrictPrefix_zero_cut_neighbours_eq
    (ell c : Nat) (E : Nat → Nat → Bool)
    (t : HensonOneType ell E)
    (hNext : c + 1 ≤ t.level)
    (hZero : c ∉ t.neighbours) :
    (HensonOneType.restrictPrefix t c (by omega)).neighbours =
      (HensonOneType.restrictPrefix t (c + 1) hNext).neighbours := by
  classical
  ext x
  simp only [HensonOneType.restrictPrefix, Finset.mem_filter]
  constructor
  · rintro ⟨hx, hxc⟩
    exact ⟨hx, by omega⟩
  · rintro ⟨hx, hxc⟩
    have hxNe : x ≠ c := by
      intro hEq
      subst x
      exact hZero hx
    exact ⟨hx, by omega⟩

/-- Every nonempty common-neighbour pool is unchanged when the
physical chronological cutoff grows by ONE coordinate, provided
all old positive-neighbour sets already lie strictly below the
earlier cutoff. The EMPTY support is excluded: its pool grows. -/
theorem trackFCommonNeighbourPool_zero_cut_eq
    (d c : Nat)
    (U : Fin d → Finset Nat)
    (hBelow : ∀ i x, x ∈ U i → x < c)
    (S : Finset (Fin d)) (hS : S.Nonempty) :
    trackFCommonNeighbourPool d c U S =
      trackFCommonNeighbourPool d (c + 1) U S := by
  classical
  obtain ⟨i, hi⟩ := hS
  ext x
  simp only [trackFCommonNeighbourPool, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨hxc, hAll⟩
    exact ⟨by omega, hAll⟩
  · rintro ⟨hxc, hAll⟩
    exact ⟨hBelow i x (hAll i hi), hAll⟩

/-- COMPLETE RAW all-support survivor age equality at an ACTUAL
zero code cut c, comparing exact genuine target prefix
types just before and just after that one original coordinate.

No symmetry, target embedding or abstract diary premise is used. -/
theorem trackFActualFront_raw_eq_across_zero_cut
    (d ell c : Nat) (E : Nat → Nat → Bool)
    (t : Fin d → HensonOneType ell E)
    (hFuture : ∀ i, c + 1 ≤ (t i).level)
    (hZero : ∀ i, c ∉ (t i).neighbours) :
    ∀ S : Finset (Fin d), S.Nonempty →
      trackFCommonRawAge d ell c E
        (fun i => (HensonOneType.restrictPrefix (t i)
          c (by have h := hFuture i; omega)).neighbours) S =
      trackFCommonRawAge d ell (c + 1) E
        (fun i => (HensonOneType.restrictPrefix (t i)
          (c + 1) (hFuture i)).neighbours) S := by
  classical
  let p : Fin d → HensonOneType ell E :=
    fun i => HensonOneType.restrictPrefix (t i) c
      (by have h := hFuture i; omega)
  let q : Fin d → HensonOneType ell E :=
    fun i => HensonOneType.restrictPrefix (t i) (c + 1)
      (hFuture i)
  have hN : (fun i => (p i).neighbours) =
      (fun i => (q i).neighbours) := by
    funext i
    exact trackFRestrictPrefix_zero_cut_neighbours_eq
      ell c E (t i) (hFuture i) (hZero i)
  have hBelow : ∀ i x, x ∈ (p i).neighbours → x < c := by
    intro i x hx
    exact (p i).below x hx
  intro S hS
  change trackFCommonRawAge d ell c E
      (fun i => (p i).neighbours) S =
    trackFCommonRawAge d ell (c + 1) E
      (fun i => (q i).neighbours) S
  unfold trackFCommonRawAge
  rw [trackFCommonNeighbourPool_zero_cut_eq
      d c (fun i => (p i).neighbours) hBelow S hS,
      hN]

/-- The canonical normalized integer graph-age of all ACTUAL
surviving target prefix types is exactly unchanged across the
selected original at c, if every survivor's bit at c is zero.
Includes arbitrary mixed/triple supports and their all-clique
canonical constraints, not just their singleton shadows.

This supplies the IMMEDIATE POSTCODE survivor no-jump ingredient,
conditional on the true zero target bits from verified #433. -/
theorem trackFActualFront_canonical_eq_across_zero_cut
    (d ell c : Nat) (E : Nat → Nat → Bool)
    (t : Fin d → HensonOneType ell E)
    (hFuture : ∀ i, c + 1 ≤ (t i).level)
    (hZero : ∀ i, c ∉ (t i).neighbours) :
    integerGraphAgeCanonical d ell
      (fun S : IntegerGraphSupport d ell =>
        trackFCommonRawAge d ell c E
          (fun i => (HensonOneType.restrictPrefix (t i)
            c (by have h := hFuture i; omega)).neighbours) S.1) =
    integerGraphAgeCanonical d ell
      (fun S : IntegerGraphSupport d ell =>
        trackFCommonRawAge d ell (c + 1) E
          (fun i => (HensonOneType.restrictPrefix (t i)
            (c + 1) (hFuture i)).neighbours) S.1) := by
  have hRaw :
      (fun S : IntegerGraphSupport d ell =>
        trackFCommonRawAge d ell c E
          (fun i => (HensonOneType.restrictPrefix (t i)
            c (by have h := hFuture i; omega)).neighbours) S.1) =
      (fun S : IntegerGraphSupport d ell =>
        trackFCommonRawAge d ell (c + 1) E
          (fun i => (HensonOneType.restrictPrefix (t i)
            (c + 1) (hFuture i)).neighbours) S.1) := by
    funext S
    exact trackFActualFront_raw_eq_across_zero_cut
      d ell c E t hFuture hZero S.1 S.2.1
  exact congrArg (integerGraphAgeCanonical d ell) hRaw

end Kk
