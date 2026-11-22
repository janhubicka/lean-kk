import Kk.TrackFSurvivorCanonical
import Kk.TrackFZeroCodeCutSurvivorAge
import Kk.TrackFCanonicalFullSupportBridge
import Kk.TrackFPairwiseTargetSeparation
import Mathlib.Tactic

/-!
# Track F: exact survivor deletion/reindexing for genuine Henson fronts

Audited English proof and hostile scope checks were committed FIRST:
docs/track_f_physical_survivor_canonical_delete_english_audit_20261122.md

The already verified normalized integer-witness reindexing theorem
commutes the COMPLETE canonical integer age with any injection of
surviving labelled sorts, whenever the raw bounds are
support-monotone. For genuine Henson prefix fronts the necessary
support monotonicity and the exact raw pullback identity are proved
from TRUE common-old-neighbour pools and directed clique capacities.

At a zero-code target cut c, this also identifies the FULL old
pre-code target age evaluated on survivor supports with the true
survivor age immediately AFTER reading the zero target coordinate
c, including all mixed/triple supports and arbitrary deleted j.

This does not yet establish equality to the prescribed OLD survivor
age R; that requires the independently verified source/target
synchronization endpoint class comparison. No full history/BRD claim.
-/

namespace Kk

/-- Literal physical raw age of the selected genuine Henson type
tuple u∘f equals the old raw age at the genuine image support f[U].
The proof identifies the ACTUAL common old-neighbour pools, never
assuming that either raw function is canonical or a graph age. -/
theorem trackFActualFront_raw_reindex
    {e d ell : Nat} (f : Fin e ↪ Fin d)
    (H : Nat) (E : Nat → Nat → Bool)
    (u : Fin d → HensonOneType ell E)
    (U : IntegerGraphSupport e ell) :
    trackFCommonRawAge e ell H E
        (fun i => (u (f i)).neighbours) U.1 =
    trackFCommonRawAge d ell H E
        (fun i => (u i).neighbours) (trackFMapSupport f U).1 := by
  classical
  have hPools :
      trackFCommonNeighbourPool e H
        (fun i => (u (f i)).neighbours) U.1 =
      trackFCommonNeighbourPool d H
        (fun i => (u i).neighbours) (U.1.image f) := by
    ext x
    simp only [trackFCommonNeighbourPool, Finset.mem_filter,
      Finset.mem_range]
    constructor
    · rintro ⟨hxH, hAll⟩
      refine ⟨hxH, ?_⟩
      intro k hk
      obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp hk
      subst k
      exact hAll i hi
    · rintro ⟨hxH, hAll⟩
      refine ⟨hxH, ?_⟩
      intro i hi
      exact hAll (f i)
        (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  unfold trackFCommonRawAge
  change ell - 1 - finiteDirectedCliqueCapacity E
      (trackFCommonNeighbourPool e H
        (fun i => (u (f i)).neighbours) U.1) =
    ell - 1 - finiteDirectedCliqueCapacity E
      (trackFCommonNeighbourPool d H
        (fun i => (u i).neighbours) (U.1.image f))
  rw [hPools]

/-- Exact NUMERIC canonical age reindexing of the COMPLETE physical
Henson type front, for an arbitrary injective labelled-sort map f.
This reuses the verified normalized integer-witness zero-extension
theorem and discharges its support-monotonicity premise from actual
physical common-neighbour capacities.

This is stronger than merely reindexing the raw age: equality holds
after FULL canonicalization on all survivor supports, even when
the omitted code coordinate imposes redundant mixed inequalities. -/
theorem trackFActualFront_canonical_reindex
    {e d ell : Nat} (f : Fin e ↪ Fin d)
    (hell : 0 < ell)
    (H : Nat) (E : Nat → Nat → Bool)
    (u : Fin d → HensonOneType ell E)
    (U : IntegerGraphSupport e ell) :
    integerGraphAgeCanonical e ell
      (fun T : IntegerGraphSupport e ell =>
        trackFCommonRawAge e ell H E
          (fun i => (u (f i)).neighbours) T.1) U =
    integerGraphAgeCanonical d ell
      (fun T : IntegerGraphSupport d ell =>
        trackFCommonRawAge d ell H E
          (fun i => (u i).neighbours) T.1)
      (trackFMapSupport f U) := by
  classical
  let B : IntegerGraphSupport d ell → Nat :=
    fun T => trackFCommonRawAge d ell H E
      (fun i => (u i).neighbours) T.1
  have hRaw :
      (fun T : IntegerGraphSupport e ell =>
        trackFCommonRawAge e ell H E
          (fun i => (u (f i)).neighbours) T.1) =
      trackFPullbackRaw f B := by
    funext T
    exact trackFActualFront_raw_reindex f H E u T
  have hMono : TrackFRawSupportMonotone d ell B := by
    intro S T hST
    exact trackFCommonRawAge_mono_support d ell H E
      (fun i => (u i).neighbours) S.1 T.1 hST
  rw [hRaw]
  exact trackFCanonical_reindex_mono f hell B hMono U

/-- Exact genuine immediate post-code survivor age with the correct
DELETION of the coded sort j and ORDER-PRESERVING survivor
reindexing f=Fin.succAboveEmb j.

Given a genuine FULL pre-code target front p on Fin(d+1) at level c,
and genuine later surviving target types t on Fin d, whose actual
prefixes at c have the same complete old-neighbour sets as the
selected pre-code survivors, if every later t_i has ZERO bit at c
then the full pre-code canonical age at f[U] equals the true
post-code survivor canonical age at the immediate prefix c+1.

This invokes physical canonical deletion/reindexing above and the
verified zero-cut survivor-age equality (#447). It does NOT assume
the reindexed pre-code profile equality as a premise.

The eventual equality to the prescribed old survivor age R and the
full code-event diary remain independent obligations. -/
theorem trackFActualFront_zero_code_survivor_canonical_reindex
    (d ell c : Nat) (E : Nat → Nat → Bool)
    (j : Fin (d + 1))
    (p : Fin (d + 1) → HensonOneType ell E)
    (hPreLevel : ∀ i, (p i).level = c)
    (later : Fin d → HensonOneType ell E)
    (hFuture : ∀ i, c + 1 ≤ (later i).level)
    (hZero : ∀ i, c ∉ (later i).neighbours)
    (hMatch : ∀ i : Fin d,
      (p (Fin.succAboveEmb j i)).neighbours =
        (HensonOneType.restrictPrefix (later i) c
          (by have h := hFuture i; omega)).neighbours)
    (U : IntegerGraphSupport d ell) :
    integerGraphAgeCanonical (d + 1) ell
      (fun T : IntegerGraphSupport (d + 1) ell =>
        trackFCommonRawAge (d + 1) ell c E
          (fun i => (p i).neighbours) T.1)
      (trackFMapSupport (Fin.succAboveEmb j) U) =
    integerGraphAgeCanonical d ell
      (fun T : IntegerGraphSupport d ell =>
        trackFCommonRawAge d ell (c + 1) E
          (fun i => (HensonOneType.restrictPrefix (later i)
            (c + 1) (hFuture i)).neighbours) T.1) U := by
  classical
  let f : Fin d ↪ Fin (d + 1) := Fin.succAboveEmb j
  have hFrontEq :
      (fun i : Fin d => p (f i)) =
      (fun i : Fin d => HensonOneType.restrictPrefix (later i) c
        (by have h := hFuture i; omega)) := by
    funext i
    apply HensonOneType.eq_of_level_neighbours
    · exact hPreLevel (f i)
    · exact hMatch i
  have hNeighboursEq :
      (fun i : Fin d => (p (f i)).neighbours) =
      (fun i : Fin d =>
        (HensonOneType.restrictPrefix (later i) c
          (by have h := hFuture i; omega)).neighbours) :=
    congrArg (fun v : Fin d → HensonOneType ell E =>
      fun i : Fin d => (v i).neighbours) hFrontEq
  have hReindex :=
    trackFActualFront_canonical_reindex f
      (by omega) c E p U
  have hZeroCut :=
    congrArg (fun a : IntegerGraphSupport d ell → Nat => a U)
      (trackFActualFront_canonical_eq_across_zero_cut
        d ell c E later hFuture hZero)
  calc
    integerGraphAgeCanonical (d + 1) ell
        (fun T : IntegerGraphSupport (d + 1) ell =>
          trackFCommonRawAge (d + 1) ell c E
            (fun i => (p i).neighbours) T.1)
        (trackFMapSupport (Fin.succAboveEmb j) U) =
      integerGraphAgeCanonical d ell
        (fun T : IntegerGraphSupport d ell =>
          trackFCommonRawAge d ell c E
            (fun i => (p (f i)).neighbours) T.1) U :=
      hReindex.symm
    _ = integerGraphAgeCanonical d ell
        (fun T : IntegerGraphSupport d ell =>
          trackFCommonRawAge d ell c E
            (fun i =>
              (HensonOneType.restrictPrefix (later i) c
                (by have h := hFuture i; omega)).neighbours) T.1) U := by
          rw [hNeighboursEq]
    _ = integerGraphAgeCanonical d ell
        (fun T : IntegerGraphSupport d ell =>
          trackFCommonRawAge d ell (c + 1) E
            (fun i =>
              (HensonOneType.restrictPrefix (later i) (c + 1)
                (hFuture i)).neighbours) T.1) U :=
      hZeroCut

end Kk
