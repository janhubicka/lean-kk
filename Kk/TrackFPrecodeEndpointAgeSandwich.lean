import Kk.TrackFTypePrefixCanonicalAgeSandwich
import Kk.TrackFActualFrontCanonicalAge
import Kk.TrackFZeroCodePreprofileRigidity
import Kk.TrackFSingletonCapacity
import Kk.TrackFCanonicalFullSupportBridge
import Mathlib.Tactic

/-!
# Track F: genuine endpoint age data force the full pre-code profile

English FIRST, 16 hostile checks:
docs/track_f_precode_endpoint_age_sandwich_english_audit_20261122.md

These are physical statements about three families of genuine
same-level chronological Henson one-types OLD <= PRE <= FAR.

If the complete OLD and FAR canonical integer ages agree on ALL
nonempty supports avoiding the coded sort j, then the genuine PRE
age agrees there too. No survivor-precode equality is assumed.

If the coded singleton has true zero-based rank zero at OLD/PRE and
the complete OLD canonical age satisfies the prescribed legal
zero-code erasure law, the verified full integer-age rigidity gives
the WHOLE PRE age equal to OLD, including all mixed triple supports.

The FAR j coordinate may be an unselected DUMMY zero continuation
of the terminated coded pre-type. This theorem DOES NOT claim a
future coded branch survives in the real diary; it is only
bookkeeping for full-support canonical comparison.

No old-to-far survivor endpoint equality is constructed here, and
no complete cover/split/code diary or BRD lower bound is claimed.
-/

namespace Kk

/-- The actual COMPLETE canonical normalized integer graph age of
a finite genuine Henson one-type front at one common old level.
The true old common-neighbour directed clique capacities are used;
there is no chosen shadow, support projection, or raw=canonical claim. -/
noncomputable def trackFPhysicalFrontCanonicalAge
    (d ell level : Nat)
    (E : Nat → Nat → Bool)
    (front : Fin d → HensonOneType ell E) :
    IntegerGraphSupport d ell → Nat :=
  integerGraphAgeCanonical d ell
    (fun T : IntegerGraphSupport d ell =>
      trackFCommonRawAge d ell level E
        (fun i => (front i).neighbours) T.1)

/-- The TRUE canonical singleton of a genuine Henson type whose
zero-based rank is zero has the manuscript rank-one value EXACTLY 1.
This uses true K_(ell-1)-free safety to avoid Nat subtraction
saturation and the verified normalized canonical singleton lemma,
not a claim of raw=canonical equality on mixed supports. -/
theorem trackFPhysicalFront_singleton_one_of_rank_zero
    (d ell m : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (front : Fin d → HensonOneType ell E)
    (hLevel : ∀ i, (front i).level = m)
    (j : Fin d) (hRank : HensonOneType.rank (front j) = 0) :
    trackFPhysicalFrontCanonicalAge d ell m E front
      (trackFSingletonSupport d ell j hell) = 1 := by
  classical
  have hBelow : ∀ i x, x ∈ (front i).neighbours → x < m := by
    intro i x hx
    have h := (front i).below x hx
    simpa only [hLevel i] using h
  have hSafe :
      finiteDirectedCliqueCapacity E (front j).neighbours < ell - 1 :=
    (finitePoolCliqueCheck_false_iff_capacity_lt
      E (ell - 1) (front j).neighbours).mp (front j).safe
  have hCap :
      finiteDirectedCliqueCapacity E (front j).neighbours = ell - 2 := by
    have hR := hRank
    change ell - 1 -
      finiteDirectedCliqueCapacity E (front j).neighbours - 1 = 0 at hR
    omega
  let B : IntegerGraphSupport d ell → Nat :=
    fun T => trackFCommonRawAge d ell m E
      (fun i => (front i).neighbours) T.1
  have hMono : TrackFRawSupportMonotone d ell B := by
    intro S T hST
    exact trackFCommonRawAge_mono_support
      d ell m E (fun i => (front i).neighbours)
      S.1 T.1 hST
  have hCapSingleton :
      B (trackFSingletonSupport d ell j hell) ≤ ell - 1 := by
    dsimp only [B, trackFCommonRawAge]
    omega
  have hRawSingleton :
      B (trackFSingletonSupport d ell j hell) = 1 := by
    change trackFCommonRawAge d ell m E
      (fun i => (front i).neighbours) {j} = 1
    unfold trackFCommonRawAge
    rw [trackFCommonNeighbourPool_singleton
      d m (fun i => (front i).neighbours) hBelow j]
    rw [hCap]
    omega
  change integerGraphAgeCanonical d ell B
    (trackFSingletonSupport d ell j hell) = 1
  exact (trackFCanonical_singleton_eq_raw
    d ell hell B hMono j hCapSingleton).trans hRawSingleton

/-- NONCIRCULAR genuine survivor-support sandwich.

Given three actual chronological families OLD <= PRE <= FAR and
their common levels m<=c<=H, their complete canonical ages obey
G_FAR <= G_PRE <= G_OLD on EVERY support. If OLD and FAR are known
to have the same canonical values on all supports avoiding j,
the intermediate actual pre-code front MUST have those values too.

No equality of the intermediate survivor profile is postulated. -/
theorem trackFActualFront_survivor_precode_age_eq_of_endpoint_eq
    (d ell m c H : Nat)
    (E : Nat → Nat → Bool) (j : Fin d)
    (hmC : m ≤ c) (hcH : c ≤ H)
    (old pre far : Fin d → HensonOneType ell E)
    (hOldLevel : ∀ i, (old i).level = m)
    (hPreLevel : ∀ i, (pre i).level = c)
    (hFarLevel : ∀ i, (far i).level = H)
    (hOldPre : ∀ i, old i ≤ pre i)
    (hPreFar : ∀ i, pre i ≤ far i)
    (hEnd : ∀ T : IntegerGraphSupport d ell,
      j ∉ T.1 →
      trackFPhysicalFrontCanonicalAge d ell H E far T =
        trackFPhysicalFrontCanonicalAge d ell m E old T) :
    ∀ T : IntegerGraphSupport d ell, j ∉ T.1 →
      trackFPhysicalFrontCanonicalAge d ell c E pre T =
        trackFPhysicalFrontCanonicalAge d ell m E old T := by
  have hPLe :
      AgeLe (trackFPhysicalFrontCanonicalAge d ell c E pre)
        (trackFPhysicalFrontCanonicalAge d ell m E old) :=
    trackFActualFront_canonical_antitone_of_extension
      d ell m c E hmC old pre hOldLevel hPreLevel hOldPre
  have hGLe :
      AgeLe (trackFPhysicalFrontCanonicalAge d ell H E far)
        (trackFPhysicalFrontCanonicalAge d ell c E pre) :=
    trackFActualFront_canonical_antitone_of_extension
      d ell c H E hcH pre far hPreLevel hFarLevel hPreFar
  intro T hjT
  apply Nat.le_antisymm (hPLe T)
  calc
    trackFPhysicalFrontCanonicalAge d ell m E old T =
        trackFPhysicalFrontCanonicalAge d ell H E far T :=
      (hEnd T hjT).symm
    _ ≤ trackFPhysicalFrontCanonicalAge d ell c E pre T :=
      hGLe T

/-- The TRUE complete PRE-code profile equals the genuine old
profile, with no hidden mixed-support decrease, provided:
(1) genuine OLD<=PRE<=FAR chronological fronts;
(2) ENDPOINT ages agree on all survivor supports T avoiding j;
(3) the old/pre code singleton Henson ranks are genuinely zero;
(4) the old canonical age obeys the full legal zero-code erasure
    law on every admissible mixed support containing j.

The intermediate survivor equality is DERIVED by the physical
age sandwich above and not assumed. The actual pre profile is
a genuine integer graph age by independently verified real-front
canonicalization (#436). The full zero-code rigidity is #430.

This proves the numeric AGE part of a pre-code event from checked
finite endpoint invariants. The later deletion/reindexing of
a true selected diary front and cover/split history remain open. -/
theorem trackFActualFront_full_precode_age_eq_of_zero_code_endpoints
    (d ell m c H : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool) (j : Fin d)
    (hmC : m ≤ c) (hcH : c ≤ H)
    (old pre far : Fin d → HensonOneType ell E)
    (hOldLevel : ∀ i, (old i).level = m)
    (hPreLevel : ∀ i, (pre i).level = c)
    (hFarLevel : ∀ i, (far i).level = H)
    (hOldPre : ∀ i, old i ≤ pre i)
    (hPreFar : ∀ i, pre i ≤ far i)
    (hEnd : ∀ T : IntegerGraphSupport d ell,
      j ∉ T.1 →
      trackFPhysicalFrontCanonicalAge d ell H E far T =
        trackFPhysicalFrontCanonicalAge d ell m E old T)
    (hOldRank : HensonOneType.rank (old j) = 0)
    (hPreRank : HensonOneType.rank (pre j) = 0)
    (hLegal : ∀ T : IntegerGraphSupport d ell,
      j ∈ T.1 → ∀ S : IntegerGraphSupport d ell,
        S.1 = T.1.erase j →
        trackFPhysicalFrontCanonicalAge d ell m E old T =
          trackFPhysicalFrontCanonicalAge d ell m E old S) :
    trackFPhysicalFrontCanonicalAge d ell c E pre =
      trackFPhysicalFrontCanonicalAge d ell m E old := by
  have hActualPre :
      IsIntegerGraphAge d ell
        (trackFPhysicalFrontCanonicalAge d ell c E pre) :=
    trackFActualFront_canonical_is_integer_graph_age
      d ell c hell E pre hPreLevel
  have hPreLe :
      AgeLe (trackFPhysicalFrontCanonicalAge d ell c E pre)
        (trackFPhysicalFrontCanonicalAge d ell m E old) :=
    trackFActualFront_canonical_antitone_of_extension
      d ell m c E hmC old pre hOldLevel hPreLevel hOldPre
  have hSurv :
      ∀ S : IntegerGraphSupport d ell, j ∉ S.1 →
        trackFPhysicalFrontCanonicalAge d ell c E pre S =
          trackFPhysicalFrontCanonicalAge d ell m E old S :=
    trackFActualFront_survivor_precode_age_eq_of_endpoint_eq
      d ell m c H E j hmC hcH old pre far
      hOldLevel hPreLevel hFarLevel hOldPre hPreFar hEnd
  have hPOne :
      ∀ T : IntegerGraphSupport d ell,
        T.1 = {j} →
        trackFPhysicalFrontCanonicalAge d ell c E pre T = 1 := by
    intro T hT
    have hTj : T = trackFSingletonSupport d ell j hell := by
      apply Subtype.ext
      exact hT
    subst T
    exact trackFPhysicalFront_singleton_one_of_rank_zero
      d ell c hell E pre hPreLevel j hPreRank
  have hFOne :
      ∀ T : IntegerGraphSupport d ell,
        T.1 = {j} →
        trackFPhysicalFrontCanonicalAge d ell m E old T = 1 := by
    intro T hT
    have hTj : T = trackFSingletonSupport d ell j hell := by
      apply Subtype.ext
      exact hT
    subst T
    exact trackFPhysicalFront_singleton_one_of_rank_zero
      d ell m hell E old hOldLevel j hOldRank
  exact integerGraphAge_zeroCode_preprofile_rigidity
    d ell j
    (trackFPhysicalFrontCanonicalAge d ell m E old)
    (trackFPhysicalFrontCanonicalAge d ell c E pre)
    hActualPre hPreLe hSurv hPOne hFOne hLegal

end Kk
