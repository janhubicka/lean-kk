import Kk.TrackFMultiSortRawIsolation
import Kk.TrackFRealHensonTypeTree
import Kk.IntegerAgeUniversalProperties
import Mathlib.Tactic

/-!
# Track F: actual chronological Henson front ages are antitone

English proof and hostile audit committed FIRST:
docs/track_f_type_prefix_canonical_age_sandwich_english_audit_20261121.md

Full genuine Henson one-type extensions enlarge ALL old common
positive-neighbour pools, so their RAW mixed clique ages decrease.
The normalized integer-witness canonicalizer is monotone under
pointwise raw bounds. Hence the COMPLETE canonical graph-age profile
decreases along any actual chronological front extension.

Equality at two checkpoints forces equality at EVERY intermediate
front by the exact full-support sandwich argument. This is the
"no hidden age changes" step for a code/split history, conditional
on actual endpoint equality. No diary or big Ramsey claim.
-/

namespace Kk

/-- The normalized integer-witness canonicalizer is monotone:
if B is pointwise no larger than C, every finite normalized clique
vector feasible under B is also feasible under C, so its complete
support-wise maximal witnesses are no larger.

No positivity or consistency of the RAW B,C is needed. -/
theorem integerGraphAgeCanonical_mono_raw
    (d ell : Nat)
    (B C : IntegerGraphSupport d ell → Nat)
    (hBC : AgeLe B C) :
    AgeLe
      (integerGraphAgeCanonical d ell B)
      (integerGraphAgeCanonical d ell C) := by
  classical
  intro T
  let value :=
    integerCliqueOnSupport (d := d) (ell := ell)
  change (Finset.univ.filter (WitnessRespects value B)).sup
      (fun w => value w T) ≤
    integerGraphAgeCanonical d ell C T
  apply Finset.sup_le
  intro w hw
  have hwB : WitnessRespects value B w :=
    (Finset.mem_filter.mp hw).2
  have hwC : WitnessRespects value C w := by
    intro S
    exact (hwB S).trans (hBC S)
  exact witnessValue_le_canonical value C w hwC T

/-- The old genuine common-neighbour pool on any nonempty sort
support is a subset of the later common pool under complete
chronological source Henson one-type extensions. Therefore
the actual source RAW bound at the later common level is NO
GREATER than the old RAW bound on every support.

This holds at arbitrary ell, without symmetry of E; the explicit
m≤M hypothesis handles the empty d case without choosing a sort. -/
theorem trackFActualFront_raw_antitone_of_extension
    (d ell m M : Nat)
    (E : Nat → Nat → Bool)
    (hmM : m ≤ M)
    (u w : Fin d → HensonOneType ell E)
    (hOldLevel : ∀ i, (u i).level = m)
    (_hNewLevel : ∀ i, (w i).level = M)
    (hExt : ∀ i, u i ≤ w i) :
    ∀ S : Finset (Fin d), S.Nonempty →
      trackFCommonRawAge d ell M E
        (fun i => (w i).neighbours) S ≤
      trackFCommonRawAge d ell m E
        (fun i => (u i).neighbours) S := by
  classical
  intro S _hS
  have hSub :
      trackFCommonNeighbourPool d m
        (fun i => (u i).neighbours) S ⊆
      trackFCommonNeighbourPool d M
        (fun i => (w i).neighbours) S := by
    intro x hx
    have hxOld : x < m ∧
        ∀ i ∈ S, x ∈ (u i).neighbours := by
      simpa only [trackFCommonNeighbourPool,
        Finset.mem_filter, Finset.mem_range] using hx
    change x ∈ (Finset.range M).filter
      (fun y => ∀ i ∈ S, y ∈ (w i).neighbours)
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr
        (lt_of_lt_of_le hxOld.1 hmM), ?_⟩
    intro i hi
    have hxLt : x < (u i).level := by
      simpa only [hOldLevel i] using hxOld.1
    exact ((hExt i).2 x hxLt).mp (hxOld.2 i hi)
  have hCapMono :=
    finiteDirectedCliqueCapacity_mono E
      (trackFCommonNeighbourPool d m
        (fun i => (u i).neighbours) S)
      (trackFCommonNeighbourPool d M
        (fun i => (w i).neighbours) S) hSub
  change ell - 1 - finiteDirectedCliqueCapacity E
      (trackFCommonNeighbourPool d M
        (fun i => (w i).neighbours) S) ≤
    ell - 1 - finiteDirectedCliqueCapacity E
      (trackFCommonNeighbourPool d m
        (fun i => (u i).neighbours) S)
  omega

/-- The complete canonical normalized integer graph-age profile
is antitone under ANY genuine coordinatewise chronological Henson
one-type extension of common-level fronts. In particular this
controls mixed triple supports, not merely the singleton shadow.

No assumption that the raw bounds equal their canonicalizations. -/
theorem trackFActualFront_canonical_antitone_of_extension
    (d ell m M : Nat)
    (E : Nat → Nat → Bool)
    (hmM : m ≤ M)
    (u w : Fin d → HensonOneType ell E)
    (hOldLevel : ∀ i, (u i).level = m)
    (hNewLevel : ∀ i, (w i).level = M)
    (hExt : ∀ i, u i ≤ w i) :
    AgeLe
      (integerGraphAgeCanonical d ell
        (fun T : IntegerGraphSupport d ell =>
          trackFCommonRawAge d ell M E
            (fun i => (w i).neighbours) T.1))
      (integerGraphAgeCanonical d ell
        (fun T : IntegerGraphSupport d ell =>
          trackFCommonRawAge d ell m E
            (fun i => (u i).neighbours) T.1)) := by
  apply integerGraphAgeCanonical_mono_raw d ell
  intro T
  exact trackFActualFront_raw_antitone_of_extension
    d ell m M E hmM u w hOldLevel hNewLevel hExt
    T.1 T.2.1

/-- A full-support no-hidden-age-change sandwich:
if actual type fronts u≤p≤w appear at successive chronological
common levels m≤h≤M, the exact canonical intermediate profile
lies between the two endpoint profiles. If endpoints coincide,
the whole intermediate profile equals the original profile.

This theorem supplies the algebraic checkpoint rigidity for a
code or split history. Establishing actual endpoint equality and
the correct intermediate selected branch front are separate tasks. -/
theorem trackFActualFront_canonical_sandwich_eq
    (d ell m h M : Nat)
    (E : Nat → Nat → Bool)
    (hmH : m ≤ h) (hhM : h ≤ M)
    (u p w : Fin d → HensonOneType ell E)
    (hULevel : ∀ i, (u i).level = m)
    (hPLevel : ∀ i, (p i).level = h)
    (hWLevel : ∀ i, (w i).level = M)
    (hUP : ∀ i, u i ≤ p i)
    (hPW : ∀ i, p i ≤ w i)
    (hEndpoints :
      (integerGraphAgeCanonical d ell
        (fun T : IntegerGraphSupport d ell =>
          trackFCommonRawAge d ell m E
            (fun i => (u i).neighbours) T.1)) =
      (integerGraphAgeCanonical d ell
        (fun T : IntegerGraphSupport d ell =>
          trackFCommonRawAge d ell M E
            (fun i => (w i).neighbours) T.1))) :
    (integerGraphAgeCanonical d ell
      (fun T : IntegerGraphSupport d ell =>
        trackFCommonRawAge d ell h E
          (fun i => (p i).neighbours) T.1)) =
    (integerGraphAgeCanonical d ell
      (fun T : IntegerGraphSupport d ell =>
        trackFCommonRawAge d ell m E
          (fun i => (u i).neighbours) T.1)) := by
  have hMiddleOld :=
    trackFActualFront_canonical_antitone_of_extension
      d ell m h E hmH u p hULevel hPLevel hUP
  have hNewMiddle :=
    trackFActualFront_canonical_antitone_of_extension
      d ell h M E hhM p w hPLevel hWLevel hPW
  funext T
  apply Nat.le_antisymm (hMiddleOld T)
  calc
    integerGraphAgeCanonical d ell
        (fun S : IntegerGraphSupport d ell =>
          trackFCommonRawAge d ell m E
            (fun i => (u i).neighbours) S.1) T =
      integerGraphAgeCanonical d ell
        (fun S : IntegerGraphSupport d ell =>
          trackFCommonRawAge d ell M E
            (fun i => (w i).neighbours) S.1) T :=
      congrArg (fun f : IntegerGraphSupport d ell → Nat => f T)
        hEndpoints
    _ ≤ integerGraphAgeCanonical d ell
        (fun S : IntegerGraphSupport d ell =>
          trackFCommonRawAge d ell h E
            (fun i => (p i).neighbours) S.1) T :=
      hNewMiddle T

end Kk
