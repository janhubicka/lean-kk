import Kk.TrackFPhysicalNumericAgeFromClasses
import Kk.TrackFPhysicalSurvivorDeletion
import Kk.TrackFZeroCodeSurvivorSynchronization
import Mathlib.Tactic

/-!
# Track F: real target survivor NUMERIC endpoint equality after code

English mathematical proof and 18 hostile checks committed FIRST:
docs/track_f_numeric_survivor_endpoint_from_full_checkpoint_english_audit_20261122.md

From a FULL previous source–target genuine canonical numeric age
equality on d+1 distinct source sorts, restrict BOTH real source
and target ages along f=Fin.succAboveEmb j, preserving ALL surviving
supports by the checked physical canonical reindexing theorem (#475).

Then apply the independently kernel-checked TRUE source/target
K4 survivor resynchronization after an actual code original r
(#433), and its complete finite-class→NUMERIC extraction (#482).
The source old-survivor age matches the later TARGET survivor age,
while the full previous checkpoint restricts the same source age
to the OLD TARGET survivor age. This yields the exact NUMERIC
OLD TARGET versus LATER TARGET survivor endpoint equality needed
by genuine no-dummy pre-code age rigidity (#488).

All target types/fibres/zero images are real; no order-preserving
source→target embedding, redundant RAW bound equality, fictitious
future coded branch, or global diary/BRD theorem is assumed.
-/

namespace Kk

/-- The actual surviving TARGET canonical age is numerically
unchanged between a previous FULL source–target checkpoint and
the TRUE after-code survivor front constructed from the ORIGINAL
source survivor types.

The initial full source and target types on Fin(d+1) need not have
identical original levels and the induced index map e need NOT
preserve chronological order. The full source–target old age
equality is an EXPLICIT genuine induction invariant; initial
individual rank compatibility alone would not suffice.

The deleted sort j is omitted by the EXACT order-preserving
target-labelled injection f=Fin.succAboveEmb j. All mixed/triple
canonical survivor ages are preserved NUMERICALLY, without
asserting equality of possibly redundant old RAW tables.

Retains ACTUAL source/target continuation types at common later
levels, true target zero bit at e(r), actual coding fibre largeness
and target survivor injectivity. The code original r must be
genuinely after the old source level, as ensured by actual code
selection #424. No dummy future coded branch occurs. -/
theorem k4_survivor_target_numeric_endpoint_of_full_checkpoint
    (d ms mt r cutoff : Nat) (hmsr : ms ≤ r)
    (Esrc Etgt : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily 4 (by decide) →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (u : Fin (d + 1) → HensonOneType 4 Esrc)
    (v : Fin (d + 1) → HensonOneType 4 Etgt)
    (huLevel : ∀ i, (u i).level = ms)
    (hvLevel : ∀ i, (v i).level = mt)
    (huInj : Function.Injective u)
    (hRank : ∀ i, HensonOneType.rank (v i) =
      HensonOneType.rank (u i))
    (hLarge : ∀ i,
      RankLargeness.Large HensonOneType.rank
        (HensonOneType.sourceCodingFibre (E := Esrc) Etgt e (v i))
        (HensonOneType.rank (u i)) (u i))
    (hFullCheckpointAge :
      trackFPhysicalFrontCanonicalAge (d + 1) 4 ms Esrc u =
      trackFPhysicalFrontCanonicalAge (d + 1) 4 mt Etgt v)
    (j : Fin (d + 1)) :
    ∃ H M : Nat,
    ∃ w : Fin d → HensonOneType 4 Esrc,
    ∃ t : Fin d → HensonOneType 4 Etgt,
      cutoff < H ∧ e r < H ∧
      (∀ i : Fin d,
        (w i).level = M ∧
        u (Fin.succAboveEmb j i) ≤ w i ∧
        HensonOneType.rank (w i) =
          HensonOneType.rank (u (Fin.succAboveEmb j i)) ∧
        r < (w i).level ∧ r ∉ (w i).neighbours) ∧
      (∀ i : Fin d,
        v (Fin.succAboveEmb j i) ≤ t i ∧
        (t i).level = H ∧
        HensonOneType.rank (t i) =
          HensonOneType.rank (u (Fin.succAboveEmb j i)) ∧
        RankLargeness.Large HensonOneType.rank
          (HensonOneType.sourceCodingFibre (E := Esrc) Etgt e (t i))
          (HensonOneType.rank (w i)) (w i) ∧
        e r ∉ (t i).neighbours) ∧
      Function.Injective t ∧
      trackFPhysicalFrontCanonicalAge d 4 mt Etgt
        (fun i => v (Fin.succAboveEmb j i)) =
      trackFPhysicalFrontCanonicalAge d 4 H Etgt t := by
  classical
  let f : Fin d ↪ Fin (d + 1) := Fin.succAboveEmb j
  let uS : Fin d → HensonOneType 4 Esrc := fun i => u (f i)
  let vS : Fin d → HensonOneType 4 Etgt := fun i => v (f i)
  have huSLevel : ∀ i, (uS i).level = ms :=
    fun i => huLevel (f i)
  have huSInj : Function.Injective uS := by
    intro i k hik
    exact f.injective (huInj hik)
  have hRankS : ∀ i, HensonOneType.rank (vS i) =
      HensonOneType.rank (uS i) :=
    fun i => hRank (f i)
  have hLargeS : ∀ i,
      RankLargeness.Large HensonOneType.rank
        (HensonOneType.sourceCodingFibre (E := Esrc) Etgt e (vS i))
        (HensonOneType.rank (uS i)) (uS i) :=
    fun i => hLarge (f i)
  obtain ⟨H, M, w, t, hCut, hrCut, hwValid, htValid,
    htInjective, _hRawSame, hFiniteTests⟩ :=
    k4_survivor_sync_after_zero_code
      d ms r cutoff hmsr Esrc Etgt
      hAvoid e he hInduced uS vS
      huSLevel huSInj hRankS hLargeS
  have htLevel : ∀ i : Fin d, (t i).level = H :=
    fun i => (htValid i).2.1
  have hSourceLater :
      trackFPhysicalFrontCanonicalAge d 4 ms Esrc uS =
      trackFPhysicalFrontCanonicalAge d 4 H Etgt t :=
    trackFPhysical_numeric_age_eq_of_full_K4_tests
      d ms H Esrc Etgt uS t
      huSLevel htLevel hFiniteTests
  have hSourceOldTarget :
      trackFPhysicalFrontCanonicalAge d 4 ms Esrc uS =
      trackFPhysicalFrontCanonicalAge d 4 mt Etgt vS := by
    funext T
    have hSourcePull :
        trackFPhysicalFrontCanonicalAge d 4 ms Esrc uS T =
        trackFPhysicalFrontCanonicalAge (d + 1) 4 ms Esrc u
          (trackFMapSupport f T) :=
      trackFActualFront_canonical_reindex f
        (by decide) ms Esrc u T
    have hTargetPull :
        trackFPhysicalFrontCanonicalAge d 4 mt Etgt vS T =
        trackFPhysicalFrontCanonicalAge (d + 1) 4 mt Etgt v
          (trackFMapSupport f T) :=
      trackFActualFront_canonical_reindex f
        (by decide) mt Etgt v T
    calc
      trackFPhysicalFrontCanonicalAge d 4 ms Esrc uS T =
          trackFPhysicalFrontCanonicalAge (d + 1) 4 ms Esrc u
            (trackFMapSupport f T) := hSourcePull
      _ = trackFPhysicalFrontCanonicalAge (d + 1) 4 mt Etgt v
            (trackFMapSupport f T) :=
        congrArg
          (fun A : IntegerGraphSupport (d + 1) 4 → Nat =>
            A (trackFMapSupport f T))
          hFullCheckpointAge
      _ = trackFPhysicalFrontCanonicalAge d 4 mt Etgt vS T :=
        hTargetPull.symm
  have hOldTargetLater :
      trackFPhysicalFrontCanonicalAge d 4 mt Etgt vS =
      trackFPhysicalFrontCanonicalAge d 4 H Etgt t :=
    hSourceOldTarget.symm.trans hSourceLater
  exact ⟨H, M, w, t, hCut, hrCut,
    hwValid, htValid, htInjective, hOldTargetLater⟩

end Kk
