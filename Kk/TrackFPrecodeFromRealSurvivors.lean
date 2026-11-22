import Kk.TrackFActualPrecodeTargetFront
import Kk.TrackFPrecodeEndpointAgeSandwich
import Kk.TrackFPhysicalSurvivorDeletion
import Mathlib.Tactic

/-!
# Track F: genuine pre-code image front from ONLY real surviving types

English proof and 17 adversarial checks were committed FIRST:
docs/track_f_precode_from_real_survivors_english_audit_20261122.md

The checked physical pre-code front constructor (#470) historically
accepted a full later family including a meaningless value for the
TERMINATED coding sort j. This theorem removes that artefact from the
PUBLIC API: the input later front is ONLY the d true survivors.

An internal Fin.insertNth supplies one irrelevant zero-padded old
code type for the older constructor's level check. The returned
genuine pre-code target front has its REAL code image old-column
type at c=e(x.level), full old target extension, injectivity, actual
rank-zero coded singleton and canonical age one; it is a genuine
integer age bounded by the old full age. The TRUE survivors extend
from their own pre-code prefixes to the given later target types.

No fabricated FUTURE coding branch survives in the conclusion, and
no age comparison of a dummy front is made. This does NOT itself
establish complete pre-code age equality or diary unavoidability.
-/

namespace Kk

/-- Construct a complete actual pre-code target type family from
exactly the REAL later surviving target family on Fin d.

The old target family on Fin(d+1) is genuine, common-level and
injective. The code node x is a TRUE source coding vertex in the
target fibre of old_j and old_j has zero-based rank 0.
The later REAL survivors, on Fin d under the order-preserving
embedding f=Fin.succAboveEmb j, extend the old survivor types,
reach one common target level H STRICTLY beyond c=e(x.level),
and have a TRUE zero target bit at c.

The output contains only:
 * a genuine actual target pre-code front at exactly c;
 * old<=pre and injectivity, true target coded prefix rank zero;
 * pre(f i)<=later_i and exact zero-cut old-neighbour identity;
 * the genuine complete pre-code canonical age below old,
   and the coded singleton's canonical value ONE.

No dummy later code type occurs in the statement/output. -/
theorem k4_precode_from_genuine_surviving_target_front
    (d m H : Nat)
    (Esrc Etgt : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily 4 (by decide) →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat)
    (old : Fin (d + 1) → HensonOneType 4 Etgt)
    (later : Fin d → HensonOneType 4 Etgt)
    (hOldLevel : ∀ i, (old i).level = m)
    (hOldInj : Function.Injective old)
    (j : Fin (d + 1))
    (x : HensonOneType 4 Esrc)
    (hxFibre : x ∈ HensonOneType.sourceCodingFibre
      (E := Esrc) Etgt e (old j))
    (hCodeRank : HensonOneType.rank (old j) = 0)
    (hLaterLevel : ∀ i, (later i).level = H)
    (hCut : e x.level < H)
    (hLaterExt : ∀ i, old (Fin.succAboveEmb j i) ≤ later i)
    (hLaterZero : ∀ i, e x.level ∉ (later i).neighbours) :
    ∃ pre : Fin (d + 1) → HensonOneType 4 Etgt,
      (∀ i, (pre i).level = e x.level ∧ old i ≤ pre i) ∧
      Function.Injective pre ∧
      HensonOneType.rank (pre j) = 0 ∧
      HensonOneType.IsCodingNode (pre j) ∧
      (∀ i : Fin d,
        pre (Fin.succAboveEmb j i) ≤ later i ∧
        (pre (Fin.succAboveEmb j i)).neighbours =
          (HensonOneType.restrictPrefix (later i) (e x.level + 1)
            (by rw [hLaterLevel i]; omega)).neighbours) ∧
      IsIntegerGraphAge (d + 1) 4
        (trackFPhysicalFrontCanonicalAge (d + 1) 4 (e x.level)
          Etgt pre) ∧
      AgeLe
        (trackFPhysicalFrontCanonicalAge (d + 1) 4 (e x.level)
          Etgt pre)
        (trackFPhysicalFrontCanonicalAge (d + 1) 4 m
          Etgt old) ∧
      trackFPhysicalFrontCanonicalAge (d + 1) 4 (e x.level)
        Etgt pre (trackFSingletonSupport (d + 1) 4 j (by decide)) =
          1 := by
  classical
  let c := e x.level
  have hmC : m ≤ c := by
    have hL := hxFibre.2.1
    simpa only [hOldLevel j] using hL
  have hmH : (old j).level ≤ H := by
    rw [hOldLevel j]
    omega
  let dummy : HensonOneType 4 Etgt :=
    HensonOneType.zeroPad (old j) H hmH
  let laterFull : Fin (d + 1) → HensonOneType 4 Etgt :=
    j.insertNth dummy later
  have hcH : c + 1 ≤ H := Nat.succ_le_of_lt hCut
  have hFutureFull :
      ∀ k : Fin (d + 1), c + 1 ≤ (laterFull k).level := by
    apply (Fin.forall_iff_succAbove
      (P := fun k : Fin (d + 1) => c + 1 ≤ (laterFull k).level) j).2
    constructor
    · simpa [laterFull, dummy, HensonOneType.zeroPad] using hcH
    · intro i
      simpa [laterFull, hLaterLevel i] using hcH
  have hOldExtFull :
      ∀ k : Fin (d + 1), k ≠ j → old k ≤ laterFull k := by
    intro k hk
    obtain ⟨i, hi⟩ :=
      Fin.exists_succAbove_eq (x := k) (y := j) hk
    subst k
    simpa [laterFull] using hLaterExt i
  have hZeroFull :
      ∀ k : Fin (d + 1), k ≠ j →
        c ∉ (laterFull k).neighbours := by
    intro k hk
    obtain ⟨i, hi⟩ :=
      Fin.exists_succAbove_eq (x := k) (y := j) hk
    subst k
    simpa [laterFull] using hLaterZero i
  obtain ⟨pre, hOldPre, hPreInj, hCodeRankNew, hActualCode,
    hFullSurvivors, hAge, hAgeLe, hCodeOne⟩ :=
    k4_construct_actual_precode_target_front
      (d + 1) m Esrc Etgt hAvoid e
      old laterFull hOldLevel hOldInj j x hxFibre hCodeRank
      hFutureFull hOldExtFull hZeroFull
  have hRealSurvivors :
      ∀ i : Fin d,
        pre (Fin.succAboveEmb j i) ≤ later i ∧
        (pre (Fin.succAboveEmb j i)).neighbours =
          (HensonOneType.restrictPrefix (later i) (c + 1)
            (by rw [hLaterLevel i]; omega)).neighbours := by
    intro i
    have hneq : Fin.succAboveEmb j i ≠ j := by
      simpa only [Fin.succAboveEmb_apply] using
        (Fin.succAbove_ne j i)
    obtain ⟨hExt, hBits⟩ :=
      hFullSurvivors (Fin.succAboveEmb j i) hneq
    have hAt : laterFull (Fin.succAboveEmb j i) = later i := by
      simp [laterFull]
    refine ⟨?_, ?_⟩
    · simpa only [hAt] using hExt
    · simpa only [hAt] using hBits
  exact ⟨pre, hOldPre, hPreInj,
    hCodeRankNew, hActualCode, hRealSurvivors,
    hAge, hAgeLe, hCodeOne⟩

end Kk
