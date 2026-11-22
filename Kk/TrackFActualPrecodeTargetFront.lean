import Kk.TrackFNonrootActualTargetFibre
import Kk.TrackFZeroCodeCutSurvivorAge
import Kk.TrackFActualFrontCanonicalAge
import Kk.TrackFTypePrefixCanonicalAgeSandwich
import Kk.TrackFSingletonCapacity
import Kk.TrackFPairwiseTargetSeparation
import Mathlib.Tactic

/-!
# Track F: genuine complete pre-code target front at the actual image cut

English FIRST and hostile audit:
docs/track_f_actual_precode_cut_front_english_audit_20261122.md

Given a genuine ACTUAL coded source node x in the true coding fibre
of an old target K4 one-type v, make the ACTUAL target type of original
c=e(x.level) at precisely its own level, preserving the full two-way
target columns and singleton zero-based rank.

Splice this code type with genuine prefix restrictions of the already
synchronized surviving target types immediately BEFORE the code cut.
The result is one ACTUAL common-level, pairwise-distinct pre-code target
front, extending the old target front, with:
* true rank-zero / manuscript singleton age ONE for the coded sort,
* a genuine complete normalized integer canonical graph-age,
* that age pointwise no larger than the old full target age,
* genuine survivor restriction before c and after c+1 identical on
  their complete old-neighbour sets (zero actual target bits).

This explicitly constructs the pre-code object missing from the
history-realization proof; it does NOT yet prove its whole age equals
the prescribed previous age, because that requires the independent
survivor endpoint-age sandwich and legal zero-code law. No diary/BRD.
-/

namespace Kk

/-- ACTUAL target image original c=e(x.level) determines a true
normalized K4-free target prefix one-type at exactly level c.
Its old type v is preserved, its rank is zero when v's rank is
zero, and its complete two-direction target columns are genuine.

The source x must be an actual coding node in the exact source
coding-node fibre of v; no monotonicity of e is used. -/
theorem k4_actual_target_code_prefix_of_actual_fibre
    (Esrc Etgt : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily 4 (by decide) →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat)
    (v : HensonOneType 4 Etgt)
    (x : HensonOneType 4 Esrc)
    (hxFibre : x ∈ HensonOneType.sourceCodingFibre
      (E := Esrc) Etgt e v)
    (hVRank : HensonOneType.rank v = 0) :
    ∃ q : HensonOneType 4 Etgt,
      q.level = e x.level ∧
      v ≤ q ∧
      HensonOneType.rank q = 0 ∧
      HensonOneType.IsCodingNode q := by
  classical
  let c := e x.level
  let q : HensonOneType 4 Etgt :=
    HensonOneType.targetTypeOfOriginal
      4 (by decide) Etgt hAvoid c c (le_refl c)
  have hVCode : v ≤ q := by
    apply HensonOneType.targetTypeOfOriginal_extends_old
      4 (by decide) Etgt hAvoid v c c
      hxFibre.2.1 (le_refl c)
    intro a ha
    exact (hxFibre.2.2 a ha).1
  have hRankLe : HensonOneType.rank q ≤ HensonOneType.rank v :=
    HensonOneType.rank_antitone hVCode
  have hQRank : HensonOneType.rank q = 0 := by
    omega
  have hQCoding : HensonOneType.IsCodingNode q := by
    intro a ha
    exact HensonOneType.targetTypeOfOriginal_columns
      4 (by decide) Etgt hAvoid c c (le_refl c) a ha
  exact ⟨q, rfl, hVCode, hQRank, hQCoding⟩

/-- Construct the COMPLETE actual pre-code target tuple at the true
selected target image c=e(x.level).

OLD: pairwise DISTINCT genuine target K4 one-types at common level m.
The code sort j has genuine zero-based rank 0 and x is a TRUE source
coding original in its target fibre. For each surviving i≠j, the
later genuine target one-type extends old i, reaches beyond c and
has zero old target bit at c. The unused later j entry is a
formal placeholder only; no property of it is used for survivor
conclusions except that the common prefix is defined at c.

The resulting pre-code front consists of:
  j -> genuine target Henson type of original c,
  i≠j -> genuine chronological restriction of later i to c.
All prefix types really have level c, preserve complete old bits,
and remain distinct. Its full canonical integer-witness graph
age is genuine, antitone below old, and coded singleton age = 1.

The separate survivor-support equality needed to prove the whole
pre-code age equals the prescribed F is NOT assumed or concluded. -/
theorem k4_construct_actual_precode_target_front
    (d m : Nat)
    (Esrc Etgt : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily 4 (by decide) →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat)
    (old later : Fin d → HensonOneType 4 Etgt)
    (hOldLevel : ∀ i, (old i).level = m)
    (hOldInj : Function.Injective old)
    (j : Fin d) (x : HensonOneType 4 Esrc)
    (hxFibre : x ∈ HensonOneType.sourceCodingFibre
      (E := Esrc) Etgt e (old j))
    (hCodeRank : HensonOneType.rank (old j) = 0)
    (hFuture : ∀ i, e x.level + 1 ≤ (later i).level)
    (hLaterExt : ∀ i, i ≠ j → old i ≤ later i)
    (hLaterZero : ∀ i, i ≠ j → e x.level ∉ (later i).neighbours) :
    ∃ pre : Fin d → HensonOneType 4 Etgt,
      (∀ i, (pre i).level = e x.level ∧ old i ≤ pre i) ∧
      Function.Injective pre ∧
      HensonOneType.rank (pre j) = 0 ∧
      HensonOneType.IsCodingNode (pre j) ∧
      (∀ i, i ≠ j →
        pre i ≤ later i ∧
        (pre i).neighbours =
          (HensonOneType.restrictPrefix (later i) (e x.level + 1)
            (hFuture i)).neighbours) ∧
      IsIntegerGraphAge d 4
        (integerGraphAgeCanonical d 4
          (fun T : IntegerGraphSupport d 4 =>
            trackFCommonRawAge d 4 (e x.level) Etgt
              (fun i => (pre i).neighbours) T.1)) ∧
      AgeLe
        (integerGraphAgeCanonical d 4
          (fun T : IntegerGraphSupport d 4 =>
            trackFCommonRawAge d 4 (e x.level) Etgt
              (fun i => (pre i).neighbours) T.1))
        (integerGraphAgeCanonical d 4
          (fun T : IntegerGraphSupport d 4 =>
            trackFCommonRawAge d 4 m Etgt
              (fun i => (old i).neighbours) T.1)) ∧
      integerGraphAgeCanonical d 4
        (fun T : IntegerGraphSupport d 4 =>
          trackFCommonRawAge d 4 (e x.level) Etgt
            (fun i => (pre i).neighbours) T.1)
        (trackFSingletonSupport d 4 j (by decide)) = 1 := by
  classical
  let c : Nat := e x.level
  have hmC : m ≤ c := by
    have hOldCode : (old j).level ≤ c := hxFibre.2.1
    simpa only [hOldLevel j] using hOldCode
  obtain ⟨q, hQLevel, hOldQ, hQRank, hQCode⟩ :=
    k4_actual_target_code_prefix_of_actual_fibre
      Esrc Etgt hAvoid e (old j) x hxFibre hCodeRank
  let pre : Fin d → HensonOneType 4 Etgt :=
    fun i => if h : i = j then q else
      HensonOneType.restrictPrefix (later i) c
        (by
          have h := hFuture i
          dsimp only [c]
          omega)
  have hPLevel : ∀ i, (pre i).level = c := by
    intro i
    by_cases hij : i = j
    · simp only [pre, dif_pos hij, hQLevel]
      rfl
    · simp only [pre, dif_neg hij, HensonOneType.restrictPrefix]
      rfl
  have hOldP : ∀ i, old i ≤ pre i := by
    intro i
    by_cases hij : i = j
    · subst i
      simpa only [pre, dif_pos rfl] using hOldQ
    · have hOldY : (old i).level ≤ c := by
        rw [hOldLevel i]
        exact hmC
      have hYLater : c ≤ (later i).level := by
        have h := hFuture i
        dsimp only [c]
        omega
      have hExt : old i ≤
          HensonOneType.restrictPrefix (later i) c hYLater :=
        HensonOneType.le_restrictPrefix_of_le
          (old i) (later i) (hLaterExt i hij)
          c hOldY hYLater
      simpa only [pre, dif_neg hij] using hExt
  have hPInj : Function.Injective pre := by
    intro i k hik
    by_contra hIK
    obtain ⟨a, ha, hDiff⟩ :=
      HensonOneType.distinct_same_level_source_types_have_old_bit_separator
        d 4 m Etgt old hOldLevel hOldInj i k hIK
    have haI : a < (old i).level := by
      simpa only [hOldLevel i] using ha
    have haK : a < (old k).level := by
      simpa only [hOldLevel k] using ha
    have hSamePre : (a ∈ (pre i).neighbours) ↔
        (a ∈ (pre k).neighbours) := by
      rw [hik]
    have hSameOld : (a ∈ (old i).neighbours) ↔
        (a ∈ (old k).neighbours) :=
      ((hOldP i).2 a haI).trans
        (hSamePre.trans ((hOldP k).2 a haK).symm)
    exact hDiff hSameOld
  have hPCodeRank : HensonOneType.rank (pre j) = 0 := by
    simpa only [pre, dif_pos rfl] using hQRank
  have hPCodeActual : HensonOneType.IsCodingNode (pre j) := by
    simpa only [pre, dif_pos rfl] using hQCode
  have hSurvivor : ∀ i, i ≠ j →
      pre i ≤ later i ∧
      (pre i).neighbours =
        (HensonOneType.restrictPrefix (later i) (c + 1)
          (hFuture i)).neighbours := by
    intro i hij
    have hiC : c ≤ (later i).level := by
      have h := hFuture i
      dsimp only [c]
      omega
    have hPrefix : pre i =
        HensonOneType.restrictPrefix (later i) c hiC := by
      simp only [pre, dif_neg hij]
    rw [hPrefix]
    exact ⟨HensonOneType.restrictPrefix_le
      (later i) c hiC,
      trackFRestrictPrefix_zero_cut_neighbours_eq
        4 c Etgt (later i) (hFuture i) (hLaterZero i hij)⟩
  have hActualAge :
      IsIntegerGraphAge d 4
        (integerGraphAgeCanonical d 4
          (fun T : IntegerGraphSupport d 4 =>
            trackFCommonRawAge d 4 c Etgt
              (fun i => (pre i).neighbours) T.1)) :=
    trackFActualFront_canonical_is_integer_graph_age
      d 4 c (by decide) Etgt pre hPLevel
  have hAgeLe :
      AgeLe
        (integerGraphAgeCanonical d 4
          (fun T : IntegerGraphSupport d 4 =>
            trackFCommonRawAge d 4 c Etgt
              (fun i => (pre i).neighbours) T.1))
        (integerGraphAgeCanonical d 4
          (fun T : IntegerGraphSupport d 4 =>
            trackFCommonRawAge d 4 m Etgt
              (fun i => (old i).neighbours) T.1)) :=
    trackFActualFront_canonical_antitone_of_extension
      d 4 m c Etgt hmC old pre hOldLevel hPLevel hOldP
  have hBelow : ∀ i a, a ∈ (pre i).neighbours → a < c := by
    intro i a ha
    have h := (pre i).below a ha
    simpa only [hPLevel i] using h
  have hCodeSafe :
      finiteDirectedCliqueCapacity Etgt (pre j).neighbours < 3 := by
    have h := (finitePoolCliqueCheck_false_iff_capacity_lt
      Etgt (4 - 1) (pre j).neighbours).mp (pre j).safe
    simpa only [show (4 - 1 : Nat) = 3 from rfl] using h
  have hCodeCapacity :
      finiteDirectedCliqueCapacity Etgt (pre j).neighbours = 2 := by
    have hR := hPCodeRank
    change 4 - 1 - finiteDirectedCliqueCapacity Etgt
      (pre j).neighbours - 1 = 0 at hR
    omega
  let B : IntegerGraphSupport d 4 → Nat :=
    fun T => trackFCommonRawAge d 4 c Etgt
      (fun i => (pre i).neighbours) T.1
  have hRawMono : TrackFRawSupportMonotone d 4 B := by
    intro S T hST
    exact trackFCommonRawAge_mono_support
      d 4 c Etgt (fun i => (pre i).neighbours)
      S.1 T.1 hST
  have hCapSingleton :
      B (trackFSingletonSupport d 4 j (by decide)) ≤ 3 := by
    dsimp only [B, trackFCommonRawAge]
    omega
  have hRawSingleton :
      B (trackFSingletonSupport d 4 j (by decide)) = 1 := by
    change trackFCommonRawAge d 4 c Etgt
      (fun i => (pre i).neighbours) {j} = 1
    unfold trackFCommonRawAge
    rw [trackFCommonNeighbourPool_singleton
      d c (fun i => (pre i).neighbours) hBelow j]
    rw [hCodeCapacity]
    decide
  have hCanonSingleton :
      integerGraphAgeCanonical d 4 B
        (trackFSingletonSupport d 4 j (by decide)) = 1 :=
    (trackFCanonical_singleton_eq_raw
      d 4 (by decide) B hRawMono j hCapSingleton).trans
        hRawSingleton
  exact ⟨pre, (fun i => ⟨hPLevel i, hOldP i⟩),
    hPInj, hPCodeRank, hPCodeActual,
    hSurvivor, hActualAge, hAgeLe, hCanonSingleton⟩

end Kk
