import Kk.TrackFActualIndependentCode
import Kk.TrackFRealTargetSurvivorNumericEndpoint
import Kk.TrackFPrecodeFromRealSurvivors
import Kk.TrackFActualCodeAgeWithoutDummy
import Kk.TrackFPhysicalSurvivorDeletion
import Mathlib.Tactic

/-!
# Track F: complete ACTUAL independent-code ORDINARY-L age stage

The English proof was written and adversarially audited FIRST:
docs/track_f_full_actual_zero_code_age_stage_english_audit_20261122.md
(22 mathematical and scope checks, before this Lean source).

Starting at one GENUINE full source–target K4 compatible checkpoint
with identical COMPLETE canonical numerical integer age, and at a
legal zero-code sort j of true rank zero:
  1. choose an ACTUAL code original r=x.level whose target image
     c=e(r) is beyond any cutoff and has BOTH zero directed edges
     to every already selected original;
  2. derive by REAL survivor synchronization the true OLD TARGET vs
     LATER TARGET NUMERIC survivor endpoint equality, with
     target ZERO bits at c and preserved actual coding fibres;
  3. build a GENUINE full pre-code target front at exact level c,
     using ONLY the REAL surviving target types and the ACTUAL
     target original's complete two-direction column;
  4. apply the checked genuine-survivor chronological age sandwich,
     safe integer-age and legal zero-code rigidity: the WHOLE
     pre-code canonical age equals the original full target age,
     on ALL nonempty supports including mixed triples;
  5. form the REAL immediate post-code survivor target prefixes at
     c+1 and identify their COMPLETE age with exactly the
     original full target canonical age restricted by the
     order-preserving survivor index Fin.succAboveEmb j.

This is a FULL ordinary-L physical numerical zero-code step,
NOT the entire diary: target lex-order indexing of checkpoints,
selected meet/split chronology, dependent Kpt E/parameter history,
global unavoidable diary colouring and BRD lower bound are
separate obligations. No source→target order preservation assumed.
No new axioms, unpublished diary characterization or 24-count.
-/

namespace Kk

/-- A complete actual zero-code L-age step, assembled entirely
from previously standard-only Lean-checked geometric and numeric
ingredients, without assuming an intermediate pre-code profile.

The initial source/target full checkpoint has actual compatible
coding fibres at equal singleton ranks and the exact complete
NUMERICAL canonical age equality required by the diary induction.
The selected coded sort j has zero-based rank 0. Already fixed
past-source edges to that sort must have bit zero. The old true
canonical target age must obey the LEGAL zero-code erasure equations
on EVERY admissible mixed support; no empty-support value is used.

Outputs real source coding node x, real later source/target survivors
w,t at common levels M,H, genuine actual pre-code target types at
c=e(x.level), and genuine immediate post-code survivor prefixes at
c+1, with:
 * target image c beyond cutoff and two-direction zeros to past;
 * rank-preserved actual large survivor coding fibres and zero c;
 * pre-code full age exactly EQUAL to the old full target age;
 * immediate post-code survivor age exactly the correct canonical
   old age pulled back by the true TARGET survivor deletion map f.

The selected coded branch TERMINATES; no dummy later coded branch
appears in the statement or age comparison. The target label
ordering still must be identified with the actual lex order when
applying this local theorem to a complete diary, and full
cover/split histories remain unproved. -/
theorem k4_full_actual_zero_code_ordinary_age_step
    (d ms mt cutoff : Nat)
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
    (hvInj : Function.Injective v)
    (hRank : ∀ i, HensonOneType.rank (v i) =
      HensonOneType.rank (u i))
    (hLarge : ∀ i,
      RankLargeness.Large HensonOneType.rank
        (HensonOneType.sourceCodingFibre (E := Esrc) Etgt e (v i))
        (HensonOneType.rank (u i)) (u i))
    (hCheckpointAge :
      trackFPhysicalFrontCanonicalAge (d + 1) 4 ms Esrc u =
      trackFPhysicalFrontCanonicalAge (d + 1) 4 mt Etgt v)
    (j : Fin (d + 1))
    (hRankZero : HensonOneType.rank (u j) = 0)
    (past : Finset Nat)
    (hPastZero : ∀ p ∈ past, p < (u j).level →
      p ∉ (u j).neighbours)
    (hLegal : ∀ T : IntegerGraphSupport (d + 1) 4,
      j ∈ T.1 → ∀ S : IntegerGraphSupport (d + 1) 4,
        S.1 = T.1.erase j →
        trackFPhysicalFrontCanonicalAge (d + 1) 4 mt Etgt v T =
        trackFPhysicalFrontCanonicalAge (d + 1) 4 mt Etgt v S) :
    ∃ x : HensonOneType 4 Esrc,
    ∃ H M : Nat,
    ∃ w : Fin d → HensonOneType 4 Esrc,
    ∃ t : Fin d → HensonOneType 4 Etgt,
    ∃ pre : Fin (d + 1) → HensonOneType 4 Etgt,
    ∃ post : Fin d → HensonOneType 4 Etgt,
      (u j ≤ x ∧
        x ∈ HensonOneType.sourceCodingFibre
          (E := Esrc) Etgt e (v j) ∧
        HensonOneType.rank x = 0 ∧
        cutoff < e x.level ∧
        (∀ p ∈ past,
          p < x.level ∧
          Esrc p x.level = false ∧
          Esrc x.level p = false ∧
          Etgt (e p) (e x.level) = false ∧
          Etgt (e x.level) (e p) = false)) ∧
      cutoff < H ∧ e x.level < H ∧
      (∀ i : Fin d,
        (w i).level = M ∧
        u (Fin.succAboveEmb j i) ≤ w i ∧
        HensonOneType.rank (w i) =
          HensonOneType.rank (u (Fin.succAboveEmb j i)) ∧
        x.level < (w i).level ∧
        x.level ∉ (w i).neighbours) ∧
      (∀ i : Fin d,
        v (Fin.succAboveEmb j i) ≤ t i ∧
        (t i).level = H ∧
        HensonOneType.rank (t i) =
          HensonOneType.rank (u (Fin.succAboveEmb j i)) ∧
        RankLargeness.Large HensonOneType.rank
          (HensonOneType.sourceCodingFibre (E := Esrc) Etgt e (t i))
          (HensonOneType.rank (w i)) (w i) ∧
        e x.level ∉ (t i).neighbours) ∧
      Function.Injective t ∧
      (∀ i : Fin (d + 1),
        (pre i).level = e x.level ∧ v i ≤ pre i) ∧
      Function.Injective pre ∧
      HensonOneType.rank (pre j) = 0 ∧
      HensonOneType.IsCodingNode (pre j) ∧
      (∀ i : Fin d,
        pre (Fin.succAboveEmb j i) ≤ t i) ∧
      trackFPhysicalFrontCanonicalAge (d + 1) 4 (e x.level)
        Etgt pre =
      trackFPhysicalFrontCanonicalAge (d + 1) 4 mt
        Etgt v ∧
      (∀ i : Fin d,
        (post i).level = e x.level + 1 ∧ post i ≤ t i) ∧
      (∀ i : Fin d,
        pre (Fin.succAboveEmb j i) ≤ post i ∧
        (pre (Fin.succAboveEmb j i)).neighbours =
          (post i).neighbours) ∧
      (∀ U : IntegerGraphSupport d 4,
        trackFPhysicalFrontCanonicalAge (d + 1) 4 (e x.level)
          Etgt pre (trackFMapSupport (Fin.succAboveEmb j) U) =
        trackFPhysicalFrontCanonicalAge d 4 (e x.level + 1)
          Etgt post U) := by
  classical
  let f : Fin d ↪ Fin (d + 1) := Fin.succAboveEmb j
  have hTargetRankZero : HensonOneType.rank (v j) = 0 :=
    (hRank j).trans hRankZero
  have hCodeLarge :
      RankLargeness.Large HensonOneType.rank
        (HensonOneType.sourceCodingFibre (E := Esrc) Etgt e (v j))
        0 (u j) := by
    simpa only [hRankZero] using hLarge j
  obtain ⟨x, hUX, hxFibre, hxRank, hxAfter, hxPast⟩ :=
    HensonOneType.sourceCodingFibre_rank_zero_independent_code
      4 cutoff Esrc Etgt e he hInduced
      (v j) (u j) hRankZero hCodeLarge past hPastZero
  have hSourceR : ms ≤ x.level := by
    simpa only [huLevel j] using hUX.1
  have hTargetC : mt ≤ e x.level := by
    simpa only [hvLevel j] using hxFibre.2.1
  obtain ⟨H, M, w, t, hCut, hCodeCut, hWValid, hTValid,
    hTInj, hOldTargetSurvivorAge⟩ :=
    k4_survivor_target_numeric_endpoint_of_full_checkpoint
      d ms mt x.level cutoff hSourceR
      Esrc Etgt hAvoid e he hInduced
      u v huLevel hvLevel huInj hRank hLarge
      hCheckpointAge j
  have htLevel : ∀ i : Fin d, (t i).level = H :=
    fun i => (hTValid i).2.1
  have htExt : ∀ i : Fin d,
      v (Fin.succAboveEmb j i) ≤ t i :=
    fun i => (hTValid i).1
  have htZero : ∀ i : Fin d, e x.level ∉ (t i).neighbours :=
    fun i => (hTValid i).2.2.2.2
  obtain ⟨pre, hPreValid, hPreInj, hPreRank,
    hPreActualCode, hPreRealSurvivors,
    _hPreIsAge, _hPreLeOld, _hPreSingletonOne⟩ :=
    k4_precode_from_genuine_surviving_target_front
      d mt H Esrc Etgt hAvoid e v t
      hvLevel hvInj j x hxFibre hTargetRankZero
      htLevel hCodeCut htExt htZero
  have hPreLevel : ∀ i, (pre i).level = e x.level :=
    fun i => (hPreValid i).1
  have hOldPre : ∀ i, v i ≤ pre i :=
    fun i => (hPreValid i).2
  have hPreLater :
      ∀ i : Fin d, pre (Fin.succAboveEmb j i) ≤ t i :=
    fun i => (hPreRealSurvivors i).1
  have hPreFullEq :
      trackFPhysicalFrontCanonicalAge (d + 1) 4 (e x.level)
        Etgt pre =
      trackFPhysicalFrontCanonicalAge (d + 1) 4 mt Etgt v :=
    k4ActualPrecode_full_age_eq_of_genuine_survivor_endpoints
      d mt (e x.level) H Etgt j
      hTargetC (Nat.le_of_lt hCodeCut)
      v pre t hvLevel hPreLevel htLevel hOldPre
      hPreLater hOldTargetSurvivorAge
      hTargetRankZero hPreRank hLegal
  have hFuture : ∀ i : Fin d, e x.level + 1 ≤ (t i).level := by
    intro i
    rw [htLevel i]
    omega
  let post : Fin d → HensonOneType 4 Etgt :=
    fun i => HensonOneType.restrictPrefix
      (t i) (e x.level + 1) (hFuture i)
  have hPostValid :
      ∀ i : Fin d,
        (post i).level = e x.level + 1 ∧ post i ≤ t i := by
    intro i
    exact ⟨rfl, HensonOneType.restrictPrefix_le
      (t i) (e x.level + 1) (hFuture i)⟩
  have hPrePost :
      ∀ i : Fin d,
        pre (Fin.succAboveEmb j i) ≤ post i ∧
        (pre (Fin.succAboveEmb j i)).neighbours =
          (post i).neighbours := by
    intro i
    have hBits :
        (pre (Fin.succAboveEmb j i)).neighbours =
          (post i).neighbours := by
      exact (hPreRealSurvivors i).2
    have hLevel :
        (pre (Fin.succAboveEmb j i)).level ≤ (post i).level := by
      rw [hPreLevel (Fin.succAboveEmb j i), (hPostValid i).1]
      omega
    refine ⟨⟨hLevel, ?_⟩, hBits⟩
    intro a _
    exact congrArg (fun S : Finset Nat => a ∈ S) hBits
  have hPreMatch :
      ∀ i : Fin d,
        (pre (Fin.succAboveEmb j i)).neighbours =
          (HensonOneType.restrictPrefix (t i) (e x.level)
            (by have hh := hFuture i; omega)).neighbours := by
    intro i
    have hBeforeAfter :=
      trackFRestrictPrefix_zero_cut_neighbours_eq
        4 (e x.level) Etgt (t i) (hFuture i) (htZero i)
    exact (hPreRealSurvivors i).2.trans hBeforeAfter.symm
  have hPostAge :
      ∀ U : IntegerGraphSupport d 4,
        trackFPhysicalFrontCanonicalAge (d + 1) 4 (e x.level)
          Etgt pre (trackFMapSupport f U) =
        trackFPhysicalFrontCanonicalAge d 4 (e x.level + 1)
          Etgt post U := by
    intro U
    exact trackFActualFront_zero_code_survivor_canonical_reindex
      d 4 (e x.level) (by decide) Etgt j
      pre hPreLevel t hFuture htZero hPreMatch U
  exact ⟨x, H, M, w, t, pre, post,
    ⟨hUX, hxFibre, hxRank, hxAfter, hxPast⟩,
    hCut, hCodeCut, hWValid, hTValid,
    hTInj, hPreValid, hPreInj, hPreRank,
    hPreActualCode, hPreLater, hPreFullEq,
    hPostValid, hPrePost, hPostAge⟩

end Kk
