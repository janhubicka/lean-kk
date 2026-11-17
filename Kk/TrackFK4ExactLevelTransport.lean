import Kk.TrackFK4FullSingletonTransport
import Kk.TrackFExactTargetPrefixRestriction
import Mathlib.Tactic

/-!
# Track F: exact-level K4 singleton source/target compatibility

English proof and adversarial audit were committed BEFORE Lean:
docs/track_f_k4_exact_target_level_english_audit.md

The verified full-K4 singleton same-rank theorem reaches a target
type at SOME level at least L. The manuscript asks for the target
type at EXACT prescribed level L when starting from an initially
compatible (equal singleton rank) pair.

We restrict the genuine target Henson type to L, preserving
both positive and negative old bits and K3-free safety.
Rank antitonicity sandwiches the intermediate type's rank
between equal endpoint ranks. The true actual sourceCodingFibre
of the long target type lies in the fibre of the shorter
restricted type, so rank-largeness survives by set inclusion.

No claim is made about full MULTI-SORT profile synchronization,
diary-envelope persistence or exact BRD numbers.
-/

namespace Kk.HensonOneType

/-- Exact prescribed target-level K4 SINGLETON continuation
for an INITIALLY compatible pair of source and target types.

Assume source actual coding-node target fibre rank(u)-large and
rank(v0)=rank(u). For every L≥v0.level, construct a genuine
target Henson one-type at EXACT level L extending v0 and a
same-rank source type refinement uL, such that the target and
source singleton ranks still match and the ACTUAL coding-node
fibre remains recursively rank-large.

No chronology monotonicity of the injective INDUCED embedding
is assumed. The equal-rank hypothesis at the old target v0
is necessary for exact-level rank sandwich, and is explicit. -/
theorem k4_sourceCodingFibre_continue_equal_rank_exact_level
    (Esrc Etgt : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily 4 (by decide) →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (v0 : HensonOneType 4 Etgt)
    (L : Nat) (hOldLevel : v0.level ≤ L)
    (u : HensonOneType 4 Esrc)
    (hOldRank : rank v0 = rank u)
    (hLarge : RankLargeness.Large rank
      (sourceCodingFibre (E := Esrc) Etgt e v0)
      (rank u) u) :
    ∃ vL : HensonOneType 4 Etgt,
    ∃ uL : HensonOneType 4 Esrc,
      v0 ≤ vL ∧ vL.level = L ∧
      u ≤ uL ∧ rank uL = rank u ∧ rank vL = rank u ∧
      RankLargeness.Large rank
        (sourceCodingFibre (E := Esrc) Etgt e vL)
        (rank u) uL := by
  obtain ⟨vH, uH, hV0H, hCutoff, hUUH, hURank,
    hVRank, hLongLarge⟩ :=
    k4_sourceCodingFibre_continue_equal_rank
      Esrc Etgt hAvoid e he hInduced v0 L u hLarge
  let vL : HensonOneType 4 Etgt :=
    restrictPrefix vH L hCutoff
  have hV0L : v0 ≤ vL :=
    le_restrictPrefix_of_le v0 vH hV0H L
      hOldLevel hCutoff
  have hVLRk : rank vL = rank vH :=
    rank_restrictPrefix_eq_of_endpoint_eq
      v0 vH hV0H (hOldRank.trans hVRank.symm)
      L hOldLevel hCutoff
  have hVLRkU : rank vL = rank u :=
    hVLRk.trans hVRank
  have hVHL : vL ≤ vH :=
    restrictPrefix_le vH L hCutoff
  have hFibreSub :
      sourceCodingFibre (E := Esrc) Etgt e vH ⊆
        sourceCodingFibre (E := Esrc) Etgt e vL :=
    sourceCodingFibre_antitone_target Esrc Etgt e vL vH hVHL
  have hShortLarge : RankLargeness.Large rank
      (sourceCodingFibre (E := Esrc) Etgt e vL)
      (rank u) uH :=
    RankLargeness.large_mono_set rank hFibreSub
      (rank u) uH hLongLarge
  exact ⟨vL, uH, hV0L, rfl, hUUH, hURank,
    hVLRkU, hShortLarge⟩

end Kk.HensonOneType
