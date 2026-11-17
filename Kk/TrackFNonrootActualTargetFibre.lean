import Kk.TrackFNonrootPrefixFibre
import Kk.TrackFTargetOriginalPrefix
import Mathlib.Tactic

/-!
# Track F: actual non-root source-target prefix continuation

English-first proof and hostile audit were committed before Lean in:
docs/track_f_nonroot_continuation_english_audit.md

From ANY rank-large ACTUAL source coding-node fibre over a target
Henson one-type v, and ANY injective original-index map e (not
necessarily monotone), every later target cutoff H can be reached
while preserving SOURCE rank and the rank-largeness of the genuine
coding-node fibre.

The target type of level H is constructed from an ACTUAL target
original e(x.level) chosen in the large finite-prefix colour class.
This invokes the real K_ell-free target prefix certificate and
retains BOTH directions of all old target adjacency bits.

Deliberately NOT proved: target/source singleton rank equality,
the clique-richness needed for that equality, simultaneous
multi-sort compatibility, or any diary/BRD theorem.
-/

namespace Kk.HensonOneType

/-- The two real old-column equalities for the same actual future
target original y imply that an old target type v0 is extended
by the actual target prefix of y at H≥v0.level.

In particular the NEGATIVE bits agree; mere inclusion of
positive neighbour sets would not suffice for the chronological
HensonOneType extension order. -/
theorem targetTypeOfOriginal_extends_old
    (ell : Nat) (hell : 2 ≤ ell)
    (Etgt : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel Etgt))
    (v0 : HensonOneType ell Etgt)
    (H y : Nat) (hVLevel : v0.level ≤ H)
    (hy : H ≤ y)
    (hOldColumn : ∀ a : Nat, a < v0.level →
      Etgt a y = decide (a ∈ v0.neighbours)) :
    v0 ≤ targetTypeOfOriginal ell hell Etgt hAvoid H y hy := by
  classical
  refine ⟨hVLevel, ?_⟩
  intro a ha
  have haH : a < H := lt_of_lt_of_le ha hVLevel
  have hNewCol :=
    (targetTypeOfOriginal_columns
      ell hell Etgt hAvoid H y hy a haH).1
  have hBits :
      decide (a ∈ v0.neighbours) =
        decide (a ∈
          (targetTypeOfOriginal ell hell Etgt hAvoid H y hy).neighbours) :=
    (hOldColumn a ha).symm.trans hNewCol
  constructor
  · intro haOld
    have hTrue :
        decide (a ∈
          (targetTypeOfOriginal ell hell Etgt hAvoid H y hy).neighbours) =
          true := by
      rw [← hBits]
      simp [haOld]
    simpa only [decide_eq_true_eq] using hTrue
  · intro haNew
    have hTrue : decide (a ∈ v0.neighbours) = true := by
      rw [hBits]
      simp [haNew]
    simpa only [decide_eq_true_eq] using hTrue

/-- The ACTUAL non-root continuation theorem for one source-target
coding-node fibre. At an arbitrarily later target prefix H, the
target type vH is constructed from a real image original, and
the corresponding source coding-node fibre stays recursively
rank-large above a same-rank SOURCE refinement.

The only map premise is injectivity of e; preserving the source
and target enumeration order is NEVER assumed.

Important: we do NOT assert that the target rank vH equals the
source rank u. That is exactly the separate richness-to-clique
and reverse-certificate gap in the manuscript transport lemma. -/
theorem sourceCodingFibre_extend_target_prefix_large
    (ell : Nat) (hell : 2 ≤ ell)
    (Esrc Etgt : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat) (he : Function.Injective e)
    (v0 : HensonOneType ell Etgt)
    (H : Nat) (hVLevel : v0.level ≤ H)
    (u : HensonOneType ell Esrc)
    (hLarge : RankLargeness.Large rank
      (sourceCodingFibre (E := Esrc) Etgt e v0)
      (rank u) u) :
    ∃ vH : HensonOneType ell Etgt,
    ∃ uH : HensonOneType ell Esrc,
      v0 ≤ vH ∧ vH.level = H ∧
      u ≤ uH ∧ rank uH = rank u ∧
      RankLargeness.Large rank
        (sourceCodingFibre (E := Esrc) Etgt e vH)
        (rank u) uH := by
  classical
  obtain ⟨j, w, x, huw, hwrank, hwx, hwLarge,
    hxOld, hxColour, hxFuture⟩ :=
    sourceCodingFibre_target_prefix_class
      Esrc Etgt e he v0 H hVLevel u hLarge
  let vH : HensonOneType ell Etgt :=
    targetTypeOfOriginal ell hell Etgt hAvoid
      H (e x.level) hxFuture
  have hVExtend : v0 ≤ vH := by
    apply targetTypeOfOriginal_extends_old
      ell hell Etgt hAvoid v0 H (e x.level)
      hVLevel hxFuture
    intro a ha
    exact (hxOld.2.2 a ha).1
  have hRefinementSubset :
      ({t : HensonOneType ell Esrc |
        t ∈ sourceCodingFibre (E := Esrc) Etgt e v0 ∧
        targetPrefixColour Etgt e H t = j ∧
        H ≤ e t.level} : Set (HensonOneType ell Esrc)) ⊆
      sourceCodingFibre (E := Esrc) Etgt e vH := by
    intro z hz
    obtain ⟨hzOld, hzColour, hzFuture⟩ := hz
    refine ⟨hzOld.1, hzFuture, ?_⟩
    intro a ha
    have hSameColour :
        targetPrefixColour Etgt e H z =
          targetPrefixColour Etgt e H x :=
      hzColour.trans hxColour.symm
    have hFirst := congrArg
      (fun c : (Fin H → Bool) × (Fin H → Bool) =>
        c.1 ⟨a, ha⟩) hSameColour
    have hSecond := congrArg
      (fun c : (Fin H → Bool) × (Fin H → Bool) =>
        c.2 ⟨a, ha⟩) hSameColour
    change Etgt a (e z.level) = Etgt a (e x.level) at hFirst
    change Etgt (e z.level) a = Etgt (e x.level) a at hSecond
    have hTarget :=
      targetTypeOfOriginal_columns
        ell hell Etgt hAvoid H (e x.level) hxFuture a ha
    exact ⟨hFirst.trans hTarget.1, hSecond.trans hTarget.2⟩
  have hTargetLarge :
      RankLargeness.Large rank
        (sourceCodingFibre (E := Esrc) Etgt e vH)
        (rank u) w :=
    RankLargeness.large_mono_set rank hRefinementSubset
      (rank u) w hwLarge
  exact ⟨vH, w, hVExtend, rfl, huw, hwrank, hTargetLarge⟩

end Kk.HensonOneType
