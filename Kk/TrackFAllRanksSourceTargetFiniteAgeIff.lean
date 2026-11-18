import Kk.TrackFAllRanksTargetFiniteAgeInclusion
import Kk.TrackFAllSupportTargetRawUpper
import Mathlib.Tactic

/-!
# Track F: conditional equality of true source/target finite extension classes

English proof and hostile audit committed first:
docs/track_f_conditional_finite_age_equality_english_audit.md

All target-source fibre largeness and old-neighbour image cutoff
hypotheses are EXPLICIT. The conclusion is logical equivalence of
ALL finite B-clique feasibility inequalities, not pointwise equality
of redundant RAW numerical bounds, nor construction of compatible
target fronts, nor diary unavoidability.
-/

namespace Kk

/-- Every finite B on its prescribed arbitrary source sorts is
source-RAW-feasible if and only if it is target-RAW-feasible,
conditional on rank-large ACTUAL target coding-node fibres
and a target cutoff beyond images of every old positive
source neighbour.

The forward implication uses actual all-ranks source richness
plus genuine transported target clique constraints (#380).
The reverse implication uses the all-support target RAW
upper bound from actual old-neighbour clique images.

No injection of the labelling σ, no order preservation of e,
and no numeric equality of redundant raw ages is asserted. -/
theorem trackFAllRanks_source_target_clique_feasibility_iff
    (d ell m H N : Nat) (hell : 2 ≤ ell)
    (Esrc Etgt B : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (u : Fin d → HensonOneType ell Esrc)
    (v : Fin d → HensonOneType ell Etgt)
    (σ : Nat → Fin d)
    (hULevel : ∀ i, (u i).level = m)
    (hVLevel : ∀ i, (v i).level = H)
    (hImageBelow : ∀ i c, c ∈ (u i).neighbours → e c < H)
    (hLarge : ∀ i,
      RankLargeness.Large HensonOneType.rank
        (HensonOneType.sourceCodingFibre (E := Esrc)
          Etgt e (v i))
        (HensonOneType.rank (u i)) (u i))
    (hSymB : ∀ i j, B i j = B j i) :
    (∀ C : Finset Nat,
      C ⊆ Finset.range N → C.Nonempty →
      IsDirectedCliqueOn B C →
      C.card ≤ trackFCommonRawAge d ell m Esrc
        (fun i => (u i).neighbours) (C.image σ)) ↔
    (∀ C : Finset Nat,
      C ⊆ Finset.range N → C.Nonempty →
      IsDirectedCliqueOn B C →
      C.card ≤ trackFCommonRawAge d ell H Etgt
        (fun i => (v i).neighbours) (C.image σ)) := by
  classical
  constructor
  · intro hSource
    exact trackFAllRanks_source_feasible_implies_target_feasible
      d ell m H N hell Esrc Etgt B hAvoid e he hInduced
      u v σ hULevel hVLevel hLarge hSymB hSource
  · intro hTarget C hCSub hNonempty hClique
    have hSNonempty : (C.image σ).Nonempty := by
      obtain ⟨i, hi⟩ := hNonempty
      exact ⟨σ i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
    have hUpper :
        trackFCommonRawAge d ell H Etgt
          (fun i => (v i).neighbours) (C.image σ) ≤
        trackFCommonRawAge d ell m Esrc
          (fun i => (u i).neighbours) (C.image σ) :=
      trackFCommonRawAge_target_le_source_of_large_fibres
        d ell m H Esrc Etgt e he hInduced
        u v hULevel hVLevel hImageBelow hLarge
        (C.image σ) hSNonempty
    exact (hTarget C hCSub hNonempty hClique).trans hUpper

end Kk
