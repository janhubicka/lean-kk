import Kk.TrackFNonrootActualTargetFibre
import Kk.TrackFTargetUpperRankCertificate
import Mathlib.Tactic

/-!
# Track F: non-root target continuation with target rank ≤ source rank

English proof and hostile audit committed before Lean:
docs/track_f_nonroot_rank_upper_english_audit.md

Composes the verified non-root rank-large target-prefix
continuation with exact transport of source old-neighbour
clique certificates along an arbitrary INJECTIVE INDUCED
embedding of actual original-graph edge tables.

The cutoff is taken beyond the images of the ORIGINAL source
type's old neighbours, not those of the later source refinement.
The latter may have additional markers whose target images occur
beyond the cutoff, so bounding them would be invalid.

This establishes a genuine later target type with a rank-large
actual source coding fibre and target singleton rank no greater
than the original source singleton rank. The missing reverse
inequality still needs a genuine source large-fibre clique and
is not assumed or proved here.
-/

namespace Kk.HensonOneType

/-- Given a rank-large ACTUAL source coding-node fibre over a
target type v0, and an arbitrary injective induced graph
embedding e, for EVERY requested target bound B there is a
GENUINE target prefix vH beyond B and a SAME-RANK source
refinement uH, such that the new ACTUAL source fibre remains
large and the target singleton rank is no GREATER than that
of the ORIGINAL source type u.

No order preservation of e is assumed. The target level is
also chosen beyond the image of every old neighbour of u,
which permits a separate exact old-clique certificate transfer. -/
theorem sourceCodingFibre_extend_target_rank_le
    (ell : Nat) (hell : 2 ≤ ell)
    (Esrc Etgt : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (v0 : HensonOneType ell Etgt)
    (B : Nat) (u : HensonOneType ell Esrc)
    (hLarge : RankLargeness.Large rank
      (sourceCodingFibre (E := Esrc) Etgt e v0)
      (rank u) u) :
    ∃ vH : HensonOneType ell Etgt,
    ∃ uH : HensonOneType ell Esrc,
      v0 ≤ vH ∧ B ≤ vH.level ∧
      u ≤ uH ∧ rank uH = rank u ∧
      RankLargeness.Large rank
        (sourceCodingFibre (E := Esrc) Etgt e vH)
        (rank u) uH ∧
      rank vH ≤ rank u := by
  classical
  let H : Nat :=
    max (max B v0.level)
      ((u.neighbours.sup (fun c => e c)) + 1)
  have hCutOld : v0.level ≤ H := by
    exact (le_max_right B v0.level).trans
      (le_max_left _ _)
  have hCutB : B ≤ H := by
    exact (le_max_left B v0.level).trans
      (le_max_left _ _)
  have hImageBound : ∀ c ∈ u.neighbours, e c < H := by
    intro c hc
    have hSup : e c ≤ u.neighbours.sup (fun t => e t) :=
      Finset.le_sup (f := fun t => e t) hc
    have hUpper : u.neighbours.sup (fun t => e t) + 1 ≤ H :=
      le_max_right _ _
    omega
  obtain ⟨vH, uH, hVExtend, hVHLevel, hUExtend,
    hUHRank, hNewLarge⟩ :=
    sourceCodingFibre_extend_target_prefix_large
      ell hell Esrc Etgt hAvoid e he
      v0 H hCutOld u hLarge
  have hOldImagesBelow :
      ∀ c ∈ u.neighbours, e c < vH.level := by
    intro c hc
    rw [hVHLevel]
    exact hImageBound c hc
  obtain ⟨x, huHx, hxFibre⟩ :=
    RankLargeness.large_has_member rank
      (sourceCodingFibre (E := Esrc) Etgt e vH)
      (rank u) uH hUHRank hNewLarge
  have hux : u ≤ x := le_trans hUExtend huHx
  have hTargetBound : rank vH ≤ rank u :=
    target_rank_le_source_of_old_neighbours
      ell Esrc Etgt e he hInduced
      u vH hOldImagesBelow x hux hxFibre
  refine ⟨vH, uH, hVExtend, ?_, hUExtend,
    hUHRank, hNewLarge, hTargetBound⟩
  rw [hVHLevel]
  exact hCutB

end Kk.HensonOneType
