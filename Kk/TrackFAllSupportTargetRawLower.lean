import Kk.TrackFMultiSortRawIsolation
import Kk.TrackFActualCodingFibre
import Kk.TrackFTargetRankClique
import Mathlib.Tactic

/-!
# Track F: mixed target raw-age lower bound from ACTUAL sorted source cliques

English proof and hostile audit committed BEFORE Lean:
docs/track_f_all_support_target_raw_lower_english_audit.md

Given an ACTUAL directed source clique of original vertices,
each assigned to a sort in a selected support S and each with
a GENUINE source coding-node witness in its assigned target
one-type fibre, their injective induced target images form a
true FUTURE target clique. Every image is fully joined to the
true common old target-neighbour pool on support S.

The already verified physical K_ell-free target clique bound
therefore forces the target mixed RAW age on S to be at least
the source clique size. A conditional all-support corollary
isolates precisely the still-open JOINT multi-sort richness
needed for the reverse age inequality in the manuscript.

No assertion that arbitrary rank-large fibres already realize
these joint cliques, canonical mixed age equality or exact BRDs
is included.
-/

namespace Kk

/-- A genuinely realized source clique labelled by target-fibre
sorts in S forces a lower bound for the target RAW clique
capacity profile on S.

Each source original c in C has an actual source coding-node
type t of level c in the assigned target v_(sort c) fibre.
The common target old-neighbour pool lies before common H,
and is joined in BOTH directions to the entire future image
clique e[C]. Exact K_ell-freeness of Etgt yields the bound.

This is a theorem about ACTUAL vertices and actual graph ages,
NOT a claim of clique existence from abstract rank largeness. -/
theorem trackFCommonRawAge_target_ge_sorted_source_clique
    (d ell H : Nat) (hell : 2 ≤ ell)
    (Esrc Etgt : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (v : Fin d → HensonOneType ell Etgt)
    (hVLevel : ∀ i, (v i).level = H)
    (S : Finset (Fin d))
    (C : Finset Nat) (sort : Nat → Fin d)
    (hSort : ∀ c ∈ C, sort c ∈ S)
    (hClique : IsDirectedCliqueOn Esrc C)
    (hFibre : ∀ c ∈ C,
      ∃ t : HensonOneType ell Esrc,
        t.level = c ∧
        t ∈ HensonOneType.sourceCodingFibre
          (E := Esrc) Etgt e (v (sort c))) :
    C.card ≤ trackFCommonRawAge d ell H Etgt
      (fun i => (v i).neighbours) S := by
  classical
  let P : Finset Nat :=
    trackFCommonNeighbourPool d H (fun i => (v i).neighbours) S
  let W : Finset Nat := C.image e
  have hPBelow : ∀ p ∈ P, p < H := by
    intro p hp
    change p ∈ (Finset.range H).filter
      (fun q => ∀ i ∈ S, q ∈ (v i).neighbours) at hp
    exact Finset.mem_range.mp (Finset.mem_filter.mp hp).1
  have hFuture : ∀ w ∈ W, H ≤ w := by
    intro w hw
    obtain ⟨c, hc, hcw⟩ := Finset.mem_image.mp hw
    obtain ⟨t, ht, htFibre⟩ := hFibre c hc
    have hLevel : H ≤ e t.level := by
      simpa only [hVLevel (sort c)] using htFibre.2.1
    have hFutureC : H ≤ e c := by simpa only [ht] using hLevel
    exact hcw ▸ hFutureC
  have hCliqueImage : IsDirectedCliqueOn Etgt W := by
    intro w hw z hz hwz
    obtain ⟨a, ha, haw⟩ := Finset.mem_image.mp hw
    obtain ⟨b, hb, hbz⟩ := Finset.mem_image.mp hz
    have hab : a ≠ b := by
      intro hEq
      subst b
      exact hwz (haw.symm.trans hbz)
    have hSource : Esrc a b = true :=
      hClique a ha b hb hab
    have hTarget : Etgt (e a) (e b) = true :=
      (hInduced a b hab).symm.trans hSource
    simpa only [haw, hbz] using hTarget
  have hJoined : ∀ p ∈ P, ∀ w ∈ W,
      Etgt p w = true ∧ Etgt w p = true := by
    intro p hp w hw
    obtain ⟨c, hc, hcw⟩ := Finset.mem_image.mp hw
    obtain ⟨t, ht, htFibre⟩ := hFibre c hc
    have hpAll : ∀ i ∈ S, p ∈ (v i).neighbours := by
      change p ∈ (Finset.range H).filter
        (fun q => ∀ i ∈ S, q ∈ (v i).neighbours) at hp
      exact (Finset.mem_filter.mp hp).2
    have hpV : p ∈ (v (sort c)).neighbours :=
      hpAll (sort c) (hSort c hc)
    have hpBelow : p < (v (sort c)).level :=
      (v (sort c)).below p hpV
    have hCols := htFibre.2.2 p hpBelow
    have hJoinT :
        Etgt p (e t.level) = true ∧
        Etgt (e t.level) p = true := by
      simpa [hpV] using hCols
    have hJoinC :
        Etgt p (e c) = true ∧
        Etgt (e c) p = true := by
      simpa only [ht] using hJoinT
    exact hcw ▸ hJoinC
  have hInjC : Set.InjOn e (↑C : Set Nat) := by
    intro a _ b _ hab
    exact he hab
  have hCardImage : W.card = C.card :=
    Finset.card_image_iff.mpr hInjC
  have hRankTarget :
      W.card ≤ finiteHensonTypeRank ell Etgt P :=
    henson_targetRank_ge_futureClique
      ell H hell Etgt hAvoid P W
      hPBelow hFuture hCliqueImage hJoined
  change C.card ≤ ell - 1 - finiteDirectedCliqueCapacity Etgt P
  rw [← hCardImage]
  exact hRankTarget

/-- The REVERSE all-support target raw bound is reduced to
an explicit FINITE-SORTED JOINT CLIQUE REALIZATION premise.

For every nonempty support S, suppose the source fibres can
jointly provide a real source clique C_S whose size is the
actual raw source bound on S, and whose original vertices
have genuine source coding-node membership in their assigned
target fibres. Then raw_source(S) ≤ raw_target(S) for ALL S.

The hypothesis is exactly the unproved mixed-fibre richness
obligation: previous disjoint-marker fan and finite-gluing
theorems do NOT themselves assert these real joint cliques. -/
theorem trackFCommonRawAge_target_ge_source_of_joint_cliques
    (d ell m H : Nat) (hell : 2 ≤ ell)
    (Esrc Etgt : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (u : Fin d → HensonOneType ell Esrc)
    (v : Fin d → HensonOneType ell Etgt)
    (hVLevel : ∀ i, (v i).level = H)
    (hJoint : ∀ S : Finset (Fin d), S.Nonempty →
      ∃ C : Finset Nat, ∃ sort : Nat → Fin d,
        IsDirectedCliqueOn Esrc C ∧
        C.card = trackFCommonRawAge d ell m Esrc
          (fun i => (u i).neighbours) S ∧
        (∀ c ∈ C, sort c ∈ S) ∧
        (∀ c ∈ C,
          ∃ t : HensonOneType ell Esrc,
            t.level = c ∧
            t ∈ HensonOneType.sourceCodingFibre
              (E := Esrc) Etgt e (v (sort c)))) :
    ∀ S : Finset (Fin d), S.Nonempty →
      trackFCommonRawAge d ell m Esrc
        (fun i => (u i).neighbours) S ≤
      trackFCommonRawAge d ell H Etgt
        (fun i => (v i).neighbours) S := by
  classical
  intro S hS
  obtain ⟨C, sort, hClique, hCard, hSort, hFibre⟩ :=
    hJoint S hS
  calc
    trackFCommonRawAge d ell m Esrc
        (fun i => (u i).neighbours) S =
        C.card := hCard.symm
    _ ≤ trackFCommonRawAge d ell H Etgt
        (fun i => (v i).neighbours) S :=
      trackFCommonRawAge_target_ge_sorted_source_clique
        d ell H hell Esrc Etgt hAvoid e he hInduced
        v hVLevel S C sort hSort hClique hFibre

end Kk
