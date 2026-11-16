import Kk.TrackFDisjointDaughterMarkers
import Kk.FiniteCliqueIntegerWitness
import Mathlib.Tactic

/-!
# Track F: collapse labelled clique patterns from daughters to old parents

The English-first proof and hostile audit are in:
docs/track_f_collapse_clique_feasibility_english_audit.md

This connects exact ACTUAL old-neighbour raw support locality to
finite labelled clique feasibility. It does not presuppose a diary
count or a global big Ramsey lower bound.

The crucial hypotheses are: each daughter holds at most one of the
chosen future vertices; every daughter singleton raw capacity is
at least 1; and multi-sort raw capacities are exact pullbacks
from the parent support. Canonical ages can change numerically,
but the previously verified canonicalizer preserves feasible
integer clique vectors.
-/

namespace Kk

/-- On a single OLD prefix, the common-neighbour pool of pulled-back
daughter neighbourhoods is exactly the original parent common pool
on the image support. The map π need not be injective. -/
theorem trackFCommonNeighbourPool_pullback
    (d p m : Nat) (π : Fin d → Fin p)
    (U : Fin p → Finset Nat) (S : Finset (Fin d)) :
    trackFCommonNeighbourPool d m (fun i => U (π i)) S =
      trackFCommonNeighbourPool p m U (S.image π) := by
  classical
  ext x
  simp only [trackFCommonNeighbourPool, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨hx, hAll⟩
    refine ⟨hx, ?_⟩
    intro j hj
    obtain ⟨i, hi, hji⟩ := Finset.mem_image.mp hj
    have hxi : x ∈ U (π i) := hAll i hi
    simpa only [hji] using hxi
  · rintro ⟨hx, hAll⟩
    refine ⟨hx, ?_⟩
    intro i hi
    exact hAll (π i)
      (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

/-- Actual raw directed-clique ages pull back along sort duplication
for every OLD finite prefix, without any fresh markers. -/
theorem trackFCommonRawAge_pullback
    (d p ell m : Nat)
    (E : Nat → Nat → Bool)
    (π : Fin d → Fin p)
    (U : Fin p → Finset Nat)
    (S : Finset (Fin d)) :
    trackFCommonRawAge d ell m E (fun i => U (π i)) S =
      trackFCommonRawAge p ell m E U (S.image π) := by
  unfold trackFCommonRawAge
  rw [trackFCommonNeighbourPool_pullback d p m π U S]

/-- Add mutually disjoint FRESH marker sets to actual Henson
daughter neighbourhoods. On a support with at least two daughter
sorts, the raw age is exactly the old parent raw age after collapse.
This includes different daughters from the SAME old parent. -/
theorem trackFCommonRawAge_disjoint_collapse
    (d p ell m n : Nat) (hmn : m ≤ n)
    (E : Nat → Nat → Bool)
    (π : Fin d → Fin p)
    (U : Fin p → Finset Nat)
    (V : Fin d → Finset Nat)
    (hOld : ∀ i x, x ∈ U (π i) → x < m)
    (hFresh : ∀ i x, x ∈ V i → m ≤ x ∧ x < n)
    (hDisj : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (S : Finset (Fin d))
    (hTwo : ∃ i ∈ S, ∃ j ∈ S, i ≠ j) :
    trackFCommonRawAge d ell n E
      (trackFAddDisjointMarkers d (fun i => U (π i)) V) S =
      trackFCommonRawAge p ell m E U (S.image π) := by
  calc
    trackFCommonRawAge d ell n E
        (trackFAddDisjointMarkers d (fun i => U (π i)) V) S =
      trackFCommonRawAge d ell m E (fun i => U (π i)) S :=
        trackFCommonRawAge_disjoint_fresh
          d ell m n hmn E (fun i => U (π i)) V
          hOld hFresh hDisj S hTwo
    _ = trackFCommonRawAge p ell m E U (S.image π) :=
        trackFCommonRawAge_pullback d p ell m E π U S

/-- A finite future labelled clique which already obeys every old
PARENT support bound remains feasible after allocating at most ONE
vertex to each new daughter, provided singleton daughter ranks
stay positive and all MULTI-daughter raw bounds are exact pullbacks.

The theorem uses literal vertex-set filter cardinalities rather
than an assumed diary count. It does not claim that the refinement
can be physically realized in a chosen Henson subcopy. -/
theorem trackFCollapse_single_occupied_preserves_raw
    (d p : Nat)
    (π : Fin d → Fin p)
    (sort : Nat → Fin d)
    (B : Finset Nat)
    (oldRaw : Finset (Fin p) → Nat)
    (newRaw : Finset (Fin d) → Nat)
    (hOld : ∀ T : Finset (Fin p), T.Nonempty →
      (B.filter (fun x => π (sort x) ∈ T)).card ≤ oldRaw T)
    (hOne : ∀ i : Fin d,
      (B.filter (fun x => sort x = i)).card ≤ 1)
    (hNewOne : ∀ i : Fin d, 1 ≤ newRaw {i})
    (hMixed : ∀ S : Finset (Fin d), 2 ≤ S.card →
      newRaw S = oldRaw (S.image π)) :
    ∀ S : Finset (Fin d), S.Nonempty →
      (B.filter (fun x => sort x ∈ S)).card ≤ newRaw S := by
  classical
  intro S hS
  by_cases hSingleton : S.card = 1
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hSingleton
    subst S
    calc
      (B.filter (fun x => sort x ∈ ({i} : Finset (Fin d)))).card ≤ 1 := by
        simpa only [Finset.mem_singleton] using hOne i
      _ ≤ newRaw {i} := hNewOne i
  · have hPos : 0 < S.card := Finset.card_pos.mpr hS
    have hTwo : 2 ≤ S.card := by omega
    have hImageNonempty : (S.image π).Nonempty := by
      obtain ⟨i, hi⟩ := hS
      exact ⟨π i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
    have hSubset :
        B.filter (fun x => sort x ∈ S) ⊆
          B.filter (fun x => π (sort x) ∈ S.image π) := by
      intro x hx
      obtain ⟨hxB, hxS⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr
        ⟨hxB, Finset.mem_image.mpr ⟨sort x, hxS, rfl⟩⟩
    calc
      (B.filter (fun x => sort x ∈ S)).card ≤
          (B.filter (fun x => π (sort x) ∈ S.image π)).card :=
        Finset.card_le_card hSubset
      _ ≤ oldRaw (S.image π) := hOld (S.image π) hImageNonempty
      _ = newRaw S := (hMixed S hTwo).symm

end Kk
