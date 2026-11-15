import Kk.TrackFMultiSortRawIsolation
import Mathlib.Tactic

/-!
# Track F: all-support raw-age isolation for disjoint daughter markers

English proof and hostile audit committed first in:
docs/track_f_disjoint_daughter_markers_english_audit.md

The finite sets U_i are ACTUAL old-neighbour sets over one old prefix;
V_i are pairwise-disjoint positive-coordinate sets in a fresh finite
interval. Complete common-neighbour pools are preserved on EVERY
support containing two distinct refined sorts. No diary or
big-Ramsey-degree assertion is assumed.

This is the multi-daughter local combinatorial ingredient of the
rank-large richness induction. It does not construct rank-large
daughter fibres nor show the full diary lower bound.
-/

namespace Kk

/-- Enlarge each old sort-neighbour set by its own fresh marker set.
Distinct sorts may have distinct old neighbourhoods; the only
restriction on fresh sets will be pairwise disjointness. -/
def trackFAddDisjointMarkers
    (d : Nat) (U V : Fin d → Finset Nat) : Fin d → Finset Nat :=
  fun i => U i ∪ V i

/-- Every newly extended sort neighbourhood stays inside the later
finite prefix under explicit old/fresh location assumptions. -/
theorem trackFAddDisjointMarkers_below
    (d m n : Nat) (hmn : m ≤ n)
    (U V : Fin d → Finset Nat)
    (hOld : ∀ i x, x ∈ U i → x < m)
    (hFresh : ∀ i x, x ∈ V i → m ≤ x ∧ x < n) :
    ∀ i x, x ∈ trackFAddDisjointMarkers d U V i → x < n := by
  intro i x hx
  change x ∈ U i ∪ V i at hx
  rcases Finset.mem_union.mp hx with hxU | hxV
  · have hxOld := hOld i x hxU
    omega
  · exact (hFresh i x hxV).2

/-- The selected singleton receives exactly its own fresh marker
coordinates, including their full literal labels, with no other
old or intervening originals introduced into this pool. -/
theorem trackFCommonNeighbourPool_disjoint_singleton
    (d m n : Nat) (hmn : m ≤ n)
    (U V : Fin d → Finset Nat)
    (hOld : ∀ i x, x ∈ U i → x < m)
    (hFresh : ∀ i x, x ∈ V i → m ≤ x ∧ x < n)
    (j : Fin d) :
    trackFCommonNeighbourPool d n
      (trackFAddDisjointMarkers d U V) {j} = U j ∪ V j := by
  have hNewBelow :=
    trackFAddDisjointMarkers_below d m n hmn U V hOld hFresh
  simpa [trackFAddDisjointMarkers] using
    (trackFCommonNeighbourPool_singleton d n
      (trackFAddDisjointMarkers d U V) hNewBelow j)

/-- Crucial multi-sort isolation theorem. If at least two distinct
sort indices occur in S and NO fresh positive marker belongs to
two different sorts, the common-neighbour pool on S is exactly the
old one. No size bound on S is needed (so triple supports are covered). -/
theorem trackFCommonNeighbourPool_disjoint_fresh
    (d m n : Nat) (hmn : m ≤ n)
    (U V : Fin d → Finset Nat)
    (hOld : ∀ i x, x ∈ U i → x < m)
    (hFresh : ∀ i x, x ∈ V i → m ≤ x ∧ x < n)
    (hDisj : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (S : Finset (Fin d))
    (hTwo : ∃ i ∈ S, ∃ j ∈ S, i ≠ j) :
    trackFCommonNeighbourPool d n
      (trackFAddDisjointMarkers d U V) S =
    trackFCommonNeighbourPool d m U S := by
  classical
  obtain ⟨i, hiS, j, hjS, hij⟩ := hTwo
  ext x
  simp only [trackFCommonNeighbourPool, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨hxN, hAll⟩
    have hxM : x < m := by
      by_contra hNot
      have hxm : m ≤ x := Nat.le_of_not_gt hNot
      have hiNew : x ∈ U i ∪ V i := by
        simpa [trackFAddDisjointMarkers] using hAll i hiS
      have hjNew : x ∈ U j ∪ V j := by
        simpa [trackFAddDisjointMarkers] using hAll j hjS
      have hiOld : x ∉ U i := by
        intro hxU
        have hxLt := hOld i x hxU
        omega
      have hjOld : x ∉ U j := by
        intro hxU
        have hxLt := hOld j x hxU
        omega
      have hVi : x ∈ V i :=
        (Finset.mem_union.mp hiNew).resolve_left hiOld
      have hVj : x ∈ V j :=
        (Finset.mem_union.mp hjNew).resolve_left hjOld
      exact (Finset.disjoint_left.mp (hDisj i j hij)) hVi hVj
    refine ⟨hxM, ?_⟩
    intro k hk
    have hkNew : x ∈ U k ∪ V k := by
      simpa [trackFAddDisjointMarkers] using hAll k hk
    rcases Finset.mem_union.mp hkNew with hxU | hxV
    · exact hxU
    · have hxFresh := (hFresh k x hxV).1
      omega
  · rintro ⟨hxM, hAllOld⟩
    refine ⟨by omega, ?_⟩
    intro k hk
    have hxUk : x ∈ U k := hAllOld k hk
    change x ∈ U k ∪ V k
    exact Finset.mem_union.mpr (Or.inl hxUk)

/-- Exact raw directed-clique age preservation on all supports
containing at least two distinct sorts, for arbitrary finite
pairwise-disjoint fresh-marker sets and actual old edge table E. -/
theorem trackFCommonRawAge_disjoint_fresh
    (d ell m n : Nat) (hmn : m ≤ n)
    (E : Nat → Nat → Bool)
    (U V : Fin d → Finset Nat)
    (hOld : ∀ i x, x ∈ U i → x < m)
    (hFresh : ∀ i x, x ∈ V i → m ≤ x ∧ x < n)
    (hDisj : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (S : Finset (Fin d))
    (hTwo : ∃ i ∈ S, ∃ j ∈ S, i ≠ j) :
    trackFCommonRawAge d ell n E
      (trackFAddDisjointMarkers d U V) S =
      trackFCommonRawAge d ell m E U S := by
  unfold trackFCommonRawAge
  rw [trackFCommonNeighbourPool_disjoint_fresh
    d m n hmn U V hOld hFresh hDisj S hTwo]

/-- Concrete failure of the same conclusion WITHOUT disjointness:
one fresh original belongs to both sorts, so their common pool
grows. The old graph and both old neighbourhoods are empty. -/
theorem trackFNonDisjointMarker_counterexample :
    trackFCommonNeighbourPool 2 1
      (trackFAddDisjointMarkers 2
        (fun _ => (∅ : Finset Nat))
        (fun _ => ({0} : Finset Nat)))
      ({0, 1} : Finset (Fin 2)) ≠
    trackFCommonNeighbourPool 2 0
      (fun _ => (∅ : Finset Nat))
      ({0, 1} : Finset (Fin 2)) := by
  decide

end Kk
