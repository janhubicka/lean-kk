import Kk.TrackFRealHensonRankDrop
import Kk.IsolatedBlockContinuationAge
import Mathlib.Tactic

/-!
# Track F: exact one-coordinate locality of genuine sorted Henson raw ages

English proof and hostile audit were committed before Lean in
docs/track_f_multisort_single_coordinate_isolation_english_audit.md.

All support pools are computed from finite old neighbourhoods of
ACTUAL vertices of the fixed Henson graph. No diary recurrence,
new axioms or already-assumed lower-bound characterization is used.

The conclusion is EXACT RAW-BOUND LOCALITY; canonical graph-age values
on mixed supports may still change as a consequence of the new
singleton constraint. This module does NOT certify simultaneous
multi-sort richness, arbitrary self-embedding transport or a BRD.
-/

namespace Kk

/-- Common old-neighbourhood vertices for a selected finite support
of sorts. For the empty support this is the entire old prefix;
graph-age statements below concern nonempty supports only. -/
def trackFCommonNeighbourPool
    (d front : Nat) (U : Fin d → Finset Nat)
    (S : Finset (Fin d)) : Finset Nat :=
  (Finset.range front).filter
    (fun x => ∀ i ∈ S, x ∈ U i)

/-- Exactly one coordinate receives 1 at the newly added original v;
all other active types receive 0 there and through the gaps. -/
def trackFAddToOneSort (d : Nat)
    (U : Fin d → Finset Nat) (j : Fin d) (v : Nat) :
    Fin d → Finset Nat :=
  fun i => if i = j then insert v (U i) else U i

/-- The common old-neighbourhood pool for one singleton support is
literally its finite neighbour set when that set lies below front. -/
theorem trackFCommonNeighbourPool_singleton
    (d front : Nat) (U : Fin d → Finset Nat)
    (hBelow : ∀ i x, x ∈ U i → x < front)
    (j : Fin d) :
    trackFCommonNeighbourPool d front U {j} = U j := by
  classical
  ext x
  simp only [trackFCommonNeighbourPool, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨_, hAll⟩
    exact hAll j (by simp)
  · intro hx
    refine ⟨hBelow j x hx, ?_⟩
    intro i hi
    have hij : i = j := Finset.mem_singleton.mp hi
    simpa [hij] using hx

/-- The one-sort insertion still defines complete finite prefix
neighbour sets on [0,v+1). -/
theorem trackFAddToOneSort_below
    (d front v : Nat) (hfv : front ≤ v)
    (U : Fin d → Finset Nat)
    (hBelow : ∀ i x, x ∈ U i → x < front)
    (j : Fin d) :
    ∀ i x, x ∈ trackFAddToOneSort d U j v i → x < v + 1 := by
  intro i x hx
  by_cases hij : i = j
  · have hInsert : x ∈ insert v (U i) := by
      simpa [trackFAddToOneSort, hij] using hx
    rcases Finset.mem_insert.mp hInsert with hxV | hxU
    · omega
    · have hOld := hBelow i x hxU
      omega
  · have hOld : x ∈ U i := by
      simpa [trackFAddToOneSort, hij] using hx
    have hxOld := hBelow i x hOld
    omega

/-- The singleton selected support gains exactly the newly coded
old original and no other old vertex or numerical gap. -/
theorem trackFCommonNeighbourPool_selected_singleton
    (d front v : Nat) (hfv : front ≤ v)
    (U : Fin d → Finset Nat)
    (hBelow : ∀ i x, x ∈ U i → x < front)
    (j : Fin d) :
    trackFCommonNeighbourPool d (v + 1)
      (trackFAddToOneSort d U j v) {j} =
        insert v (U j) := by
  have hNewBelow :=
    trackFAddToOneSort_below d front v hfv U hBelow j
  simpa [trackFAddToOneSort] using
    (trackFCommonNeighbourPool_singleton d (v + 1)
      (trackFAddToOneSort d U j v) hNewBelow j)

/-- On ANY support containing a sort other than j, adding v
exclusively to the jth type leaves the complete old common-neighbour
pool literally unchanged. This includes all pair/triple supports. -/
theorem trackFCommonNeighbourPool_other
    (d front v : Nat) (hfv : front ≤ v)
    (U : Fin d → Finset Nat)
    (hBelow : ∀ i x, x ∈ U i → x < front)
    (j : Fin d) (S : Finset (Fin d))
    (hOther : ∃ i ∈ S, i ≠ j) :
    trackFCommonNeighbourPool d (v + 1)
      (trackFAddToOneSort d U j v) S =
        trackFCommonNeighbourPool d front U S := by
  classical
  obtain ⟨i, hiS, hij⟩ := hOther
  ext x
  simp only [trackFCommonNeighbourPool, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨_, hAll⟩
    have hxi : x ∈ U i := by
      have hxNew := hAll i hiS
      simpa [trackFAddToOneSort, hij] using hxNew
    have hxOld : x < front := hBelow i x hxi
    refine ⟨hxOld, ?_⟩
    intro k hk
    have hxNew := hAll k hk
    by_cases hkj : k = j
    · have hInsert : x ∈ insert v (U k) := by
        simpa [trackFAddToOneSort, hkj] using hxNew
      rcases Finset.mem_insert.mp hInsert with hxV | hxU
      · have hxNe : x ≠ v := by omega
        exact False.elim (hxNe hxV)
      · exact hxU
    · simpa [trackFAddToOneSort, hkj] using hxNew
  · rintro ⟨hxOld, hAll⟩
    refine ⟨by omega, ?_⟩
    intro k hk
    have hxUk : x ∈ U k := hAll k hk
    by_cases hkj : k = j
    · have hInsert : x ∈ insert v (U k) :=
        Finset.mem_insert_of_mem hxUk
      simpa [trackFAddToOneSort, hkj] using hInsert
    · simpa [trackFAddToOneSort, hkj] using hxUk

/-- Raw old clique bound for a support, using the ACTUAL directed
edge table and maximum clique on the genuine common-neighbour pool.
On empty support this is only an auxiliary numerical convention. -/
def trackFCommonRawAge (d ell front : Nat)
    (E : Nat → Nat → Bool)
    (U : Fin d → Finset Nat) (S : Finset (Fin d)) : Nat :=
  ell - 1 -
    finiteDirectedCliqueCapacity E
      (trackFCommonNeighbourPool d front U S)

/-- Every mixed support containing another active sort has the same
raw clique capacity and raw age before and after the isolated drop.
No canonicalized age-invariance is asserted. -/
theorem trackFCommonRawAge_other
    (d ell front v : Nat) (hfv : front ≤ v)
    (E : Nat → Nat → Bool)
    (U : Fin d → Finset Nat)
    (hBelow : ∀ i x, x ∈ U i → x < front)
    (j : Fin d) (S : Finset (Fin d))
    (hOther : ∃ i ∈ S, i ≠ j) :
    trackFCommonRawAge d ell (v + 1) E
        (trackFAddToOneSort d U j v) S =
      trackFCommonRawAge d ell front E U S := by
  unfold trackFCommonRawAge
  rw [trackFCommonNeighbourPool_other d front v hfv U hBelow j S hOther]

/-- The exact singleton capacity increment lowers its raw age by
precisely one. The rank≥2 hypothesis prevents Nat subtraction
from saturating and guarantees the new bound is still positive. -/
theorem trackFCommonRawAge_selected_drop
    (d ell front v : Nat) (hfv : front ≤ v)
    (E : Nat → Nat → Bool)
    (U : Fin d → Finset Nat)
    (hBelow : ∀ i x, x ∈ U i → x < front)
    (j : Fin d)
    (hCap : finiteDirectedCliqueCapacity E (insert v (U j)) =
      finiteDirectedCliqueCapacity E (U j) + 1)
    (hEnough : finiteDirectedCliqueCapacity E (U j) + 3 ≤ ell) :
    trackFCommonRawAge d ell (v + 1) E
      (trackFAddToOneSort d U j v) {j} + 1 =
        trackFCommonRawAge d ell front E U {j} := by
  unfold trackFCommonRawAge
  rw [trackFCommonNeighbourPool_selected_singleton
        d front v hfv U hBelow j,
      trackFCommonNeighbourPool_singleton d front U hBelow j,
      hCap]
  omega

/-- GENUINE Henson version of single-coordinate rank-drop locality.
The witness is one actual later original whose complete incoming
L-column is fixed, and every mixed raw support stays exact.
The full graph-age canonicalizer is not assumed to preserve mixed
canonical values. -/
theorem henson_leftDense_one_sort_raw_age_drop
    (d ell : Nat) (hell : 3 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell (by omega) →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (front : Nat) (U : Fin d → Finset Nat)
    (hBelow : ∀ i x, x ∈ U i → x < front)
    (j : Fin d)
    (hEnough : finiteDirectedCliqueCapacity E (U j) + 3 ≤ ell) :
    ∃ (C : Finset Nat) (v : Nat),
      C ⊆ U j ∧ front ≤ v ∧
      (∀ x, x < v →
        E x v = decide (x ∈ C) ∧ E v x = decide (x ∈ C)) ∧
      (∀ S : Finset (Fin d), (∃ i ∈ S, i ≠ j) →
        trackFCommonRawAge d ell (v + 1) E
          (trackFAddToOneSort d U j v) S =
        trackFCommonRawAge d ell front E U S) ∧
      trackFCommonRawAge d ell (v + 1) E
        (trackFAddToOneSort d U j v) {j} + 1 =
      trackFCommonRawAge d ell front E U {j} := by
  obtain ⟨C, v, hCU, _hClique, _hCcard, hv, hColumn,
    hCap, _hSafe, _hRank⟩ :=
      henson_leftDense_exact_type_rank_drop
        ell hell E hAvoid hDense front (U j) (hBelow j) hEnough
  refine ⟨C, v, hCU, hv, hColumn, ?_, ?_⟩
  · intro S hOther
    exact trackFCommonRawAge_other
      d ell front v hv E U hBelow j S hOther
  · exact trackFCommonRawAge_selected_drop
      d ell front v hv E U hBelow j hCap hEnough

end Kk
