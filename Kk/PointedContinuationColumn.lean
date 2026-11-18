import Kk.FiniteOldColumnAgePositive
import Kk.LinkedCliqueCapacityUpdate
import Mathlib.Tactic

/-!
# Track B: the exact complete continuation around an already selected original

English proof and independent audit precede this file in
`docs/track_b_pointed_continuation_english_audit.md`.

The old sorts may be refined by an arbitrary parent map.  A new bit map
prescribes adjacency to the SAME chosen original v.  Every other original
between the old cut and the new full cut has a zero future column.  The
common-neighbour pool and its clique capacity are computed exactly, including
all original gaps.  The enlarged parent support is a plain finite set and
need not belong to IntegerGraphSupport.

This is ordinary graph data only.  No transport of full parameter-closed Kpt
sources, corrected B3, an arbitrary diary transition, or infinite copy is claimed.
-/

namespace Kk

/-- Complete new columns with the old prefix pulled back along pi, the
specified bit at the fixed pivot v, and zeros at every other original. -/
def pointedContinuationColumn {d e : Nat}
    (b v : Nat) (c : Nat → Fin d → Bool)
    (pi : Fin e → Fin d) (beta : Fin e → Bool) : Nat → Fin e → Bool :=
  fun p u => if p < b then c p (pi u) else if p = v then beta u else false

theorem pointedContinuationColumn_old {d e : Nat}
    (b v : Nat) (c : Nat → Fin d → Bool)
    (pi : Fin e → Fin d) (beta : Fin e → Bool)
    (p : Nat) (hp : p < b) (u : Fin e) :
    pointedContinuationColumn b v c pi beta p u = c p (pi u) := by
  simp [pointedContinuationColumn, hp]

theorem pointedContinuationColumn_pivot {d e : Nat}
    (b v : Nat) (c : Nat → Fin d → Bool)
    (pi : Fin e → Fin d) (beta : Fin e → Bool)
    (hbv : b ≤ v) (u : Fin e) :
    pointedContinuationColumn b v c pi beta v u = beta u := by
  simp [pointedContinuationColumn, Nat.not_lt.mpr hbv]

theorem pointedContinuationColumn_gap {d e : Nat}
    (b v : Nat) (c : Nat → Fin d → Bool)
    (pi : Fin e → Fin d) (beta : Fin e → Bool)
    (p : Nat) (hbp : b ≤ p) (hpv : p ≠ v) (u : Fin e) :
    pointedContinuationColumn b v c pi beta p u = false := by
  simp [pointedContinuationColumn, Nat.not_lt.mpr hbp, hpv]

/-- For every nonempty refined support, all genuine intervening originals
are excluded from its common pool by their explicit zero columns.  The pivot
is included exactly when every new passing bit on that support is positive. -/
theorem pointedContinuation_common_pool {d e : Nat}
    (b v H : Nat) (c : Nat → Fin d → Bool)
    (pi : Fin e → Fin d) (beta : Fin e → Bool)
    (hbv : b ≤ v) (hvH : v < H)
    (U : Finset (Fin e)) (hU : U.Nonempty) :
    oldSupportCommonNeighbourPool (Finset.range H)
        (pointedContinuationColumn b v c pi beta) U =
      if ∀ u ∈ U, beta u = true then
        insert v (oldSupportCommonNeighbourPool (Finset.range b) c (U.image pi))
      else oldSupportCommonNeighbourPool (Finset.range b) c (U.image pi) := by
  classical
  have hImage (p : Nat) :
      (∀ t ∈ U.image pi, c p t = true) ↔
        ∀ u ∈ U, c p (pi u) = true := by
    constructor
    · intro h u hu
      exact h (pi u) (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
    · intro h t ht
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
      exact h u hu
  by_cases hAll : ∀ u ∈ U, beta u = true
  · rw [if_pos hAll]
    ext p
    constructor
    · intro hp
      obtain ⟨hpH, hBits⟩ := Finset.mem_filter.mp hp
      by_cases hpOld : p < b
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_range.mpr hpOld, (hImage p).mpr ?_⟩
        intro u hu
        simpa only [pointedContinuationColumn_old b v c pi beta p hpOld u]
          using hBits u hu
      · by_cases hpv : p = v
        · exact Finset.mem_insert.mpr (Or.inl hpv)
        · obtain ⟨u, hu⟩ := hU
          have hBit := hBits u hu
          simp [pointedContinuationColumn, hpOld, hpv] at hBit
    · intro hp
      rcases Finset.mem_insert.mp hp with hpv | hpOld
      · subst p
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_range.mpr hvH, ?_⟩
        intro u hu
        rw [pointedContinuationColumn_pivot b v c pi beta hbv u]
        exact hAll u hu
      · obtain ⟨hpb, hBits⟩ := Finset.mem_filter.mp hpOld
        have hpLt := Finset.mem_range.mp hpb
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
        intro u hu
        rw [pointedContinuationColumn_old b v c pi beta p hpLt u]
        exact (hImage p).mp hBits u hu
  · rw [if_neg hAll]
    ext p
    constructor
    · intro hp
      obtain ⟨hpH, hBits⟩ := Finset.mem_filter.mp hp
      by_cases hpOld : p < b
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_range.mpr hpOld, (hImage p).mpr ?_⟩
        intro u hu
        simpa only [pointedContinuationColumn_old b v c pi beta p hpOld u]
          using hBits u hu
      · by_cases hpv : p = v
        · subst p
          apply False.elim
          apply hAll
          intro u hu
          simpa only [pointedContinuationColumn_pivot b v c pi beta hbv u]
            using hBits u hu
        · obtain ⟨u, hu⟩ := hU
          have hBit := hBits u hu
          simp [pointedContinuationColumn, hpOld, hpv] at hBit
    · intro hp
      obtain ⟨hpb, hBits⟩ := Finset.mem_filter.mp hp
      have hpLt := Finset.mem_range.mp hpb
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
      intro u hu
      rw [pointedContinuationColumn_old b v c pi beta p hpLt u]
      exact (hImage p).mp hBits u hu

/-- Zero rows outside the old prefix and pivot do not contribute to any
nonempty common pool, although those originals remain in the full graph. -/
theorem pointedContinuation_common_pool_eq_insert {d e : Nat}
    (b v H : Nat) (c : Nat → Fin d → Bool)
    (pi : Fin e → Fin d) (beta : Fin e → Bool)
    (hbv : b ≤ v) (hvH : v < H)
    (U : Finset (Fin e)) (hU : U.Nonempty) :
    oldSupportCommonNeighbourPool (Finset.range H)
        (pointedContinuationColumn b v c pi beta) U =
      oldSupportCommonNeighbourPool (insert v (Finset.range b))
        (pointedContinuationColumn b v c pi beta) U := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hpH, hBits⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨?_, hBits⟩
    by_cases hpv : p = v
    · exact Finset.mem_insert.mpr (Or.inl hpv)
    · by_cases hpb : p < b
      · exact Finset.mem_insert_of_mem (Finset.mem_range.mpr hpb)
      · obtain ⟨u, hu⟩ := hU
        have hBit := hBits u hu
        simp [pointedContinuationColumn, hpb, hpv] at hBit
  · intro hp
    obtain ⟨hpBase, hBits⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨?_, hBits⟩
    rcases Finset.mem_insert.mp hpBase with hpv | hpb
    · subst p
      exact Finset.mem_range.mpr hvH
    · have hpLt := Finset.mem_range.mp hpb
      exact Finset.mem_range.mpr (by omega)

/-- The actual full-prefix raw bound equals the pivot-plus-old-prefix
bound. This equality needs no old-sort hypothesis for the chosen pivot. -/
theorem pointedContinuation_raw_eq_insert {d e : Nat}
    (E : Nat → Nat → Bool) (ell b v H : Nat)
    (c : Nat → Fin d → Bool)
    (pi : Fin e → Fin d) (beta : Fin e → Bool)
    (hbv : b ≤ v) (hvH : v < H) :
    finiteOldColumnRawBound E ell e (Finset.range H)
        (pointedContinuationColumn b v c pi beta) =
      finiteOldColumnRawBound E ell e (insert v (Finset.range b))
        (pointedContinuationColumn b v c pi beta) := by
  funext U
  unfold finiteOldColumnRawBound
  rw [pointedContinuation_common_pool_eq_insert b v H c pi beta hbv hvH U.1 U.2.1]

/-- The mutual old neighbours of the chosen pivot inside a common pool
are exactly the common pool for the old support enlarged by its old sort. -/
theorem pointedContinuation_mutual_pool {d : Nat}
    (E : Nat → Nat → Bool) (b v : Nat)
    (c : Nat → Fin d → Bool) (s : Fin d)
    (hColumn : ∀ p, p < b → E p v = c p s ∧ E v p = c p s)
    (S : Finset (Fin d)) :
    mutualLinkedNeighbours E
        (oldSupportCommonNeighbourPool (Finset.range b) c S) v =
      oldSupportCommonNeighbourPool (Finset.range b) c (insert s S) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hpPool, hForward, hReverse⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpb, hBits⟩ := Finset.mem_filter.mp hpPool
    have hpLt := Finset.mem_range.mp hpb
    apply Finset.mem_filter.mpr
    refine ⟨hpb, ?_⟩
    intro t ht
    rcases Finset.mem_insert.mp ht with hts | htS
    · subst t
      exact (hColumn p hpLt).1.symm.trans hForward
    · exact hBits t htS
  · intro hp
    obtain ⟨hpb, hBits⟩ := Finset.mem_filter.mp hp
    have hpLt := Finset.mem_range.mp hpb
    have hAtS := hBits s (Finset.mem_insert_self s S)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hpb, ?_⟩, ?_, ?_⟩
    · intro t ht
      exact hBits t (Finset.mem_insert_of_mem ht)
    · exact (hColumn p hpLt).1.trans hAtS
    · exact (hColumn p hpLt).2.trans hAtS

/-- Exact capacity on every nonempty new support, allowing repeated
parents and an enlarged parent support outside IntegerGraphSupport. -/
theorem pointedContinuation_capacity {d e : Nat}
    (E : Nat → Nat → Bool) (b v H : Nat)
    (c : Nat → Fin d → Bool) (s : Fin d)
    (pi : Fin e → Fin d) (beta : Fin e → Bool)
    (hbv : b ≤ v) (hvH : v < H)
    (hColumn : ∀ p, p < b → E p v = c p s ∧ E v p = c p s)
    (U : Finset (Fin e)) (hU : U.Nonempty) :
    finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range H)
          (pointedContinuationColumn b v c pi beta) U) =
      if ∀ u ∈ U, beta u = true then
        max
          (finiteDirectedCliqueCapacity E
            (oldSupportCommonNeighbourPool (Finset.range b) c (U.image pi)))
          (1 + finiteDirectedCliqueCapacity E
            (oldSupportCommonNeighbourPool (Finset.range b) c
              (insert s (U.image pi))))
      else finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b) c (U.image pi)) := by
  classical
  rw [pointedContinuation_common_pool b v H c pi beta hbv hvH U hU]
  by_cases hAll : ∀ u ∈ U, beta u = true
  · rw [if_pos hAll, if_pos hAll]
    have hvNot : v ∉ oldSupportCommonNeighbourPool (Finset.range b) c (U.image pi) := by
      intro hv
      have hvb := Finset.mem_range.mp (Finset.mem_filter.mp hv).1
      omega
    rw [finiteDirectedCliqueCapacity_insert_eq E _ v hvNot]
    rw [pointedContinuation_mutual_pool E b v c s hColumn]
  · rw [if_neg hAll, if_neg hAll]

/-- The constructed successor raw bound, expressed using only the old
complete columns, the pivot's old sort, and the new parent and bit maps. -/
noncomputable def pointedContinuationRawBound {d e : Nat}
    (E : Nat → Nat → Bool) (ell b : Nat)
    (c : Nat → Fin d → Bool) (s : Fin d)
    (pi : Fin e → Fin d) (beta : Fin e → Bool) :
    IntegerGraphSupport e ell → Nat := by
  classical
  exact fun U => ell - 1 -
    (if ∀ u ∈ U.1, beta u = true then
      max
        (finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool (Finset.range b) c (U.1.image pi)))
        (1 + finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool (Finset.range b) c
            (insert s (U.1.image pi))))
    else finiteDirectedCliqueCapacity E
      (oldSupportCommonNeighbourPool (Finset.range b) c (U.1.image pi)))

/-- The full actual prefix has exactly the explicit successor raw bound
on ALL supports simultaneously; no original gap is removed from the graph. -/
theorem pointedContinuation_raw_bound {d e : Nat}
    (E : Nat → Nat → Bool) (ell b v H : Nat)
    (c : Nat → Fin d → Bool) (s : Fin d)
    (pi : Fin e → Fin d) (beta : Fin e → Bool)
    (hbv : b ≤ v) (hvH : v < H)
    (hColumn : ∀ p, p < b → E p v = c p s ∧ E v p = c p s) :
    finiteOldColumnRawBound E ell e (Finset.range H)
        (pointedContinuationColumn b v c pi beta) =
      pointedContinuationRawBound E ell b c s pi beta := by
  classical
  funext U
  unfold finiteOldColumnRawBound pointedContinuationRawBound
  rw [pointedContinuation_capacity E b v H c s pi beta hbv hvH hColumn U.1 U.2.1]

/-- Exact one-vertex branch test.  A zero child needs only its old singleton
certificate.  A positive child additionally needs its common old neighbours
with the pivot's sort to have capacity strictly below ell-2. -/
theorem pointedContinuation_singleton_safe_iff {d e : Nat}
    (E : Nat → Nat → Bool) (ell b v H : Nat)
    (c : Nat → Fin d → Bool) (s : Fin d)
    (pi : Fin e → Fin d) (beta : Fin e → Bool)
    (hbv : b ≤ v) (hvH : v < H)
    (hColumn : ∀ p, p < b → E p v = c p s ∧ E v p = c p s)
    (u : Fin e) :
    finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range H)
          (pointedContinuationColumn b v c pi beta) {u}) < ell - 1 ↔
      finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool (Finset.range b) c {pi u}) < ell - 1 ∧
        (beta u = true →
          1 + finiteDirectedCliqueCapacity E
            (oldSupportCommonNeighbourPool (Finset.range b) c
              (insert s {pi u})) < ell - 1) := by
  classical
  have hCap := pointedContinuation_capacity E b v H c s pi beta
    hbv hvH hColumn {u} (Finset.singleton_nonempty u)
  simp only [Finset.image_singleton, Finset.mem_singleton, forall_eq] at hCap
  rw [hCap]
  by_cases hBit : beta u = true
  · simp [hBit, max_lt_iff]
  · simp [hBit]

/-- Once every retained child passes the exact singleton test, the whole
jointly canonicalized successor is a genuine positive integer graph age.
Mixed clique profiles still obey all support bounds, not just these tests. -/
theorem pointedContinuation_canonical_is_age_of_safe_children {d e : Nat}
    (E : Nat → Nat → Bool) (ell b v H : Nat) (hell : 2 ≤ ell)
    (c : Nat → Fin d → Bool) (s : Fin d)
    (pi : Fin e → Fin d) (beta : Fin e → Bool)
    (hbv : b ≤ v) (hvH : v < H)
    (hColumn : ∀ p, p < b → E p v = c p s ∧ E v p = c p s)
    (hSafe : ∀ u : Fin e,
      finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool (Finset.range b) c {pi u}) < ell - 1 ∧
        (beta u = true →
          1 + finiteDirectedCliqueCapacity E
            (oldSupportCommonNeighbourPool (Finset.range b) c
              (insert s {pi u})) < ell - 1)) :
    IsIntegerGraphAge e ell
      (integerGraphAgeCanonical e ell
        (pointedContinuationRawBound E ell b c s pi beta)) := by
  rw [← pointedContinuation_raw_bound E ell b v H c s pi beta hbv hvH hColumn]
  apply finiteOldColumnCanonical_is_age_of_singleton_safe E ell e hell
    (Finset.range H) (pointedContinuationColumn b v c pi beta)
  intro u
  have hSingle := (pointedContinuation_singleton_safe_iff E ell b v H c s
    pi beta hbv hvH hColumn u).mpr (hSafe u)
  simpa [oldSupportCommonNeighbourPool] using hSingle

/-- A literal one-vertex normalized vector is feasible exactly when its
complete old singleton neighbourhood has no clique of size ell-1. -/
theorem finiteOldColumn_one_vertex_feasible_iff
    (E : Nat → Nat → Bool) (ell d : Nat) (hell : 2 ≤ ell)
    (P : Finset Nat) (c : Nat → Fin d → Bool) (u : Fin d) :
    let hSize : ({0} : Finset Nat).card < ell := by simp; omega
    let w := integerCliqueWeightsOfFinset (fun _ : Nat => u) {0} hSize
    WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell))
        (finiteOldColumnRawBound E ell d P c) w ↔
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool P c {u}) < ell - 1 := by
  classical
  dsimp only
  let hSize : ({0} : Finset Nat).card < ell := by simp; omega
  let w := integerCliqueWeightsOfFinset (fun _ : Nat => u) {0} hSize
  have hMass (U : IntegerGraphSupport d ell) :
      integerCliqueOnSupport w U = if u ∈ U.1 then 1 else 0 := by
    rw [integerCliqueOnSupport_of_finset]
    by_cases hu : u ∈ U.1
    · simp [hu]
    · simp [hu]
  change WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell))
      (finiteOldColumnRawBound E ell d P c) w ↔ _
  constructor
  · intro hW
    let U : IntegerGraphSupport d ell := ⟨{u}, by constructor <;> simp; omega⟩
    have hOne : integerCliqueOnSupport w U = 1 := by
      rw [hMass]
      simp [U]
    have hBound := hW U
    rw [hOne] at hBound
    change 1 ≤ ell - 1 -
      finiteDirectedCliqueCapacity E (oldSupportCommonNeighbourPool P c {u}) at hBound
    omega
  · intro hSingle U
    rw [hMass]
    by_cases hu : u ∈ U.1
    · rw [if_pos hu]
      have hSub : oldSupportCommonNeighbourPool P c U.1 ⊆
          oldSupportCommonNeighbourPool P c {u} := by
        intro p hp
        obtain ⟨hpP, hBits⟩ := Finset.mem_filter.mp hp
        apply Finset.mem_filter.mpr
        refine ⟨hpP, ?_⟩
        intro t ht
        have htu := Finset.mem_singleton.mp ht
        subst t
        exact hBits u hu
      have hCap := finiteDirectedCliqueCapacity_mono E
        (oldSupportCommonNeighbourPool P c U.1)
        (oldSupportCommonNeighbourPool P c {u}) hSub
      unfold finiteOldColumnRawBound
      omega
    · rw [if_neg hu]
      exact Nat.zero_le _

/-- The proposed child has an actual feasible singleton vector precisely
under the explicit old and old-with-pivot capacity tests. Unsafe branches are
therefore absent from the constructed universal future, not silently positive. -/
theorem pointedContinuation_one_vertex_feasible_iff {d e : Nat}
    (E : Nat → Nat → Bool) (ell b v H : Nat) (hell : 2 ≤ ell)
    (c : Nat → Fin d → Bool) (s : Fin d)
    (pi : Fin e → Fin d) (beta : Fin e → Bool)
    (hbv : b ≤ v) (hvH : v < H)
    (hColumn : ∀ p, p < b → E p v = c p s ∧ E v p = c p s)
    (u : Fin e) :
    let hSize : ({0} : Finset Nat).card < ell := by simp; omega
    let w := integerCliqueWeightsOfFinset (fun _ : Nat => u) {0} hSize
    WitnessRespects (integerCliqueOnSupport (d := e) (ell := ell))
        (pointedContinuationRawBound E ell b c s pi beta) w ↔
      finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool (Finset.range b) c {pi u}) < ell - 1 ∧
        (beta u = true →
          1 + finiteDirectedCliqueCapacity E
            (oldSupportCommonNeighbourPool (Finset.range b) c
              (insert s {pi u})) < ell - 1) := by
  rw [← pointedContinuation_raw_bound E ell b v H c s pi beta hbv hvH hColumn]
  exact (finiteOldColumn_one_vertex_feasible_iff E ell e hell
    (Finset.range H) (pointedContinuationColumn b v c pi beta) u).trans
      (pointedContinuation_singleton_safe_iff E ell b v H c s pi beta
        hbv hvH hColumn u)

#print axioms Kk.pointedContinuation_common_pool
#print axioms Kk.pointedContinuation_raw_eq_insert
#print axioms Kk.pointedContinuation_mutual_pool
#print axioms Kk.pointedContinuation_capacity
#print axioms Kk.pointedContinuation_raw_bound
#print axioms Kk.pointedContinuation_singleton_safe_iff
#print axioms Kk.pointedContinuation_canonical_is_age_of_safe_children
#print axioms Kk.finiteOldColumn_one_vertex_feasible_iff
#print axioms Kk.pointedContinuation_one_vertex_feasible_iff

end Kk
