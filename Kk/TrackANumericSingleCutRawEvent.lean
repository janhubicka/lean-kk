import Kk.PartialNumericCriticalGenerations
import Kk.NumericPrefixGapZero
import Mathlib.Tactic

/-!
# Track A: genuine individual NUMERICAL H ordinary-L raw cut events

English-first proof and adversarial audit:
  docs/track_a_numeric_one_cut_english_audit_20261122.md

Track A #460 characterizes generation-boundary raw changes. This
module uses actual zero L columns of odd fake H coordinates to
localize each change to the *even physical cut*
hPosition(k,b,g), not the abstract generation index g.
No auxiliary Kpt E/I1/I2/I3/B3 or BRD claim is inferred.
-/

namespace Kk

open SuccessorTree.V10

/-- Adding any old coordinate whose column to every future sort is
FALSE does not alter a NONEMPTY U-common-neighbour old pool.
Even if z is already in P, the identity is exact. -/
theorem oldSupportCommonNeighbourPool_insert_zero_column
    {d ell : Nat} (P : Finset Nat)
    (c : Nat → Fin d → Bool) (z : Nat)
    (hz : ∀ t : Fin d, c z t = false)
    (U : IntegerGraphSupport d ell) :
    oldSupportCommonNeighbourPool (insert z P) c U.1 =
      oldSupportCommonNeighbourPool P c U.1 := by
  classical
  change (insert z P).filter (fun p => ∀ t ∈ U.1, c p t = true) =
    P.filter (fun p => ∀ t ∈ U.1, c p t = true)
  ext x
  constructor
  · intro hx
    obtain ⟨hxInsert,hAll⟩ := Finset.mem_filter.mp hx
    rcases Finset.mem_insert.mp hxInsert with hxZ | hxP
    · subst x
      obtain ⟨t,ht⟩ := U.2.1
      have hBit := hAll t ht
      rw [hz t] at hBit
      cases hBit
    · exact Finset.mem_filter.mpr ⟨hxP,hAll⟩
  · intro hx
    obtain ⟨hxP,hAll⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_insert_of_mem hxP,hAll⟩

/-- A zero old-to-future column leaves every raw clique-capacity
support bound exactly unchanged, including Nat-subtraction zero
saturation; it therefore also preserves canonical integer age. -/
theorem finiteOldColumnRawBound_insert_zero_column
    (E : Nat → Nat → Bool) (ell d : Nat)
    (P : Finset Nat) (c : Nat → Fin d → Bool)
    (z : Nat) (hz : ∀ t : Fin d, c z t = false) :
    finiteOldColumnRawBound E ell d (insert z P) c =
      finiteOldColumnRawBound E ell d P c := by
  classical
  funext U
  unfold finiteOldColumnRawBound
  rw [oldSupportCommonNeighbourPool_insert_zero_column
    P c z hz U]

/-- The complete numbered partial old binary-L raw continuation
age at an ARBITRARY numeric prefix cut. Not a selected shadow. -/
noncomputable def trackANumericRawAt
    {d : Nat} (E : Nat → Nat → Bool)
    (ell k M cut : Nat) (j : Fin d → Nat) :
    IntegerGraphSupport d ell → Nat :=
  finiteOldColumnRawBound
    (fun x y => (finiteNumericHL
      (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
    ell d (Finset.range cut)
    (fun z t => (finiteNumericHL
      (normalizedGraphModel E) k M).binary
        z (hPosition k (j t) k) (0 : Fin 1))

/-- At the physical generation boundary hPosition(k,b,g),
the literal arbitrary-cut raw function is DEFINITIONALLY the
already verified Track A old partial generation raw age. -/
theorem trackANumericRawAt_hPosition
    {d : Nat} (E : Nat → Nat → Bool)
    (ell k b g M : Nat) (j : Fin d → Nat) :
    trackANumericRawAt E ell k M (hPosition k b g) j =
      finiteNumericHPartialActualRawAt E ell k b g M j := by
  rfl

/-- Between two consecutive real b-generation positions, the
intervening ODD dummy never changes ANY ordinary-L raw support
bound. This is a statement about the true generated L table.
Auxiliary H+ E atoms of the dummy are not claimed to vanish. -/
theorem trackA_numeric_odd_dummy_raw_neutral
    {d : Nat} (E : Nat → Nat → Bool)
    (ell k b g M : Nat) (j : Fin d → Nat) :
    trackANumericRawAt E ell k M
      (hPosition k b g + 2) j =
    trackANumericRawAt E ell k M
      (hPosition k b g + 1) j := by
  classical
  let cut := hPosition k b g
  have hOdd : ∀ t : Fin d,
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (cut+1) (hPosition k (j t) k) (0 : Fin 1) = false := by
    intro t
    have hNumber : cut + 1 = 2*((k+1)*b+g)+1 := by
      dsimp [cut,hPosition]
      ring
    rw [hNumber]
    exact (finiteNumericH_odd_dummy_to_top_zero
      E k M ((k+1)*b+g) (j t)).1
  have hRange : Finset.range (cut+2) =
      insert (cut+1) (Finset.range (cut+1)) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert]
    omega
  change trackANumericRawAt E ell k M (cut+2) j =
    trackANumericRawAt E ell k M (cut+1) j
  unfold trackANumericRawAt
  rw [hRange]
  exact finiteOldColumnRawBound_insert_zero_column
    (fun x y => (finiteNumericHL
      (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
    ell d (Finset.range (cut+1))
    (fun z t => (finiteNumericHL
      (normalizedGraphModel E) k M).binary
        z (hPosition k (j t) k) (0 : Fin 1))
    (cut+1) hOdd

/-- Exact FULL raw function event at the individual EVEN NUMERIC
cut hPosition(k,b,g), g<k. It is NOT at the abstract generation
index g or the following odd dummy cut. Under genuine Henson
K_ell-freeness this event occurs precisely when g belongs to the
verified original critical generation schedule C_gen(E,b,j).
This has no implication for full dependent Kpt interestingness. -/
theorem trackA_henson_numeric_real_cut_change_iff_critical
    {d : Nat} (E : Nat → Nat → Bool)
    (ell : Nat) (hell : 2 ≤ ell)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (k b g M : Nat) (hg : g+1 ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t) :
    trackANumericRawAt E ell k M (hPosition k b g + 1) j ≠
      trackANumericRawAt E ell k M (hPosition k b g) j ↔
    g ∈ trackACriticalGenerations ell E b j := by
  have hNext : hPosition k b (g+1) = hPosition k b g + 2 := by
    dsimp [hPosition]
    ring
  have hNew :
      finiteNumericHPartialActualRawAt E ell k b (g+1) M j =
        trackANumericRawAt E ell k M (hPosition k b g + 1) j := by
    calc
      finiteNumericHPartialActualRawAt E ell k b (g+1) M j =
          trackANumericRawAt E ell k M
            (hPosition k b (g+1)) j := rfl
      _ = trackANumericRawAt E ell k M
            (hPosition k b g + 2) j := by rw [hNext]
      _ = trackANumericRawAt E ell k M
            (hPosition k b g + 1) j :=
          trackA_numeric_odd_dummy_raw_neutral E ell k b g M j
  have hOld :
      finiteNumericHPartialActualRawAt E ell k b g M j =
        trackANumericRawAt E ell k M (hPosition k b g) j := rfl
  have hGen :=
    trackA_henson_raw_change_iff_critical_generation
      E ell hell hAvoid k b g (g+1) M (by omega) hg j hj
  rw [hNew,hOld] at hGen
  constructor
  · intro hRaw
    obtain ⟨p,hMem,hLow,hHigh⟩ := hGen.mp hRaw
    have hEq : p=g := by omega
    simpa [hEq] using hMem
  · intro hCritical
    exact hGen.mpr ⟨g,hCritical,by omega,by omega⟩

#print axioms Kk.oldSupportCommonNeighbourPool_insert_zero_column
#print axioms Kk.finiteOldColumnRawBound_insert_zero_column
#print axioms Kk.trackANumericRawAt_hPosition
#print axioms Kk.trackA_numeric_odd_dummy_raw_neutral
#print axioms Kk.trackA_henson_numeric_real_cut_change_iff_critical

end Kk
