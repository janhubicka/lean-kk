import Kk.TrackANumericSingleCutRawEvent
import Kk.TrackAKptResidualDefectBudget
import Mathlib.Tactic

/-!
# Track A: exact actual physical non-top real raw critical cut spectrum

English FIRST and adversarial proof:
docs/track_a_exact_physical_critical_spectrum_english_audit_20261122.md

The already verified generation critical schedule is mapped through the
TRUE hPosition(k,b,g). These results identify its literal ordinary-L
raw-event numeric coordinates and prove all ODD numerical cuts carry
zero binary-L old-to-top raw-age change. They do not certify full
dependent Kpt I1/I2/I3/E/B3 boringness or global Ramsey degrees.
-/

namespace Kk

open SuccessorTree.V10

/-- ANY odd numerical H coordinate is ordinary-L raw-neutral on
every nonempty support, regardless of original graph symmetry,
K_ell-freeness or the chosen earlier original block.
The generated odd-to-top L column is literally zero.
This does not assert absence of auxiliary H+ E incidence. -/
theorem trackA_numeric_all_odd_raw_neutral
    {d : Nat} (E : Nat → Nat → Bool)
    (ell k M a : Nat) (j : Fin d → Nat) :
    trackANumericRawAt E ell k M (2*a+2) j =
      trackANumericRawAt E ell k M (2*a+1) j := by
  classical
  have hOdd : ∀ t : Fin d,
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (2*a+1) (hPosition k (j t) k) (0 : Fin 1) = false := by
    intro t
    exact (finiteNumericH_odd_dummy_to_top_zero E k M a (j t)).1
  have hRange : Finset.range (2*a+2) =
      insert (2*a+1) (Finset.range (2*a+1)) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert]
    omega
  unfold trackANumericRawAt
  rw [hRange]
  exact finiteOldColumnRawBound_insert_zero_column
    (fun x y => (finiteNumericHL
      (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
    ell d (Finset.range (2*a+1))
    (fun z t => (finiteNumericHL
      (normalizedGraphModel E) k M).binary
        z (hPosition k (j t) k) (0 : Fin 1))
    (2*a+1) hOdd

/-- The previously verified finite hPosition image of the original
critical GENERATIONS is EXACTLY the set of individual numerical
even real-copy cuts in the current original b block (g<k)
which genuinely change the full numbered-prefix ordinary L RAW age.
This compares actual raw support FUNCTIONS, not just one support
or a selected diary shadow. -/
theorem trackA_henson_physical_critical_cut_iff_actual_raw_event
    {d : Nat} (E : Nat → Nat → Bool)
    (ell : Nat) (hell : 2 ≤ ell)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (k b M : Nat) (j : Fin d → Nat) (hj : ∀ t, b < j t)
    (cut : Nat) :
    cut ∈ trackAPhysicalCriticalCuts ell k E b j ↔
      ∃ g : Nat, g < k ∧ cut = hPosition k b g ∧
        trackANumericRawAt E ell k M (cut+1) j ≠
          trackANumericRawAt E ell k M cut j := by
  classical
  constructor
  · intro hc
    have hImage :
        cut ∈ ((trackACriticalGenerations ell E b j).filter
          (fun g => g < k)).image (fun g => hPosition k b g) := hc
    obtain ⟨g,hg,hEq⟩ := Finset.mem_image.mp hImage
    obtain ⟨hCrit,hLt⟩ := Finset.mem_filter.mp hg
    refine ⟨g,hLt,hEq.symm,?_⟩
    rw [←hEq]
    exact (trackA_henson_numeric_real_cut_change_iff_critical
      E ell hell hAvoid k b g M (by omega) j hj).mpr hCrit
  · rintro ⟨g,hLt,hEq,hChange⟩
    have hCrit : g ∈ trackACriticalGenerations ell E b j := by
      rw [hEq] at hChange
      exact (trackA_henson_numeric_real_cut_change_iff_critical
        E ell hell hAvoid k b g M (by omega) j hj).mp hChange
    change cut ∈ ((trackACriticalGenerations ell E b j).filter
      (fun g => g < k)).image (fun g => hPosition k b g)
    exact Finset.mem_image.mpr
      ⟨g, Finset.mem_filter.mpr ⟨hCrit,hLt⟩, hEq.symm⟩

#print axioms Kk.trackA_numeric_all_odd_raw_neutral
#print axioms Kk.trackA_henson_physical_critical_cut_iff_actual_raw_event

end Kk
