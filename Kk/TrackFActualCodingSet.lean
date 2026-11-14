import Kk.TrackFWordEdgeAny
import Kk.TrackFSurvivorCanonical
import Mathlib.Tactic

/-!
# Track F: exact literal E passing-one set and coding successor AGE

The concrete passing-one set is defined by the manuscript's ACTUAL
chronological word predicate E, independently of the abstract
graph-age bit set. Under the valid-diary synchronized positive
initial spectra and a candidate coded branch of singleton age 1,
they coincide exactly for every surviving ordered active branch.

After coding j is deleted and a literal passing-one column appended
to those surviving branches, the entire canonical graph age agrees
with the restricted old age, provided all nonempty X-supported
capacities satisfy the controlled-coding safety cap. This statement
still does NOT derive the minimal-pre-age admissibility condition,
non-free splitting, full diary inverse or infinite unavoidability.
-/

namespace Kk

/-- The selected two-sort embedding for one surviving branch i and
coded branch j, with the correct *ordered deletion* of j. -/
def trackFDeletedPair (d : Nat)
    (j : Fin (d + 1)) (i : Fin d) :
    Fin 2 ↪ Fin (d + 1) :=
  trackFSelectPair ((Fin.succAboveEmb j) i) j (by
    simpa using (Fin.succAbove_ne j i))

/-- Literal concrete passing-one set, defined solely from the E
relation of the chronological word columns. -/
noncomputable def trackFConcretePassingSet (d ell : Nat)
    (j : Fin (d + 1))
    (cols : List (Fin (d + 1) → Nat)) : Finset (Fin d) := by
  classical
  exact Finset.univ.filter (fun i =>
    trackFConcreteEdgeAt ell cols ((Fin.succAboveEmb j) i) j)

/-- The INDEPENDENT abstract pair-capacity passing-one set. Unlike
the concrete set, this uses the genuine full graph-age F and does
not mention word relation E. -/
def trackFAbstractPassingSet (d ell : Nat)
    (hell : 3 ≤ ell)
    (j : Fin (d + 1))
    (F : IntegerGraphSupport (d + 1) ell → Nat) :
    Finset (Fin d) :=
  Finset.univ.filter (fun i =>
    F (trackFMapSupport (trackFDeletedPair d j i)
        (trackFPairBoth ell hell)) =
    F (trackFMapSupport (trackFDeletedPair d j i)
        (trackFPairFirst ell hell)) + 1)

/-- The literal E passing set and the abstract numerical
controlled-coding passing set are EXACTLY EQUAL, for a genuine
finite graph age and its synchronized positive-spectrum word
history, with the proposed coded branch j of singleton age 1.

The initial-spectrum and singleton-age conditions are essential:
arbitrary word histories do not satisfy this equality. -/
theorem trackFConcretePassingSet_eq_abstract
    (d ell : Nat) (hell : 3 ≤ ell)
    (j : Fin (d + 1))
    (cols : List (Fin (d + 1) → Nat))
    (F : IntegerGraphSupport (d + 1) ell → Nat)
    (hAge : IsIntegerGraphAge (d + 1) ell F)
    (hOld : integerGraphAgeCanonical (d + 1) ell
      (trackFWordRaw (d + 1) ell cols) = F)
    (hSpectrum : trackFWordSpectrumMatches (d + 1) ell
      (by omega) cols F)
    (hCoding : F (trackFSpectrumSingleton (d + 1) ell
      (by omega) j) = 1) :
    trackFConcretePassingSet d ell j cols =
      trackFAbstractPassingSet d ell hell j F := by
  classical
  ext i
  simp only [trackFConcretePassingSet,trackFAbstractPassingSet,
    Finset.mem_filter,Finset.mem_univ,true_and]
  have hNe : ((Fin.succAboveEmb j) i) ≠ j := by
    simpa using (Fin.succAbove_ne j i)
  exact trackFConcreteEdgeAt_iff_abstractPassing
    (d + 1) ell hell cols F
    hAge hOld hSpectrum ((Fin.succAboveEmb j) i) j hNe hCoding

/-- A literal E-determined passing-one column cannot change the
canonical graph age after deleting the coded branch j, provided
its actual X-supported subcapacities satisfy the full safety cap.
This uses the verified true dimension reduction, not a postulated
new age or an abstract replacement model. -/
theorem trackFWordRaw_coding_by_literal_E_exact
    (d ell : Nat) (hell : 3 ≤ ell)
    (j : Fin (d + 1))
    (cols : List (Fin (d + 1) → Nat))
    (F : IntegerGraphSupport (d + 1) ell → Nat)
    (hAge : IsIntegerGraphAge (d + 1) ell F)
    (hOld : integerGraphAgeCanonical (d + 1) ell
      (trackFWordRaw (d + 1) ell cols) = F)
    (hSafe : ∀ U : IntegerGraphSupport d ell,
      U.1 ⊆ trackFConcretePassingSet d ell j cols →
        F (trackFMapSupport (Fin.succAboveEmb j) U) ≤ ell - 2) :
    integerGraphAgeCanonical d ell
      (trackFWordRaw d ell
        (trackFRestrictColumns (Fin.succAboveEmb j) cols ++
          [trackFNewColumn
            (trackFConcretePassingSet d ell j cols) 1])) =
      trackFPullbackRaw (Fin.succAboveEmb j) F := by
  exact trackFWordRaw_coding_after_delete_exact
    d ell j (by omega) cols F hAge hOld
    (trackFConcretePassingSet d ell j cols) hSafe

/-- The exact canonical age-profile effect of a real concrete
E-based coding step, with the safety cap stated on the *independent*
abstract passing set. The proof uses the separately established
E/X equality to transfer that cap to the literal word column. -/
theorem trackFWordRaw_coding_by_abstractSet_exact
    (d ell : Nat) (hell : 3 ≤ ell)
    (j : Fin (d + 1))
    (cols : List (Fin (d + 1) → Nat))
    (F : IntegerGraphSupport (d + 1) ell → Nat)
    (hAge : IsIntegerGraphAge (d + 1) ell F)
    (hOld : integerGraphAgeCanonical (d + 1) ell
      (trackFWordRaw (d + 1) ell cols) = F)
    (hSpectrum : trackFWordSpectrumMatches (d + 1) ell
      (by omega) cols F)
    (hCoding : F (trackFSpectrumSingleton (d + 1) ell
      (by omega) j) = 1)
    (hSafe : ∀ U : IntegerGraphSupport d ell,
      U.1 ⊆ trackFAbstractPassingSet d ell hell j F →
        F (trackFMapSupport (Fin.succAboveEmb j) U) ≤ ell - 2) :
    integerGraphAgeCanonical d ell
      (trackFWordRaw d ell
        (trackFRestrictColumns (Fin.succAboveEmb j) cols ++
          [trackFNewColumn
            (trackFConcretePassingSet d ell j cols) 1])) =
      trackFPullbackRaw (Fin.succAboveEmb j) F := by
  have hSets : trackFConcretePassingSet d ell j cols =
      trackFAbstractPassingSet d ell hell j F :=
    trackFConcretePassingSet_eq_abstract
      d ell hell j cols F hAge hOld hSpectrum hCoding
  apply trackFWordRaw_coding_by_literal_E_exact
    d ell hell j cols F hAge hOld
  intro U hU
  exact hSafe U (by simpa only [hSets] using hU)

end Kk
