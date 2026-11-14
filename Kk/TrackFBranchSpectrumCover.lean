import Kk.TrackFBranchSpectrum
import Kk.TrackFCoverSupportValues
import Mathlib.Tactic

/-!
# Track F: full positive-spectrum synchronization at a genuine age cover

The old active words have, on each branch i, exactly the positive
symbols {1,...,ell-1-F({i})}. For a true consecutive age-change
F' ⋖ F, append the concrete nonzero symbol n=ell-1-F'(T)
precisely on the unique minimal changed support T.

We prove that the NEW words have exactly the positive symbols
{1,...,ell-1-F'({i})}, using:
  * singleton changed capacities drop by exactly one;
  * every changed support contains the unique minimal changed T;
  * a proper singleton subset of multi-support T does NOT change;
  * genuine lower graph-age monotonicity.

This proves the general age-change positive-spectrum invariant, not
the complete diary inverse, controlled E/passing equality or the
non-free splitting-age theorem.
-/

namespace Kk

/-- A concrete singleton nonempty support at an active branch i. -/
def trackFSpectrumSingleton (d ell : Nat) (hell : 2 ≤ ell)
    (i : Fin d) : IntegerGraphSupport d ell := by
  refine ⟨{i}, ?_⟩
  constructor
  · simp
  · simp
    omega

/-- The current chronological history's exact positive-spectrum
heights are synchronized with the actual canonical graph age at
every singleton support. -/
def trackFWordSpectrumMatches
    (d ell : Nat) (hell : 2 ≤ ell)
    (cols : List (Fin d → Nat))
    (F : IntegerGraphSupport d ell → Nat) : Prop :=
  ∀ i : Fin d,
    trackFBranchInitial cols i
      (ell - 1 - F (trackFSpectrumSingleton d ell hell i))

/-- A TRUE K_ell age-cover column cannot introduce a skipped
positive symbol on any active branch. Moreover, its exact new
spectrum height agrees with the LOWER age singleton capacity.

This applies to ANY genuine finite cover and its minimal changed
support, not only to small K4 diagrams. -/
theorem trackFWordSpectrum_age_cover
    (d ell : Nat) (hell : 3 ≤ ell)
    (cols : List (Fin d → Nat))
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (T : IntegerGraphSupport d ell)
    (hTChanged : lower T < upper T)
    (hTMinimal : ∀ U : IntegerGraphSupport d ell,
      U.1 ⊆ T.1 → U.1 ≠ T.1 → lower U = upper U)
    (hOld : trackFWordSpectrumMatches d ell (by omega)
      cols upper) :
    trackFWordSpectrumMatches d ell (by omega)
      (cols ++ [trackFNewColumn T.1 (ell - 1 - lower T)])
      lower := by
  classical
  let h2 : 2 ≤ ell := by omega
  intro i
  let S := trackFSpectrumSingleton d ell h2 i
  let a := ell - 1 - upper S
  let a' := ell - 1 - lower S
  let q := trackFNewColumn T.1 (ell - 1 - lower T) i
  have hOldI : trackFBranchInitial cols i a := hOld i
  have hHeight : max a q = a' := by
    by_cases hiT : i ∈ T.1
    · have hSSub : S.1 ⊆ T.1 := by
        intro k hk
        have hKi : k = i := by
          simpa [S,trackFSpectrumSingleton] using hk
        simpa [hKi] using hiT
      by_cases hTIsSingleton : T.1 = S.1
      · have hTS : T = S := Subtype.ext hTIsSingleton
        have hDrop : upper S = lower S + 1 := by
          have h := trackFCover_drop_one_at_changed d ell
            lower upper hCover T hTChanged
          simpa only [hTS] using h
        have hLo : 1 ≤ lower S := (hCover.lower_age.1 S).1
        have hLoCap : lower S ≤ ell - 1 := (hCover.lower_age.1 S).2
        have hUpCap : upper S ≤ ell - 1 := (hCover.upper_age.1 S).2
        have hQ : q = ell - 1 - lower S := by
          simp [q,trackFNewColumn,hiT,hTS]
        rw [hQ]
        dsimp [a,a']
        omega
      · have hSNe : S.1 ≠ T.1 := by
          intro hEq
          exact hTIsSingleton hEq.symm
        have hSame : lower S = upper S :=
          hTMinimal S hSSub hSNe
        have hMon : lower S ≤ lower T :=
          integerGraphAge_monotone d ell
            lower hCover.lower_age S T hSSub
        have hSLoCap : lower S ≤ ell - 1 :=
          (hCover.lower_age.1 S).2
        have hTLoCap : lower T ≤ ell - 1 :=
          (hCover.lower_age.1 T).2
        have hQ : q = ell - 1 - lower T := by
          simp [q,trackFNewColumn,hiT]
        rw [hQ]
        dsimp [a,a']
        omega
    · have hSame : lower S = upper S := by
        by_contra hNe
        have hSChanged : lower S < upper S := by
          have hLe := hCover.le S
          omega
        have hTU : T.1 ⊆ S.1 :=
          trackFCover_essential_contained_in_changed d ell
            (by omega) lower upper hCover T
            hTChanged hTMinimal S hSChanged
        obtain ⟨k,hk⟩ := T.2.1
        have hkS : k ∈ S.1 := hTU hk
        have hKi : k = i := by
          simpa [S,trackFSpectrumSingleton] using hkS
        apply hiT
        simpa [hKi] using hk
      have hQ : q = 0 := by
        simp [q,trackFNewColumn,hiT]
      rw [hQ]
      simp [a,a',hSame]
  have hDropSingleton : upper S ≤ lower S + 1 :=
    trackFCover_drop_at_most_one d ell lower upper hCover S
  have hLoCap : lower S ≤ ell - 1 :=
    (hCover.lower_age.1 S).2
  have hUpCap : upper S ≤ ell - 1 :=
    (hCover.upper_age.1 S).2
  have hNewLe : a' ≤ a + 1 := by
    dsimp [a,a']
    omega
  have hStepBound : q ≤ a + 1 :=
    (Nat.le_max_right a q).trans (hHeight.le.trans hNewLe)
  have hNew := trackFBranchInitial_append
    cols (trackFNewColumn T.1 (ell - 1 - lower T))
    i a hOldI hStepBound
  change trackFBranchInitial
    (cols ++ [trackFNewColumn T.1 (ell - 1 - lower T)])
    i a'
  rw [←hHeight]
  exact hNew

/-- A controlled-coding column appends 0 or 1 to each SURVIVING
branch; regardless of age labels this cannot skip a positive symbol.
Full age synchronization is guaranteed separately by the verified
safe-coding-after-deletion theorem, once its X set is determined. -/
theorem trackFWordSpectrum_coding_column
    (d : Nat)
    (cols : List (Fin d → Nat))
    (X : Finset (Fin d))
    (heights : Fin d → Nat)
    (hInit : ∀ i, trackFBranchInitial cols i (heights i)) :
    ∀ i, trackFBranchInitial
      (cols ++ [trackFNewColumn X 1]) i
      (max (heights i) (trackFNewColumn X 1 i)) := by
  apply trackFAllBranchInitial_append
    cols (trackFNewColumn X 1) heights hInit
  intro i
  simp [trackFNewColumn]
  omega

end Kk
