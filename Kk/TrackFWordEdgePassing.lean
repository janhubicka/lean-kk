import Kk.TrackFWordEdgeLiteral
import Kk.TrackFPairCapacityTrue
import Mathlib.Tactic

/-!
# Track F: actual literal word E iff abstract controlled-coding passing bit

For a two-sort concrete level (word x=0 and candidate coded j=1),
with true canonical integer graph age F, F({j})=1, and the exact
positive-spectrum synchronization of the actual chronological
words with their singleton ages, the FULL literal word predicate E
is equivalent to F({x,j}) = F({x})+1.

Unlike a conditional replacement interface, all pieces are the
actual finite normalized integer-witness age and genuine raw
common-symbol word columns. The initial-segment synchronization is
a stated necessary hypothesis and its age-cover induction is already
Lean-verified in TrackFBranchSpectrumCover.

Full controlled coding requires additional age-cap and minimal-pre-age
conditions. Splitting, full decorated diaries and independent infinite
BRD unavoidability are not proved here.
-/

namespace Kk

/-- For actual two-sort equal-length word columns with a GENUINE
canonical K_ell age F, exact positive-initial-segment spectra
synchronized with the canonical singleton ages, and a proposed coded
branch j=1 of age one, the manuscript's literal concrete E predicate
is equivalent to the true abstract controlled-coding passing bit.

Both the numerical pair formula and the *literal* E definition are
proved independently, with all hypotheses explicit. -/
theorem trackFConcreteEdgePair_iff_abstractPassing
    (ell : Nat) (hell : 3 ≤ ell)
    (cols : List (Fin 2 → Nat))
    (hAge : IsIntegerGraphAge 2 ell
      (integerGraphAgeCanonical 2 ell (trackFWordRaw 2 ell cols)))
    (hSpectrum : trackFWordSpectrumMatches 2 ell (by omega)
      cols (integerGraphAgeCanonical 2 ell (trackFWordRaw 2 ell cols)))
    (hCoding : integerGraphAgeCanonical 2 ell
      (trackFWordRaw 2 ell cols) (trackFPairSecond ell hell) = 1) :
    trackFConcreteEdgePair ell cols ↔
      integerGraphAgeCanonical 2 ell
        (trackFWordRaw 2 ell cols) (trackFPairBoth ell hell) =
      integerGraphAgeCanonical 2 ell
        (trackFWordRaw 2 ell cols) (trackFPairFirst ell hell) + 1 := by
  classical
  let B := trackFWordRaw 2 ell cols
  let F := integerGraphAgeCanonical 2 ell B
  let s0 := trackFPairFirst ell hell
  let s1 := trackFPairSecond ell hell
  let sp := trackFPairBoth ell hell
  let a := ell - 1 - F s0
  let c := trackFWordMax 2 ell cols sp
  let h2 : 2 ≤ ell := by omega
  have hS0 : trackFSpectrumSingleton 2 ell h2 (0 : Fin 2) = s0 := by
    apply Subtype.ext
    rfl
  have hS1 : trackFSpectrumSingleton 2 ell h2 (1 : Fin 2) = s1 := by
    apply Subtype.ext
    rfl
  have hInitX : trackFBranchInitial cols (0 : Fin 2) a := by
    simpa only [hS0] using hSpectrum (0 : Fin 2)
  have hInitJRaw : trackFBranchInitial cols (1 : Fin 2)
      (ell - 1 - F s1) := by
    simpa only [hS1] using hSpectrum (1 : Fin 2)
  have hJHeight : ell - 1 - F s1 = ell - 2 := by
    change F s1 = 1 at hCoding
    rw [hCoding]
    omega
  have hInitJ : trackFBranchInitial cols (1 : Fin 2)
      (ell - 2) := by
    simpa only [hJHeight] using hInitJRaw
  have hF0Pos : 1 ≤ F s0 := (hAge.1 s0).1
  have hF0Cap : F s0 ≤ ell - 1 := (hAge.1 s0).2
  have haBound : a ≤ ell - 2 := by
    dsimp [a]
    omega
  have hcBound : c ≤ a :=
    trackFWordMax_pair_le_height ell a hell cols hInitX
  have hEdge : trackFConcreteEdgePair ell cols ↔ c < a :=
    trackFConcreteEdgePair_iff_commonMax_lt
      ell a hell haBound cols hInitX hInitJ
  have hPair : F sp =
      min (ell - 1 - c) (F s0 + F s1) := by
    exact trackFPair_word_capacity ell hell cols
  have hJ : F s1 = 1 := hCoding
  have hPair1 : F sp = min (ell - 1 - c) (F s0 + 1) := by
    calc
      F sp = min (ell - 1 - c) (F s0 + F s1) := hPair
      _ = min (ell - 1 - c) (F s0 + 1) := by rw [hJ]
  have hXSum : F s0 + 1 = ell - a := by
    dsimp [a]
    omega
  have hArith :
      (min (ell - 1 - c) (F s0 + 1) = F s0 + 1) ↔
        c < a := by
    rw [hXSum]
    exact trackFPair_passing_arithmetic ell a c hell haBound hcBound
  change trackFConcreteEdgePair ell cols ↔ F sp = F s0 + 1
  rw [hPair1]
  exact hEdge.trans hArith.symm

end Kk
