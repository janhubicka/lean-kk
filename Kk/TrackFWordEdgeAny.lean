import Kk.TrackFWordEdgePassing
import Kk.TrackFSurvivorCanonical
import Mathlib.Tactic

/-!
# Track F: literal concrete E/passing-bit equivalence at arbitrary active levels

Any two distinct equally long active word branches x and j can be
selected by a genuine Fin 2 ↪ Fin d embedding (without identifying
coordinates). Exact raw/canonical age restriction and genuine age
preservation were previously Lean-verified in TrackFSurvivorCanonical.

The two-sort E iff passing theorem, proved independently of the
abstract bit definition from all literal E clauses, therefore lifts
to arbitrary d and ell whenever the actual words have the verified
initial-segment/singleton-age synchronization property.

This is a local coding passing-bit dictionary, NOT full controlled
coding (which also needs age caps and minimal pre-age), non-free
splitting, a complete age-decorated diary inverse, or independently
proved infinite unavoidability.
-/

namespace Kk

/-- Two equal-length active words differ at some chronological
coordinate. This is the manuscript's u ≠ w condition. -/
def trackFWordDifferent {d : Nat}
    (cols : List (Fin d → Nat))
    (x j : Fin d) : Prop :=
  ∃ col ∈ cols, col x ≠ col j

/-- The literal equal-length concrete graph-edge predicate at ANY
two active coordinates x,j of a d-sort word level.
Every clause of the manuscript's E is present, without mentioning
any abstract graph-age function. -/
def trackFConcreteEdgeAt {d : Nat}
    (ell : Nat) (cols : List (Fin d → Nat))
    (x j : Fin d) : Prop :=
  trackFWordDifferent cols x j ∧
    trackFSeenSymbol cols x 1 ∧
    trackFSeenSymbol cols j 1 ∧
    (trackFSeenSymbol cols x (ell - 2) ∨
     trackFSeenSymbol cols j (ell - 2)) ∧
    (∃ n : Nat, 0 < n ∧
      trackFSeenSymbol cols x n ∧
      trackFSeenSymbol cols j n ∧
      (∀ m : Nat, n < m →
        ¬ (trackFSeenSymbol cols x m ∧
           trackFSeenSymbol cols j m)) ∧
      ¬ (∃ col ∈ cols, col x = n ∧ col j = n))

/-- The equal-length word-seen predicate is invariant under an
injective selection of survivor branch coordinates. -/
theorem trackFSeenSymbol_reindex {e d : Nat}
    (f : Fin e ↪ Fin d)
    (cols : List (Fin d → Nat)) (i : Fin e) (n : Nat) :
    trackFSeenSymbol (trackFRestrictColumns f cols) i n ↔
      trackFSeenSymbol cols (f i) n := by
  constructor
  · rintro ⟨col,hmem,hval⟩
    rcases List.mem_map.mp hmem with ⟨orig,horig,heq⟩
    subst col
    exact ⟨orig,horig,hval⟩
  · rintro ⟨orig,horig,hval⟩
    exact ⟨fun i => orig (f i),
      List.mem_map.mpr ⟨orig,horig,rfl⟩,hval⟩

/-- Word distinctness is invariant under coordinate selection. -/
theorem trackFWordDifferent_reindex {e d : Nat}
    (f : Fin e ↪ Fin d)
    (cols : List (Fin d → Nat)) (i j : Fin e) :
    trackFWordDifferent (trackFRestrictColumns f cols) i j ↔
      trackFWordDifferent cols (f i) (f j) := by
  constructor
  · rintro ⟨col,hmem,hneq⟩
    rcases List.mem_map.mp hmem with ⟨orig,horig,heq⟩
    subst col
    exact ⟨orig,horig,hneq⟩
  · rintro ⟨orig,horig,hneq⟩
    exact ⟨fun i => orig (f i),
      List.mem_map.mpr ⟨orig,horig,rfl⟩,hneq⟩

/-- Simultaneously shared positive-letter occurrences are invariant
under any injective selection of survivor coordinates. -/
theorem trackFPairSimultaneous_reindex {d : Nat}
    (f : Fin 2 ↪ Fin d)
    (cols : List (Fin d → Nat)) (n : Nat) :
    trackFPairSimultaneous (trackFRestrictColumns f cols) n ↔
      (∃ col ∈ cols, col (f 0) = n ∧ col (f 1) = n) := by
  constructor
  · rintro ⟨col,hmem,h0,h1⟩
    rcases List.mem_map.mp hmem with ⟨orig,horig,heq⟩
    subst col
    exact ⟨orig,horig,h0,h1⟩
  · rintro ⟨orig,horig,h0,h1⟩
    exact ⟨fun i => orig (f i),
      List.mem_map.mpr ⟨orig,horig,rfl⟩,h0,h1⟩

/-- Selecting two active coordinates preserves the FULL literal E
predicate, not merely its single-symbol maximum approximation. -/
theorem trackFConcreteEdgePair_reindex {d : Nat}
    (ell : Nat) (f : Fin 2 ↪ Fin d)
    (cols : List (Fin d → Nat)) :
    trackFConcreteEdgePair ell (trackFRestrictColumns f cols) ↔
      trackFConcreteEdgeAt ell cols (f 0) (f 1) := by
  simp only [trackFConcreteEdgePair, trackFConcreteEdgeAt,
    trackFWordDifferent, trackFSeenSymbol_reindex,
    trackFPairSimultaneous_reindex]
  apply and_congr
  · exact trackFWordDifferent_reindex f cols (0 : Fin 2) (1 : Fin 2)
  · exact Iff.rfl

/-- Select x first and the candidate coded branch j second,
using an *injective* two-sort embedding. The pair must be distinct. -/
def trackFSelectPair {d : Nat}
    (x j : Fin d) (hne : x ≠ j) : Fin 2 ↪ Fin d where
  toFun := fun i => if i = 0 then x else j
  inj' := by
    intro i k hEq
    fin_cases i <;> fin_cases k <;>
      simp_all [hne,hne.symm]

@[simp] theorem trackFSelectPair_zero {d : Nat}
    (x j : Fin d) (hne : x ≠ j) :
    trackFSelectPair x j hne (0 : Fin 2) = x := by
  change (if (0 : Fin 2) = 0 then x else j) = x
  simp

@[simp] theorem trackFSelectPair_one {d : Nat}
    (x j : Fin d) (hne : x ≠ j) :
    trackFSelectPair x j hne (1 : Fin 2) = j := by
  change (if (1 : Fin 2) = 0 then x else j) = j
  simp

/-- Exact singleton supports commute with injecting selected
surviving branch coordinates into the original finite sort level. -/
theorem trackFMapSpectrumSingleton {e d ell : Nat}
    (f : Fin e ↪ Fin d) (hell : 2 ≤ ell) (i : Fin e) :
    trackFMapSupport f (trackFSpectrumSingleton e ell hell i) =
      trackFSpectrumSingleton d ell hell (f i) := by
  apply Subtype.ext
  simp [trackFMapSupport,trackFSpectrumSingleton]

/-- The synchronized initial-segment invariant of *all* active
word branches is inherited by an arbitrary injectively selected
survivor level, with its exact pulled-back singleton graph ages. -/
theorem trackFWordSpectrumMatches_reindex {e d ell : Nat}
    (f : Fin e ↪ Fin d) (hell : 2 ≤ ell)
    (cols : List (Fin d → Nat))
    (F : IntegerGraphSupport d ell → Nat)
    (hSync : trackFWordSpectrumMatches d ell hell cols F) :
    trackFWordSpectrumMatches e ell hell
      (trackFRestrictColumns f cols) (trackFPullbackRaw f F) := by
  intro i n hn
  have hEq : trackFMapSupport f (trackFSpectrumSingleton e ell hell i) =
      trackFSpectrumSingleton d ell hell (f i) :=
    trackFMapSpectrumSingleton f hell i
  change trackFSeenSymbol (trackFRestrictColumns f cols) i n ↔
    n ≤ ell - 1 -
      trackFPullbackRaw f F (trackFSpectrumSingleton e ell hell i)
  rw [trackFSeenSymbol_reindex]
  simpa only [trackFPullbackRaw,hEq] using hSync (f i) n hn

/-- For arbitrary distinct active branches x,j and a GENUINE
finite canonical K_ell age of their actual chronological word
history, synchronized positive-initial-segment spectra and
F({j})=1 imply that the manuscript's LITERAL E(x,j) agrees
exactly with its ABSTRACT controlled-coding passing-one bit.

The selected support on the RHS is the actual image of the
two-sort pair/singleton under the genuine embedding x→0,j→1.
It is definitionally the labelled support {x,j}/{x}.
No other controlled coding or diary theorem is assumed. -/
theorem trackFConcreteEdgeAt_iff_abstractPassing
    (d ell : Nat) (hell : 3 ≤ ell)
    (cols : List (Fin d → Nat))
    (F : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell F)
    (hOld : integerGraphAgeCanonical d ell
      (trackFWordRaw d ell cols) = F)
    (hSync : trackFWordSpectrumMatches d ell (by omega) cols F)
    (x j : Fin d) (hNe : x ≠ j)
    (hCoding : F (trackFSpectrumSingleton d ell (by omega) j) = 1) :
    trackFConcreteEdgeAt ell cols x j ↔
      F (trackFMapSupport (trackFSelectPair x j hNe)
          (trackFPairBoth ell hell)) =
      F (trackFMapSupport (trackFSelectPair x j hNe)
          (trackFPairFirst ell hell)) + 1 := by
  classical
  let f : Fin 2 ↪ Fin d := trackFSelectPair x j hNe
  let cols2 : List (Fin 2 → Nat) := trackFRestrictColumns f cols
  let F2 := integerGraphAgeCanonical 2 ell (trackFWordRaw 2 ell cols2)
  let h2 : 2 ≤ ell := by omega
  have hF2 : F2 = trackFPullbackRaw f F := by
    funext U
    calc
      F2 U =
        integerGraphAgeCanonical d ell
          (trackFWordRaw d ell cols) (trackFMapSupport f U) :=
        trackFWordCanonical_reindex f (by omega) cols U
      _ = F (trackFMapSupport f U) := by rw [hOld]
  have hF2Age : IsIntegerGraphAge 2 ell F2 := by
    rw [hF2]
    exact trackFGraphAge_reindex f F hAge
  have hF2Sync : trackFWordSpectrumMatches 2 ell h2 cols2 F2 := by
    rw [hF2]
    exact trackFWordSpectrumMatches_reindex f h2 cols F hSync
  have hSelect1 :
      trackFMapSupport f (trackFPairSecond ell hell) =
        trackFSpectrumSingleton d ell h2 j := by
    calc
      trackFMapSupport f (trackFPairSecond ell hell) =
          trackFMapSupport f
            (trackFSpectrumSingleton 2 ell h2 (1 : Fin 2)) := by
        apply Subtype.ext
        rfl
      _ = trackFSpectrumSingleton d ell h2 (f 1) :=
        trackFMapSpectrumSingleton f h2 (1 : Fin 2)
      _ = trackFSpectrumSingleton d ell h2 j := by
        simp [f]
  have hF2Code : F2 (trackFPairSecond ell hell) = 1 := by
    rw [hF2]
    change F (trackFMapSupport f (trackFPairSecond ell hell)) = 1
    rw [hSelect1]
    exact hCoding
  have hTwo : trackFConcreteEdgePair ell cols2 ↔
      F2 (trackFPairBoth ell hell) =
        F2 (trackFPairFirst ell hell) + 1 :=
    trackFConcreteEdgePair_iff_abstractPassing ell hell cols2
      hF2Age hF2Sync hF2Code
  have hEdge : trackFConcreteEdgeAt ell cols x j ↔
      trackFConcreteEdgePair ell cols2 := by
    have h := trackFConcreteEdgePair_reindex ell f cols
    have hZero : f 0 = x := trackFSelectPair_zero x j hNe
    have hOne : f 1 = j := trackFSelectPair_one x j hNe
    simpa only [hZero,hOne] using h.symm
  calc
    trackFConcreteEdgeAt ell cols x j ↔
        trackFConcreteEdgePair ell cols2 := hEdge
    _ ↔ F2 (trackFPairBoth ell hell) =
        F2 (trackFPairFirst ell hell) + 1 := hTwo
    _ ↔ F (trackFMapSupport f (trackFPairBoth ell hell)) =
        F (trackFMapSupport f (trackFPairFirst ell hell)) + 1 := by
      rw [hF2]
      rfl

end Kk
