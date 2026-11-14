import Kk.TrackFRawCoverColumn
import Kk.TrackFCodingColumn
import Kk.TrackFCoverOneStep
import Mathlib.Tactic

/-!
# Track F: raw age of literal chronological concrete-word columns

A finite concrete level of d active equal-length words is represented
by its *ordered list of columns*, each a function Fin d → Nat.
The raw capacity on a nonempty support U is the minimum of the
initial ell-1 and all per-column caps ell-1-commonSymbol(column,U).
This is the literal c_n common-letter definition of manuscript
Def:Concrete (written with finite chronological columns).

For an actual newly appended column that writes n>0 on T and 0
outside T, we prove the raw capacity has *exactly* the previously
Lean-verified all-subsets cap effect. Thus actual age-change and
controlled-coding columns realize their canonical-age claims even
for noncanonical raw bounds. These local theorems do NOT establish
the deletion/restriction bridge, concrete E/passing-bit equivalence,
non-free splitting, the entire diary inverse, or a global BRD bound.
-/

namespace Kk

/-- A selected representative of the nonempty active support U. -/
def trackFColumnRepresentative {d ell : Nat}
    (U : IntegerGraphSupport d ell) : Fin d :=
  U.1.min' U.2.1

theorem trackFColumnRepresentative_mem {d ell : Nat}
    (U : IntegerGraphSupport d ell) :
    trackFColumnRepresentative U ∈ U.1 :=
  Finset.min'_mem U.1 U.2.1

/-- The unique common letter written on all branches of U at this
single coordinate, or 0 if there is no common positive letter.
Because U is nonempty, the value is representative-independent. -/
noncomputable def trackFColumnCommon {d ell : Nat}
    (column : Fin d → Nat) (U : IntegerGraphSupport d ell) : Nat :=
  if ∀ i ∈ U.1, column i = column (trackFColumnRepresentative U)
  then column (trackFColumnRepresentative U)
  else 0

/-- The literal new concrete diary column: put letter n on T,
and 0 on all other active branches. -/
def trackFNewColumn {d : Nat}
    (T : Finset (Fin d)) (n : Nat) : Fin d → Nat :=
  fun i => if i ∈ T then n else 0

/-- A common positive letter occurs in the new column exactly on
the nonempty admissible supports contained in T. In a mixed
0/n column no positive common letter is introduced. -/
theorem trackFNewColumnCommon {d ell : Nat}
    (T : Finset (Fin d)) (n : Nat) (hn : 0 < n)
    (U : IntegerGraphSupport d ell) :
    trackFColumnCommon (trackFNewColumn T n) U =
      if U.1 ⊆ T then n else 0 := by
  classical
  let x : Fin d := trackFColumnRepresentative U
  have hxU : x ∈ U.1 := trackFColumnRepresentative_mem U
  change
    (if ∀ i ∈ U.1,
        trackFNewColumn T n i = trackFNewColumn T n x
     then trackFNewColumn T n x else 0) =
      if U.1 ⊆ T then n else 0
  by_cases hSub : U.1 ⊆ T
  · have hxT : x ∈ T := hSub hxU
    have hUniform : ∀ i ∈ U.1,
        trackFNewColumn T n i = trackFNewColumn T n x := by
      intro i hi
      simp [trackFNewColumn, hSub hi, hxT]
    rw [if_pos hUniform, if_pos hSub]
    simp [trackFNewColumn, hxT]
  · obtain ⟨i, hiU, hiNotT⟩ := Finset.not_subset.mp hSub
    by_cases hxT : x ∈ T
    · have hNonuniform : ¬ (∀ j ∈ U.1,
          trackFNewColumn T n j = trackFNewColumn T n x) := by
        intro hUniform
        have hEq := hUniform i hiU
        simp [trackFNewColumn, hiNotT, hxT] at hEq
        omega
      simp [hSub, hNonuniform]
    · by_cases hUniform : ∀ j ∈ U.1,
          trackFNewColumn T n j = trackFNewColumn T n x
      · simp [hSub, hUniform, trackFNewColumn, hxT]
      · simp [hSub, hUniform]

/-- The literal raw φ of a finite chronological list of word
columns: every common positive letter imposes one capacity cap.
For alphabet {0,...,ell-2}, this equals the manuscript's
ell-1 - max positive common symbol, using max ∅ = 0. -/
noncomputable def trackFWordRaw (d ell : Nat)
    (columns : List (Fin d → Nat)) :
    IntegerGraphSupport d ell → Nat :=
  fun U => columns.foldl
    (fun bound column =>
      min bound (ell - 1 - trackFColumnCommon column U))
    (ell - 1)

private theorem trackFWordRaw_fold_le {d ell : Nat}
    (U : IntegerGraphSupport d ell)
    (cols : List (Fin d → Nat)) (start : Nat) :
    cols.foldl
      (fun b col => min b (ell - 1 - trackFColumnCommon col U))
      start ≤ start := by
  induction cols generalizing start with
  | nil => simp
  | cons c cs ih =>
      simp only [List.foldl_cons]
      exact (ih _).trans (Nat.min_le_left _ _)

/-- Every raw word bound is at most the initial capacity ell-1. -/
theorem trackFWordRaw_le_cap {d ell : Nat}
    (cols : List (Fin d → Nat))
    (U : IntegerGraphSupport d ell) :
    trackFWordRaw d ell cols U ≤ ell - 1 :=
  trackFWordRaw_fold_le U cols (ell - 1)

/-- The raw capacity of an actual appended word column is the
old raw capacity capped by that column's literal common symbol. -/
theorem trackFWordRaw_append {d ell : Nat}
    (cols : List (Fin d → Nat)) (column : Fin d → Nat)
    (U : IntegerGraphSupport d ell) :
    trackFWordRaw d ell (cols ++ [column]) U =
      min (trackFWordRaw d ell cols U)
        (ell - 1 - trackFColumnCommon column U) := by
  simp [trackFWordRaw, List.foldl_append]

/-- MAIN LITERAL COLUMN FORMULA: the new raw bound after appending
letter n>0 on exactly T is the genuine all-U⊆T raw cap, not an
assumed abstract-age action. T itself may have size > ell-1. -/
theorem trackFWordRaw_append_as_coding_cap {d ell : Nat}
    (cols : List (Fin d → Nat))
    (T : Finset (Fin d)) (n : Nat) (hn : 0 < n) :
    trackFWordRaw d ell (cols ++ [trackFNewColumn T n]) =
      trackFCodingRaw d ell (trackFWordRaw d ell cols)
        T (ell - 1 - n) := by
  funext U
  rw [trackFWordRaw_append,
    trackFNewColumnCommon T n hn U]
  unfold trackFCodingRaw
  by_cases hUT : U.1 ⊆ T
  · simp [hUT]
  · simp [hUT, Nat.min_eq_left (trackFWordRaw_le_cap cols U)]

/-- The unique essential changed support of a genuine cover
has a legal nonzero concrete age letter n = ell-1-lower(T). -/
theorem trackFWord_cover_symbol_valid
    (d ell : Nat)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (T : IntegerGraphSupport d ell)
    (hChanged : lower T < upper T) :
    1 ≤ ell - 1 - lower T ∧
      ell - 1 - lower T ≤ ell - 2 := by
  have hStep :=
    trackFCover_drop_one_at_changed d ell
      lower upper hCover T hChanged
  have hLower := (hCover.lower_age.1 T).1
  have hUpper := (hCover.upper_age.1 T).2
  omega

/-- A literal age-change column on the actual chronological words
realizes the LOWER age of the genuine graph-age cover. No
assumption that the old raw word bound is canonical. -/
theorem trackFWordRaw_age_cover_exact
    (d ell : Nat)
    (cols : List (Fin d → Nat))
    (lower upper : IntegerGraphSupport d ell → Nat)
    (T : IntegerGraphSupport d ell)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (hChanged : lower T < upper T)
    (hOld :
      integerGraphAgeCanonical d ell
        (trackFWordRaw d ell cols) = upper) :
    integerGraphAgeCanonical d ell
      (trackFWordRaw d ell
        (cols ++ [trackFNewColumn T.1 (ell - 1 - lower T)])) =
      lower := by
  have hn := (trackFWord_cover_symbol_valid d ell lower upper
    hCover T hChanged).1
  rw [trackFWordRaw_append_as_coding_cap cols T.1
    (ell - 1 - lower T) hn]
  have hCap : ell - 1 - (ell - 1 - lower T) = lower T := by
    have hB := (hCover.lower_age.1 T).2
    omega
  rw [hCap]
  exact trackFRawCoverColumn_exact d ell
    (trackFWordRaw d ell cols) lower upper T
    hOld hCover hChanged

/-- If every surviving passing-one support is already safe,
then the ACTUAL literal one/zero coding column cannot change
the canonical graph age. Deletion of j and the concrete E-bit
dictionary remain independent prerequisites. -/
theorem trackFWordRaw_coding_preserves_age
    (d ell : Nat)
    (cols : List (Fin d → Nat))
    (X : Finset (Fin d))
    (F : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell F)
    (hOld :
      integerGraphAgeCanonical d ell
        (trackFWordRaw d ell cols) = F)
    (hSafe : ∀ U : IntegerGraphSupport d ell,
      U.1 ⊆ X → F U ≤ ell - 2) :
    integerGraphAgeCanonical d ell
      (trackFWordRaw d ell
        (cols ++ [trackFNewColumn X 1])) = F := by
  rw [trackFWordRaw_append_as_coding_cap cols X 1 (by omega)]
  have hCap : ell - 1 - 1 = ell - 2 := by omega
  rw [hCap]
  exact trackFCodingColumn_canonical_eq d ell
    (trackFWordRaw d ell cols) F X (ell - 2)
    hAge hOld hSafe

end Kk
