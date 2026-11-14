import Kk.TrackFLiteralWordColumns
import Mathlib.Tactic

/-!
# Track F: genuine positive initial-segment spectra of chronological words

The word edge predicate E cannot be identified with abstract passing
bits for arbitrary raw histories: a word (2) that never saw (1) is a
counterexample in K4. A valid diary therefore needs the event-level
positive-spectrum initial-segment invariant.

Here we formalize the literal predicate and its *exact* behavior under
an appended chronological column, with no graph-age assumptions
hidden in the definition. The subsequent age-cover synchronization
uses the already verified cover classification.
-/

namespace Kk

/-- The positive or zero letter n actually occurs at chronological
coordinate of the currently active branch i. -/
def trackFSeenSymbol {d : Nat}
    (cols : List (Fin d → Nat)) (i : Fin d) (n : Nat) : Prop :=
  ∃ col ∈ cols, col i = n

/-- The positive letters occurring on a branch are exactly the
initial segment {1,...,a}. The symbol 0 is deliberately excluded
from this condition, since zero can appear any number of times. -/
def trackFBranchInitial {d : Nat}
    (cols : List (Fin d → Nat)) (i : Fin d) (a : Nat) : Prop :=
  ∀ n : Nat, 0 < n → (trackFSeenSymbol cols i n ↔ n ≤ a)

/-- The positive symbol occurrences after appending one real word
column are the union of earlier occurrences and the new letter. -/
theorem trackFSeenSymbol_append {d : Nat}
    (cols : List (Fin d → Nat))
    (column : Fin d → Nat)
    (i : Fin d) (n : Nat) :
    trackFSeenSymbol (cols ++ [column]) i n ↔
      trackFSeenSymbol cols i n ∨ column i = n := by
  constructor
  · rintro ⟨x,hmem,hval⟩
    rcases List.mem_append.mp hmem with hOld | hNew
    · exact Or.inl ⟨x,hOld,hval⟩
    · have hXC : x = column := by simpa using hNew
      subst x
      exact Or.inr hval
  · intro h
    rcases h with ⟨x,hmem,hval⟩ | hval
    · exact ⟨x,List.mem_append.mpr (Or.inl hmem),hval⟩
    · exact ⟨column,List.mem_append.mpr (Or.inr (by simp)),hval⟩

/-- Exact append-column spectrum invariant: a new letter q no larger
than the NEXT missing symbol a+1 preserves a positive initial
segment, of new height max(a,q). This includes appending 0,
a repeated positive symbol, or the next new positive symbol. -/
theorem trackFBranchInitial_append {d : Nat}
    (cols : List (Fin d → Nat))
    (column : Fin d → Nat)
    (i : Fin d) (a : Nat)
    (hInit : trackFBranchInitial cols i a)
    (hNext : column i ≤ a + 1) :
    trackFBranchInitial (cols ++ [column]) i
      (max a (column i)) := by
  intro n hn
  rw [trackFSeenSymbol_append]
  rw [hInit n hn]
  omega

/-- In a simultaneous column extension on all branches, requiring
the new letter on EACH branch to be at most the next unseen positive
symbol preserves the complete family of initial segment spectra. -/
theorem trackFAllBranchInitial_append {d : Nat}
    (cols : List (Fin d → Nat))
    (column : Fin d → Nat)
    (heights : Fin d → Nat)
    (hInit : ∀ i, trackFBranchInitial cols i (heights i))
    (hNext : ∀ i, column i ≤ heights i + 1) :
    ∀ i, trackFBranchInitial (cols ++ [column]) i
      (max (heights i) (column i)) := by
  intro i
  exact trackFBranchInitial_append cols column i
    (heights i) (hInit i) (hNext i)

end Kk
