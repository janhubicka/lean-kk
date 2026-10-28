import Kk.GraphAgeShadow
import Mathlib.Tactic

/-!
# A genuine K4 graph-age cover invisible on the selected shadow

The special resolved-copy normalization claims that the first of two
reserved vertices of a canonical K4 clique gadget is boring because
it does not lower the graph-age function on the active selected front.
That numerical inequality alone does not control the full auxiliary
parameter-closed B3 test.

The following EXACT two-sort K4 graph-age functions have bounds
  selected x   : 2 -> 2
  auxiliary z  : 1 -> 1
  mixed {x,z}  : 3 -> 2.
Both are legal under the manuscript's integer clique-multiplicity
witness definition, and the decrease is a true cover. The selected
one-sort shadow is unchanged.

This is an independent Lean check of the finite graph-age obstruction,
not a counterexample to the specially resolved numerical H copy.
To apply it to that construction, one must still establish the
auxiliary z source's exact E cut and Algorithm 5.4 closure membership.
-/

namespace Kk

/-- Supports indexed by Fin 3 as in GraphAgeShadow:
0={x}, 1={z}, 2={x,z}. For K4, a multiplicity is in {0,1,2,3}. -/
def twoSortK4Weight (s : Fin 3) (w : Fin 2 → Fin 4) : Nat :=
  if s = 0 then (w 0).val
  else if s = 1 then (w 1).val
  else (w 0).val + (w 1).val

/-- The literal witness-based graph-age definition for forbidden K4
on two nonempty sorts, with values from 1 to 3. -/
def IsTwoSortK4Age (F : Fin 3 → Nat) : Prop :=
  (∀ s : Fin 3, 1 ≤ F s ∧ F s ≤ 3) ∧
  ∀ s : Fin 3, ∃ w : Fin 2 → Fin 4,
    twoSortK4Weight s w = F s ∧
    ∀ t : Fin 3, twoSortK4Weight t w ≤ F t

/-- Before inserting the first reserved gadget vertex, x permits
two-cliques and the mixed x,z support permits three-cliques. -/
def beforeK4 (s : Fin 3) : Nat :=
  if s = 0 then 2 else if s = 1 then 1 else 3

/-- The mixed x,z clique capacity drops by one, but neither selected
nor auxiliary singleton capacity changes. -/
def afterK4 (s : Fin 3) : Nat :=
  if s = 1 then 1 else 2

theorem beforeK4_valid : IsTwoSortK4Age beforeK4 := by
  constructor
  · intro s
    fin_cases s <;> decide
  · intro s
    fin_cases s
    · refine ⟨(fun i : Fin 2 => if i = 0 then (2 : Fin 4) else 0), by decide, ?_⟩
      intro t
      fin_cases t <;> decide
    · refine ⟨(fun i : Fin 2 => if i = 1 then (1 : Fin 4) else 0), by decide, ?_⟩
      intro t
      fin_cases t <;> decide
    · refine ⟨(fun i : Fin 2 => if i = 0 then (2 : Fin 4) else 1), by decide, ?_⟩
      intro t
      fin_cases t <;> decide

theorem afterK4_valid : IsTwoSortK4Age afterK4 := by
  constructor
  · intro s
    fin_cases s <;> decide
  · intro s
    fin_cases s
    · refine ⟨(fun i : Fin 2 => if i = 0 then (2 : Fin 4) else 0), by decide, ?_⟩
      intro t
      fin_cases t <;> decide
    · refine ⟨(fun i : Fin 2 => if i = 1 then (1 : Fin 4) else 0), by decide, ?_⟩
      intro t
      fin_cases t <;> decide
    · refine ⟨(fun i : Fin 2 => if i = 0 then (2 : Fin 4) else 0), by decide, ?_⟩
      intro t
      fin_cases t <;> decide

theorem afterK4_lt_beforeK4 :
    TwoSortAgeLe afterK4 beforeK4 ∧
    ¬ TwoSortAgeLe beforeK4 afterK4 := by
  constructor
  · intro s
    fin_cases s <;> decide
  · intro h
    have h2 := h 2
    norm_num [beforeK4, afterK4] at h2

/-- No intermediate age function exists between the two legal
bounds: this is a TRUE cover, not merely a strict decrease. -/
theorem afterK4_covers_beforeK4
    (G : Fin 3 → Nat)
    (_hValid : IsTwoSortK4Age G)
    (hLow : TwoSortAgeLe afterK4 G)
    (hHigh : TwoSortAgeLe G beforeK4) :
    G = afterK4 ∨ G = beforeK4 := by
  have hx : G 0 = 2 := by
    have h1 := hLow 0
    have h2 := hHigh 0
    simp [afterK4, beforeK4] at h1 h2
    omega
  have hz : G 1 = 1 := by
    have h1 := hLow 1
    have h2 := hHigh 1
    simp [afterK4, beforeK4] at h1 h2
    omega
  have hm : G 2 = 2 ∨ G 2 = 3 := by
    have h1 := hLow 2
    have h2 := hHigh 2
    simp [afterK4, beforeK4] at h1 h2
    omega
  rcases hm with h | h
  · left
    funext s
    fin_cases s <;> simp [afterK4, hx, hz, h]
  · right
    funext s
    fin_cases s <;> simp [beforeK4, hx, hz, h]

/-- Exact K4 analogue of the earlier K3 auxiliary shadow example:
the full age changes by one cover while the selected age does not. -/
theorem selected_K4_shadow_does_not_detect_cover :
    IsTwoSortK4Age beforeK4 ∧
    IsTwoSortK4Age afterK4 ∧
    beforeK4 0 = afterK4 0 ∧
    beforeK4 2 ≠ afterK4 2 :=
  ⟨beforeK4_valid, afterK4_valid, by decide, by decide⟩

end Kk
