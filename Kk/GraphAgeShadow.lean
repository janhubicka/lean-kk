import Mathlib.Tactic

/-!
# The selected graph-age shadow does not determine the full age

A tiny adversarial counterexample to a tempting shortcut in the
K_ell-free diary upper-bound proof.

For K_3 with two sorts x and z, selected x and auxiliary z, let both
singleton bounds be 1, and lower the mixed bound from 2 to 1.
These are BOTH genuine graph-age functions under the manuscript's
integer-witness definition. The latter covers the former in the
pointwise age poset, but the selected singleton shadow is unchanged.

This module does NOT refute the specialized canonical resolved-copy
construction; it shows only that its proposed full (B3) age-test
projection cannot follow from the axioms of graph-age functions
alone. A separate auxiliary-witness projection property must be
proved for that construction.

No unproved axiom or new Ramsey assertion is used.
-/

namespace Kk

/-- The three nonempty supports of two labelled sorts, in order:
0 = {x}, 1 = {z}, 2 = {x,z}. -/
def twoSortWeight (s : Fin 3) (w : Fin 2 → Fin 3) : Nat :=
  if s = 0 then (w 0).val
  else if s = 1 then (w 1).val
  else (w 0).val + (w 1).val

/-- Exactly the finite integer-witness definition for K_3 on two
sorts. All weights belong to {0,1,2}, as in Def:Graph_Age_Function. -/
def IsTwoSortTriangleAge (F : Fin 3 → Nat) : Prop :=
  (∀ s : Fin 3, 1 ≤ F s ∧ F s ≤ 2) ∧
  ∀ s : Fin 3, ∃ w : Fin 2 → Fin 3,
    twoSortWeight s w = F s ∧
    ∀ t : Fin 3, twoSortWeight t w ≤ F t

/-- A clique with one vertex in each of x,z is permitted. -/
def fullBefore (s : Fin 3) : Nat :=
  if s = 2 then 2 else 1

/-- A mixed two-vertex clique is no longer permitted. -/
def fullAfter (_s : Fin 3) : Nat := 1

theorem fullBefore_valid : IsTwoSortTriangleAge fullBefore := by decide
theorem fullAfter_valid : IsTwoSortTriangleAge fullAfter := by decide

/-- Restriction to the selected type x is exactly unchanged. -/
theorem selected_shadow_unchanged :
    fullBefore 0 = fullAfter 0 := rfl

/-- The full age on x together with auxiliary z has changed. -/
theorem mixed_support_changes :
    fullBefore 2 = 2 ∧ fullAfter 2 = 1 := by decide

def TwoSortAgeLe (F G : Fin 3 → Nat) : Prop :=
  ∀ s, F s ≤ G s

theorem fullAfter_lt_fullBefore :
    TwoSortAgeLe fullAfter fullBefore ∧
    ¬ TwoSortAgeLe fullBefore fullAfter := by
  constructor
  · intro s
    fin_cases s <;> decide
  · intro h
    have h2 := h 2
    norm_num [TwoSortAgeLe, fullBefore, fullAfter] at h2

/-- There is no intermediate valid graph-age function between these
two ages: the invisible-to-selected-shadow change is a TRUE cover. -/
theorem fullAfter_covers_fullBefore
    (G : Fin 3 → Nat)
    (_hValid : IsTwoSortTriangleAge G)
    (hLow : TwoSortAgeLe fullAfter G)
    (hHigh : TwoSortAgeLe G fullBefore) :
    G = fullAfter ∨ G = fullBefore := by
  have hX : G 0 = 1 := by
    have h1 := hLow 0
    have h2 := hHigh 0
    simp [fullAfter, fullBefore] at h1 h2
    omega
  have hZ : G 1 = 1 := by
    have h1 := hLow 1
    have h2 := hHigh 1
    simp [fullAfter, fullBefore] at h1 h2
    omega
  have hJoint : G 2 = 1 ∨ G 2 = 2 := by
    have h1 := hLow 2
    have h2 := hHigh 2
    simp [fullAfter, fullBefore] at h1 h2
    omega
  rcases hJoint with h | h
  · left
    funext s
    fin_cases s <;> simp [fullAfter, hX, hZ, h]
  · right
    funext s
    fin_cases s <;> simp [fullBefore, hX, hZ, h]

/-- Hence the selected age shadow cannot detect every full age cover,
even in the smallest nontrivial triangle-free example. -/
theorem selected_shadow_does_not_detect_cover :
    IsTwoSortTriangleAge fullBefore ∧
    IsTwoSortTriangleAge fullAfter ∧
    fullBefore 0 = fullAfter 0 ∧
    fullBefore 2 ≠ fullAfter 2 :=
  ⟨fullBefore_valid, fullAfter_valid,
    selected_shadow_unchanged, by decide⟩

end Kk
