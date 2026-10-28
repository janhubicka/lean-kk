import Kk.K4AuxiliaryShadow
import Mathlib.Tactic

/-!
# A uniform invisible auxiliary cover for all long K_ell clique gadgets

For every ell >= 4 and 1 <= s <= ell-3, the two-sort
graph-age states (s+1,1,s+2) and (s+1,1,s+1) are both legal
under the literal integer clique-multiplicity witness definition
for K_ell-free graphs. The second covers the first, while the
selected x singleton capacity is unchanged.

The length of the manuscript's proposed canonical clique block is
r = ell - 1 - s, so r>=2 is equivalent to s<=ell-3.
Thus *every* such long block admits an abstract full/selected
age discrepancy at its first auxiliary step, not just K4.

This is a purely graph-age obstruction. It neither proves that
the auxiliary future type enters the complete Algorithm 5.4
parameter closure, nor refutes the particular resolved copy.
The finite K4 instance is already checked separately.
-/

namespace Kk

/-- The clique multiplicity on supports x, z, and x+z,
with arbitrary nonnegative integer weights. -/
def twoSortNatWeight (t : Fin 3) (w : Fin 2 → Nat) : Nat :=
  if t = 0 then w 0 else if t = 1 then w 1 else w 0 + w 1

/-- Literal consistency via integer multiplicity witnesses; the
values of a K_ell graph-age function lie in 1,...,ell-1. -/
def IsTwoSortEllAge (ell : Nat) (F : Fin 3 → Nat) : Prop :=
  (∀ t : Fin 3, 1 ≤ F t ∧ F t < ell) ∧
  ∀ t : Fin 3, ∃ w : Fin 2 → Nat,
    twoSortNatWeight t w = F t ∧
    ∀ u : Fin 3, twoSortNatWeight u w ≤ F u

def uniformBefore (s : Nat) (t : Fin 3) : Nat :=
  if t = 0 then s+1 else if t = 1 then 1 else s+2

def uniformAfter (s : Nat) (t : Fin 3) : Nat :=
  if t = 1 then 1 else s+1

theorem uniformBefore_valid
    (ell s : Nat) (hs : 1 ≤ s) (hTop : s+3 ≤ ell) :
    IsTwoSortEllAge ell (uniformBefore s) := by
  constructor
  · intro t
    fin_cases t <;> simp [uniformBefore] <;> omega
  · intro t
    fin_cases t
    · refine ⟨(fun i : Fin 2 => if i = 0 then s+1 else 0), ?_, ?_⟩
      · simp [twoSortNatWeight, uniformBefore]
      · intro u
        fin_cases u <;> simp [twoSortNatWeight, uniformBefore] <;> omega
    · refine ⟨(fun i : Fin 2 => if i = 1 then 1 else 0), ?_, ?_⟩
      · simp [twoSortNatWeight, uniformBefore]
      · intro u
        fin_cases u <;> simp [twoSortNatWeight, uniformBefore] <;> omega
    · refine ⟨(fun i : Fin 2 => if i = 0 then s+1 else 1), ?_, ?_⟩
      · simp [twoSortNatWeight, uniformBefore]
      · intro u
        fin_cases u <;> simp [twoSortNatWeight, uniformBefore] <;> omega

theorem uniformAfter_valid
    (ell s : Nat) (hs : 1 ≤ s) (hTop : s+3 ≤ ell) :
    IsTwoSortEllAge ell (uniformAfter s) := by
  constructor
  · intro t
    fin_cases t <;> simp [uniformAfter] <;> omega
  · intro t
    fin_cases t
    · refine ⟨(fun i : Fin 2 => if i = 0 then s+1 else 0), ?_, ?_⟩
      · simp [twoSortNatWeight, uniformAfter]
      · intro u
        fin_cases u <;> simp [twoSortNatWeight, uniformAfter] <;> omega
    · refine ⟨(fun i : Fin 2 => if i = 1 then 1 else 0), ?_, ?_⟩
      · simp [twoSortNatWeight, uniformAfter]
      · intro u
        fin_cases u <;> simp [twoSortNatWeight, uniformAfter] <;> omega
    · refine ⟨(fun i : Fin 2 => if i = 0 then s+1 else 0), ?_, ?_⟩
      · simp [twoSortNatWeight, uniformAfter]
      · intro u
        fin_cases u <;> simp [twoSortNatWeight, uniformAfter] <;> omega

theorem uniformAfter_lt_before (s : Nat) :
    TwoSortAgeLe (uniformAfter s) (uniformBefore s) ∧
    ¬ TwoSortAgeLe (uniformBefore s) (uniformAfter s) := by
  constructor
  · intro t
    fin_cases t <;> simp [uniformBefore, uniformAfter] <;> omega
  · intro h
    have h2 := h 2
    simp [TwoSortAgeLe, uniformBefore, uniformAfter] at h2
    omega

/-- The only changed bound is mixed support x+z, dropping by ONE.
There is no intermediate graph-age function, even without invoking
consistency (a stronger order-theoretic conclusion). -/
theorem uniformAfter_covers_before
    (s : Nat) (G : Fin 3 → Nat)
    (hLow : TwoSortAgeLe (uniformAfter s) G)
    (hHigh : TwoSortAgeLe G (uniformBefore s)) :
    G = uniformAfter s ∨ G = uniformBefore s := by
  have hx : G 0 = s+1 := by
    have h1 := hLow 0
    have h2 := hHigh 0
    simp [uniformAfter, uniformBefore] at h1 h2
    omega
  have hz : G 1 = 1 := by
    have h1 := hLow 1
    have h2 := hHigh 1
    simp [uniformAfter, uniformBefore] at h1 h2
    omega
  have hm : G 2 = s+1 ∨ G 2 = s+2 := by
    have h1 := hLow 2
    have h2 := hHigh 2
    simp [uniformAfter, uniformBefore] at h1 h2
    omega
  rcases hm with h | h
  · left
    funext t
    fin_cases t <;> simp [uniformAfter, hx, hz, h]
  · right
    funext t
    fin_cases t <;> simp [uniformBefore, hx, hz, h]

/-- Every K_ell canonical cover block of length r>=2 has the
same abstract failure of projection to selected one-sort data.
No property of the specially resolved H copy is asserted. -/
theorem uniform_auxiliary_shadow_cover
    (ell s : Nat) (hs : 1 ≤ s) (hTop : s+3 ≤ ell) :
    IsTwoSortEllAge ell (uniformBefore s) ∧
    IsTwoSortEllAge ell (uniformAfter s) ∧
    (∀ G : Fin 3 → Nat, TwoSortAgeLe (uniformAfter s) G →
      TwoSortAgeLe G (uniformBefore s) →
      G = uniformAfter s ∨ G = uniformBefore s) ∧
    uniformBefore s 0 = uniformAfter s 0 ∧
    uniformBefore s 2 ≠ uniformAfter s 2 := by
  refine ⟨uniformBefore_valid ell s hs hTop,
    uniformAfter_valid ell s hs hTop,
    uniformAfter_covers_before s, ?_, ?_⟩
  · simp [uniformBefore, uniformAfter]
  · simp [uniformBefore, uniformAfter]

end Kk
