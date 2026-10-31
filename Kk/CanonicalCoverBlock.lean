import Mathlib.Tactic

/-!
# Canonical raw cover blocks: the exact order-theoretic step

Let C be a class of graph-age functions ordered pointwise. Suppose the
canonicalizer G sends a raw bound B to the greatest admissible member
of C below B, whenever at least one admissible member lies below B.

For a *genuine* cover F' ⋖ F whose unique changed coordinate T
drops from F(T)=F'(T)+1, set r = ell-1-F'(T).
The ideal block of a auxiliary clique constraints is:
  B_a(T) = min(F(T), ell-1-a),   B_a(U) = F(U) otherwise.
Then G(B_a)=F for a<r and G(B_r)=F'.

We prove the entire Nat-arithmetic/cover/canonicalizer deduction.
The graph-age definition and the greatest-age canonicalization
theorem must still be supplied by the K_k specialization.
No new axiom, opaque placeholder, or Ramsey theorem is introduced.
-/

namespace Kk

universe u

/-- Pointwise order on integer-valued age records. -/
def AgeLe {ι : Type u} (A B : ι → Nat) : Prop :=
  ∀ i, A i ≤ B i

/-- A genuine cover in a prescribed class of admissible age records. -/
structure AgeCover {ι : Type u}
    (IsAge : (ι → Nat) → Prop)
    (lower upper : ι → Nat) : Prop where
  lower_age : IsAge lower
  upper_age : IsAge upper
  le : AgeLe lower upper
  strict : lower ≠ upper
  no_intermediate :
    ∀ H, IsAge H → AgeLe lower H → AgeLe H upper →
      H = lower ∨ H = upper

/-- One ideal clique-capacity constraint on a single support T. -/
def rawCliqueBlockBound {ι : Type u} [DecidableEq ι]
    (ell a : Nat) (upper : ι → Nat) (T : ι) : ι → Nat :=
  fun U => if U = T then min (upper U) (ell - 1 - a) else upper U

/-- Before the final clique vertex, the ideal raw bound is literally F. -/
theorem rawCliqueBlockBound_eq_upper_of_lt
    {ι : Type u} [DecidableEq ι]
    (ell r a : Nat) (lower upper : ι → Nat) (T : ι)
    (hEll : ell = lower T + r + 1)
    (hAt : upper T = lower T + 1)
    (ha : a < r) :
    rawCliqueBlockBound ell a upper T = upper := by
  funext U
  by_cases hU : U = T
  · subst U
    have hBound : upper T ≤ ell - 1 - a := by omega
    simp [rawCliqueBlockBound, Nat.min_eq_left hBound]
  · simp [rawCliqueBlockBound, hU]

/-- At the last clique vertex, the lower age lies below the new raw bound. -/
theorem ageLe_final_rawCliqueBlockBound
    {ι : Type u} [DecidableEq ι]
    (ell r : Nat) (lower upper : ι → Nat) (T : ι)
    (hLE : AgeLe lower upper)
    (hEll : ell = lower T + r + 1)
    (hAt : upper T = lower T + 1) :
    AgeLe lower (rawCliqueBlockBound ell r upper T) := by
  intro U
  by_cases hU : U = T
  · subst U
    have hEq : ell - 1 - r = lower T := by omega
    simpa [rawCliqueBlockBound, hEq] using hLE T
  · simpa [rawCliqueBlockBound, hU] using hLE U

/-- A raw clique-block constraint never weakens the original bounds. -/
theorem rawCliqueBlockBound_le_upper
    {ι : Type u} [DecidableEq ι]
    (ell a : Nat) (upper : ι → Nat) (T : ι) :
    AgeLe (rawCliqueBlockBound ell a upper T) upper := by
  intro U
  by_cases hU : U = T
  · subst U
    simp only [rawCliqueBlockBound, if_pos rfl]
    exact Nat.min_le_left _ _
  · simp [rawCliqueBlockBound, hU]

/-- The nontrivial final-stage deduction needs exactly the usual
properties of the canonical graph-age operation, displayed as
hypotheses rather than assumed as axioms. -/
theorem canonical_cover_block_final
    {ι : Type u} [DecidableEq ι]
    (ell r : Nat) (IsAge : (ι → Nat) → Prop)
    (canonical : (ι → Nat) → (ι → Nat))
    (lower upper : ι → Nat) (T : ι)
    (hCover : AgeCover IsAge lower upper)
    (hEll : ell = lower T + r + 1)
    (hAt : upper T = lower T + 1)
    (hCanonicalAge :
      ∀ B, AgeLe lower B → IsAge (canonical B))
    (hCanonicalLe :
      ∀ B, AgeLe (canonical B) B)
    (hCanonicalGreatest :
      ∀ B H, IsAge H → AgeLe H B → AgeLe H (canonical B)) :
    canonical (rawCliqueBlockBound ell r upper T) = lower := by
  let B := rawCliqueBlockBound ell r upper T
  have hLB : AgeLe lower B :=
    ageLe_final_rawCliqueBlockBound ell r lower upper T
      hCover.le hEll hAt
  have hCL : AgeLe lower (canonical B) :=
    hCanonicalGreatest B lower hCover.lower_age hLB
  have hCU : AgeLe (canonical B) upper := by
    intro i
    exact le_trans (hCanonicalLe B i)
      (rawCliqueBlockBound_le_upper ell r upper T i)
  have hNotUpper : canonical B ≠ upper := by
    intro heq
    have hBound := hCanonicalLe B T
    rw [heq] at hBound
    dsimp [B, rawCliqueBlockBound] at hBound
    simp only [ite_true] at hBound
    omega
  rcases hCover.no_intermediate (canonical B)
    (hCanonicalAge B hLB) hCL hCU with h | h
  · exact h
  · exact False.elim (hNotUpper h)

/-- Complete stage-by-stage identity for the ideal selected-front
raw bounds, conditional only on the canonicalizer's exact
admissibility, bound, and maximality properties. -/
theorem canonical_cover_block_all_stages
    {ι : Type u} [DecidableEq ι]
    (ell r : Nat) (IsAge : (ι → Nat) → Prop)
    (canonical : (ι → Nat) → (ι → Nat))
    (lower upper : ι → Nat) (T : ι)
    (hCover : AgeCover IsAge lower upper)
    (hEll : ell = lower T + r + 1)
    (hAt : upper T = lower T + 1)
    (hCanonicalAge :
      ∀ B, AgeLe lower B → IsAge (canonical B))
    (hCanonicalLe :
      ∀ B, AgeLe (canonical B) B)
    (hCanonicalGreatest :
      ∀ B H, IsAge H → AgeLe H B → AgeLe H (canonical B))
    (a : Nat) (ha : a ≤ r) :
    canonical (rawCliqueBlockBound ell a upper T) =
      if a < r then upper else lower := by
  by_cases hLt : a < r
  · rw [if_pos hLt,
      rawCliqueBlockBound_eq_upper_of_lt ell r a lower upper T
        hEll hAt hLt]
    apply funext
    intro i
    exact Nat.le_antisymm
      (hCanonicalLe upper i)
      (hCanonicalGreatest upper upper hCover.upper_age
        (fun _ => le_refl _) i)
  · have hEq : a = r := by omega
    subst a
    rw [if_neg (lt_irrefl r)]
    exact canonical_cover_block_final ell r IsAge canonical
      lower upper T hCover hEll hAt hCanonicalAge
      hCanonicalLe hCanonicalGreatest

end Kk
