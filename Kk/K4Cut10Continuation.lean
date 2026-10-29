import Kk.HensonEncoding
import SuccessorTree.V10.LocalAgeForbiddenTest
import Mathlib.Tactic

/-!
# The full-socle first-gadget K4 corrected-B3 continuation

The numerical-H running example has first reserved original q1 at
cut 10, second reserved original q2 at 22 and top selected original
x at 38. The actual L-reduct through coordinate 10 is edgeless.
The later complete type q2 through cut 10 is adjacent only to q1=10,
while the selected top type x is adjacent to each even old coordinate.

We construct a finite ordered L-only continuation on 0,...,13,
retaining the exact 11-vertex initial socle, with future vertices
11 (type q2) and 12,13 (two copies of type x). Join all three
future vertices. The induced K4 {10,11,12,13} contains the tested
cut; deleting 10 leaves a K4-free, symmetric, irreflexive model.

This is a genuine failure of CommonSocleAgeTest for the TWO
specified complete upper L-types, not merely of a selected one-sort
graph age. There is no auxiliary E on the arbitrary age witness.

A later transfer will check these complete types against the
ACTUAL numerical H Kpt originals and use the verified AlgorithmRun
closure selection to show the full selected-stage corrected B3
fails at cut 10. This module makes no such claim by itself.
-/

namespace Kk

open SuccessorTree.V10

/-- The full first-cut L-only continuation, with 11 old
socle vertices and three newly chosen future vertices. -/
def k4Cut10Continuation : AgeTestModel 1 0 1 where
  carrier := {x | x < 14}
  binary := fun x y _ =>
    if x ≤ 10 then
      if y ≤ 10 then false
      else if y = 11 then decide (x = 10)
      else decide (x % 2 = 0)
    else if y ≤ 10 then
      if x = 11 then decide (y = 10)
      else decide (y % 2 = 0)
    else decide (x ≠ y)
  unary := fun _ t => Fin.elim0 t
  diagonal := fun _ _ => false

def k4Cut10Socle : AgeTestModel 1 0 1 :=
  k4Cut10Continuation.restrictCarrier (fun x => x ≤ 10)

/-- Complete future q2 type, including every negative L atom. -/
def k4Cut10UpperQ2 : RelationalPrefixType 11 1 0 1 :=
  RelationalPrefixType.ofAgeModel k4Cut10Continuation 11 11

/-- Complete future active x type. Both 12 and 13 realize it. -/
def k4Cut10UpperX : RelationalPrefixType 11 1 0 1 :=
  RelationalPrefixType.ofAgeModel k4Cut10Continuation 11 12

theorem k4Cut10_finite : k4Cut10Continuation.BoundedCarrier := by
  exact ⟨14, fun x hx => hx⟩

theorem k4Cut10_sameSocle :
    SameInitialL k4Cut10Continuation k4Cut10Socle 10 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    change (x < 14 ↔ x < 14 ∧ x ≤ 10)
    omega
  · intros; rfl
  · intro x hx t
    exact Fin.elim0 t
  · intros; rfl

/-- The q2 and selected x complete upper L-types comprise
every future vertex of the continuation. The two copies of
x have all atomic bits identical through the tested cut. -/
theorem k4Cut10_upper_types :
    UpperTypesPrescribed k4Cut10Continuation 10
      (fun R => R = k4Cut10UpperQ2 ∨ R = k4Cut10UpperX) := by
  intro x hx hAbove
  have hxBound : x < 14 := hx
  have hxCases : x = 11 ∨ x = 12 ∨ x = 13 := by omega
  rcases hxCases with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · right
    apply RelationalPrefixType.eq_of_atoms
    · intro a b t
      fin_cases t
      cases a with
      | none =>
        cases b with
        | none =>
          change k4Cut10Continuation.binary 13 13 (0 : Fin 1) =
            k4Cut10Continuation.binary 12 12 (0 : Fin 1)
          decide
        | some j =>
          have hj : j.val ≤ 10 := by omega
          change k4Cut10Continuation.binary 13 j.val (0 : Fin 1) =
            k4Cut10Continuation.binary 12 j.val (0 : Fin 1)
          simp [k4Cut10Continuation, hj]
      | some i =>
        cases b with
        | none =>
          have hi : i.val ≤ 10 := by omega
          change k4Cut10Continuation.binary i.val 13 (0 : Fin 1) =
            k4Cut10Continuation.binary i.val 12 (0 : Fin 1)
          simp [k4Cut10Continuation, hi]
        | some j => rfl
    · intro a t
      exact Fin.elim0 t
    · intro a t
      fin_cases t
      rfl

theorem k4Cut10_symmetric (x y : Nat) :
    k4Cut10Continuation.binary x y (0 : Fin 1) =
      k4Cut10Continuation.binary y x (0 : Fin 1) := by
  by_cases hx : x ≤ 10 <;> by_cases hy : y ≤ 10
  · simp [k4Cut10Continuation, hx, hy]
  · simp [k4Cut10Continuation, hx, hy]
  · simp [k4Cut10Continuation, hx, hy]
  · simp [k4Cut10Continuation, hx, hy, eq_comm]

/-- After deleting cut 10, any four-clique would have to
include at least one old socle vertex below 10 and the
future q2 vertex 11. But only deleted vertex 10 is
adjacent to q2 among old vertices. -/
theorem k4Cut10_deleted_noK4 :
    ¬ ∃ f : Fin 4 → Nat,
      (k4Cut10Continuation.withoutVertex 10).Realizes
        (cliquePattern 4) f := by
  rintro ⟨f,hCopy⟩
  have h0 := hCopy.2.1 (0 : Fin 4)
  have h1 := hCopy.2.1 (1 : Fin 4)
  have h3 := hCopy.2.1 (3 : Fin 4)
  change f 0 < 14 ∧ f 0 ≠ 10 at h0
  change f 1 < 14 ∧ f 1 ≠ 10 at h1
  change f 3 < 14 ∧ f 3 ≠ 10 at h3
  have h01 : f 0 < f 1 := hCopy.1 (by decide)
  have h12 : f 1 < f 2 := hCopy.1 (by decide)
  have h23 : f 2 < f 3 := hCopy.1 (by decide)
  have hf0 : f 0 < 10 := by omega
  have hEdge : k4Cut10Continuation.binary (f 0) (f 1) (0 : Fin 1) =
      true := by
    exact hCopy.2.2.1 (0 : Fin 4) (1 : Fin 4) (by decide) (0 : Fin 1)
  by_cases hOld : f 1 ≤ 10
  · have hNoEdge : k4Cut10Continuation.binary (f 0) (f 1) (0 : Fin 1) =
        false := by
      simp [k4Cut10Continuation, show f 0 ≤ 10 by omega, hOld]
    rw [hNoEdge] at hEdge
    contradiction
  · have hAt11 : f 1 = 11 := by omega
    have hNoEdge : k4Cut10Continuation.binary (f 0) (f 1) (0 : Fin 1) =
        false := by
      simp [k4Cut10Continuation, show f 0 ≤ 10 by omega, hAt11,
        show f 0 ≠ 10 by omega]
    rw [hNoEdge] at hEdge
    contradiction

/-- The cut-deleted model avoids all four indexed normalized
K4 forbidden patterns, not just its clique component. -/
theorem k4Cut10_deleted_avoids :
    ∀ bad, bad ∈ hensonForbiddenFamily 4 (by decide) →
      bad.Avoids (k4Cut10Continuation.withoutVertex 10) := by
  intro bad hBad
  simp [hensonForbiddenFamily] at hBad
  rcases hBad with h | h | h | h
  · rw [h]
    change ¬ ∃ f : Fin 1 → Nat,
      (k4Cut10Continuation.withoutVertex 10).Realizes loopPattern f
    rintro ⟨f,hCopy⟩
    have hDiag := hCopy.2.2.2.2 (0 : Fin 1) (0 : Fin 1)
    change false = true at hDiag
    contradiction
  · rw [h]
    change ¬ ∃ f : Fin 2 → Nat,
      (k4Cut10Continuation.withoutVertex 10).Realizes forwardAsymPattern f
    rintro ⟨f,hCopy⟩
    have hForward := hCopy.2.2.1 (0 : Fin 2) (1 : Fin 2) (by decide) (0 : Fin 1)
    have hReverse := hCopy.2.2.1 (1 : Fin 2) (0 : Fin 2) (by decide) (0 : Fin 1)
    change k4Cut10Continuation.binary (f 0) (f 1) (0 : Fin 1) = true at hForward
    change k4Cut10Continuation.binary (f 1) (f 0) (0 : Fin 1) = false at hReverse
    rw [k4Cut10_symmetric (f 0) (f 1), hReverse] at hForward
    contradiction
  · rw [h]
    change ¬ ∃ f : Fin 2 → Nat,
      (k4Cut10Continuation.withoutVertex 10).Realizes backwardAsymPattern f
    rintro ⟨f,hCopy⟩
    have hForward := hCopy.2.2.1 (0 : Fin 2) (1 : Fin 2) (by decide) (0 : Fin 1)
    have hReverse := hCopy.2.2.1 (1 : Fin 2) (0 : Fin 2) (by decide) (0 : Fin 1)
    change k4Cut10Continuation.binary (f 0) (f 1) (0 : Fin 1) = false at hForward
    change k4Cut10Continuation.binary (f 1) (f 0) (0 : Fin 1) = true at hReverse
    rw [k4Cut10_symmetric (f 0) (f 1), hReverse] at hForward
    contradiction
  · rw [h]
    exact k4Cut10_deleted_noK4

/-- Forbidden clique {10,11,12,13} witnesses the failed
B3 test, with cut 10 as an actual clique vertex. -/
def k4Cut10Embedding (a : Fin 4) : Nat :=
  if a = 0 then 10 else if a = 1 then 11 else if a = 2 then 12 else 13

theorem k4Cut10_realizesK4 :
    ∃ f : Fin 4 → Nat,
      k4Cut10Continuation.Realizes (cliquePattern 4) f := by
  refine ⟨k4Cut10Embedding, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · intro a
    fin_cases a <;> simp [k4Cut10Embedding, k4Cut10Continuation]
  · intro a b hab t
    fin_cases a <;> fin_cases b <;> fin_cases t <;>
      simp_all [k4Cut10Embedding, k4Cut10Continuation, cliquePattern]
  · intro a t
    exact Fin.elim0 t
  · intro a t
    rfl

/-- The first-cut finite continuation shows the failure of
corrected B3 for an upper spectrum containing q2 and x.
The full 11-vertex lower socle and all missing L atoms
are retained; nothing is asserted yet about the actual
selected parameter-closed source membership. -/
theorem k4Cut10_twoUpper_B3_fails :
    ¬ CommonSocleAgeTest
      (hensonForbiddenFamily 4 (by decide))
      k4Cut10Socle 10
      (fun R => R = k4Cut10UpperQ2 ∨ R = k4Cut10UpperX) := by
  intro hB3
  have hK4mem :
      (NormalizedForbidden.nontrivial 4
        (cliquePattern 4) (by decide) (cliquePattern_irreducible 4)) ∈
        hensonForbiddenFamily 4 (by decide) := by
    simp [hensonForbiddenFamily]
  have hFullAvoid :=
    hB3 k4Cut10Continuation k4Cut10_finite k4Cut10_sameSocle
      k4Cut10_upper_types k4Cut10_deleted_avoids
      (NormalizedForbidden.nontrivial 4
        (cliquePattern 4) (by decide) (cliquePattern_irreducible 4))
      hK4mem
  exact hFullAvoid k4Cut10_realizesK4

end Kk
