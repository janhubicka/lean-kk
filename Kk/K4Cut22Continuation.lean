import Kk.HensonEncoding
import SuccessorTree.V10.LocalAgeForbiddenTest
import Mathlib.Tactic

/-!
# A full-socle finite B3 witness at the second K4 gadget cut

The actual numerical H example has the cut 22. Before that cut the
L-graph on vertices 0,...,22 has exactly one edge, {10,22}.
The higher original at 38 is adjacent to every EVEN old coordinate
0,...,22 and to no odd one. Add two future vertices 23 and 24
realizing that same complete upper L-type and join them by an edge.

This finite ordered graph now has a K4 {10,22,23,24}; but after
deleting the tested cut 22 its old socle is edgeless, and only two
future vertices remain. Thus it avoids K4 after the deletion.

All singleton loops and directed asymmetries are also absent.
This module proves the exact CommonSocleAgeTest failure over the
WHOLE 23-element socle, not just a four-vertex toy model.

The remaining application step is to prove that the induced L socle
and the cut-22 upper type coincide with the ACTUAL numerical H
model built from the stated four-vertex K4-free base. This module
does not assert that equality without proof, and it makes no
claim about a particular AlgorithmRun selection.
-/

namespace Kk

open SuccessorTree.V10

/-- The complete sparse L-only model, with two identical upper
types at coordinates 23,24. The lower socle contains 0,...,22.
All ordered binary atoms, including negative bits, are explicit. -/
def k4Cut22Continuation : AgeTestModel 1 0 1 where
  carrier := {x | x < 25}
  binary := fun x y _ =>
    if x ≤ 22 then
      if y ≤ 22 then
        decide ((x = 10 ∧ y = 22) ∨ (x = 22 ∧ y = 10))
      else decide (x % 2 = 0)
    else if y ≤ 22 then decide (y % 2 = 0)
    else decide (x ≠ y)
  unary := fun _ t => Fin.elim0 t
  diagonal := fun _ _ => false

/-- The first 23 vertices with their complete directed L-atoms. -/
def k4Cut22Socle : AgeTestModel 1 0 1 :=
  k4Cut22Continuation.restrictCarrier (fun x => x ≤ 22)

/-- Full L-type of the first future vertex; the second one
realizes the same type with all negative facts preserved. -/
def k4Cut22Upper : RelationalPrefixType 23 1 0 1 :=
  RelationalPrefixType.ofAgeModel k4Cut22Continuation 23 23

theorem k4Cut22_finite : k4Cut22Continuation.BoundedCarrier := by
  exact ⟨25,fun x hx => hx⟩

theorem k4Cut22_sameSocle :
    SameInitialL k4Cut22Continuation k4Cut22Socle 22 := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x hx
    change (x < 25 ↔ x < 25 ∧ x ≤ 22)
    omega
  · intros; rfl
  · intro x hx t
    exact Fin.elim0 t
  · intros; rfl

/-- The two complete upper types of the finite continuation coincide,
including both directed L-columns and negative relations. -/
theorem k4Cut22_upper_types :
    UpperTypesPrescribed k4Cut22Continuation 22
      (fun R => R = k4Cut22Upper) := by
  intro x hx hAbove
  have hBound : x < 25 := hx
  have hxCase : x = 23 ∨ x = 24 := by omega
  rcases hxCase with rfl | rfl
  · rfl
  · apply RelationalPrefixType.eq_of_atoms
    · intro a b t
      fin_cases t
      cases a with
      | none =>
        cases b with
        | none => rfl
        | some j =>
          have hj : j.val ≤ 22 := by omega
          change k4Cut22Continuation.binary 24 j.val (0 : Fin 1) =
            k4Cut22Continuation.binary 23 j.val (0 : Fin 1)
          simp [k4Cut22Continuation, hj]
      | some i =>
        cases b with
        | none =>
          have hi : i.val ≤ 22 := by omega
          change k4Cut22Continuation.binary i.val 24 (0 : Fin 1) =
            k4Cut22Continuation.binary i.val 23 (0 : Fin 1)
          simp [k4Cut22Continuation, hi]
        | some j => rfl
    · intro a t
      exact Fin.elim0 t
    · intro a t
      fin_cases t
      rfl

theorem k4Cut22_symmetric (x y : Nat) :
    k4Cut22Continuation.binary x y (0 : Fin 1) =
      k4Cut22Continuation.binary y x (0 : Fin 1) := by
  by_cases hx : x ≤ 22 <;> by_cases hy : y ≤ 22
  · have hPair :
        ((x = 10 ∧ y = 22) ∨ (x = 22 ∧ y = 10)) ↔
          ((y = 10 ∧ x = 22) ∨ (y = 22 ∧ x = 10)) := by tauto
    simpa [k4Cut22Continuation, hx, hy] using
      (congrArg decide (propext hPair))
  · simp [k4Cut22Continuation, hx, hy]
  · simp [k4Cut22Continuation, hx, hy]
  · simp [k4Cut22Continuation, hx, hy, eq_comm]

/-- After deleting the cut 22, any ordered four-clique would have
to contain two distinct old vertices below 22. Those are nonadjacent
in this exact model. -/
theorem k4Cut22_deleted_noK4 :
    ¬ ∃ f : Fin 4 → Nat,
      (k4Cut22Continuation.withoutVertex 22).Realizes
        (cliquePattern 4) f := by
  rintro ⟨f,hCopy⟩
  have h0 := hCopy.2.1 (0 : Fin 4)
  have h1 := hCopy.2.1 (1 : Fin 4)
  have h2 := hCopy.2.1 (2 : Fin 4)
  have h3 := hCopy.2.1 (3 : Fin 4)
  change f 0 < 25 ∧ f 0 ≠ 22 at h0
  change f 1 < 25 ∧ f 1 ≠ 22 at h1
  change f 2 < 25 ∧ f 2 ≠ 22 at h2
  change f 3 < 25 ∧ f 3 ≠ 22 at h3
  have h01 : f 0 < f 1 := hCopy.1 (by decide)
  have h12 : f 1 < f 2 := hCopy.1 (by decide)
  have h23 : f 2 < f 3 := hCopy.1 (by decide)
  have hf1 : f 1 < 22 := by omega
  have hf0 : f 0 < 22 := by omega
  have hEdge : k4Cut22Continuation.binary (f 0) (f 1) (0 : Fin 1) =
      true := by
    have he := hCopy.2.2.1 (0 : Fin 4) (1 : Fin 4) (by decide) (0 : Fin 1)
    change k4Cut22Continuation.binary (f 0) (f 1) (0 : Fin 1) = true at he
    exact he
  have hNoEdge : k4Cut22Continuation.binary (f 0) (f 1) (0 : Fin 1) =
      false := by
    simp [k4Cut22Continuation, show f 0 ≤ 22 by omega,
      show f 1 ≤ 22 by omega,
      show f 0 ≠ 22 by omega,
      show f 1 ≠ 22 by omega]
  rw [hNoEdge] at hEdge
  contradiction

theorem k4Cut22_deleted_avoids :
    ∀ bad, bad ∈ hensonForbiddenFamily 4 (by decide) →
      bad.Avoids (k4Cut22Continuation.withoutVertex 22) := by
  intro bad hBad
  simp [hensonForbiddenFamily] at hBad
  rcases hBad with h | h | h | h
  · rw [h]
    change ¬ ∃ f : Fin 1 → Nat,
      (k4Cut22Continuation.withoutVertex 22).Realizes loopPattern f
    rintro ⟨f,hCopy⟩
    have hDiag := hCopy.2.2.2.2 (0 : Fin 1) (0 : Fin 1)
    change false = true at hDiag
    contradiction
  · rw [h]
    change ¬ ∃ f : Fin 2 → Nat,
      (k4Cut22Continuation.withoutVertex 22).Realizes forwardAsymPattern f
    rintro ⟨f,hCopy⟩
    have hForward := hCopy.2.2.1 (0 : Fin 2) (1 : Fin 2) (by decide) (0 : Fin 1)
    have hReverse := hCopy.2.2.1 (1 : Fin 2) (0 : Fin 2) (by decide) (0 : Fin 1)
    change k4Cut22Continuation.binary (f 0) (f 1) (0 : Fin 1) = true at hForward
    change k4Cut22Continuation.binary (f 1) (f 0) (0 : Fin 1) = false at hReverse
    rw [k4Cut22_symmetric (f 0) (f 1), hReverse] at hForward
    contradiction
  · rw [h]
    change ¬ ∃ f : Fin 2 → Nat,
      (k4Cut22Continuation.withoutVertex 22).Realizes backwardAsymPattern f
    rintro ⟨f,hCopy⟩
    have hForward := hCopy.2.2.1 (0 : Fin 2) (1 : Fin 2) (by decide) (0 : Fin 1)
    have hReverse := hCopy.2.2.1 (1 : Fin 2) (0 : Fin 2) (by decide) (0 : Fin 1)
    change k4Cut22Continuation.binary (f 0) (f 1) (0 : Fin 1) = false at hForward
    change k4Cut22Continuation.binary (f 1) (f 0) (0 : Fin 1) = true at hReverse
    rw [k4Cut22_symmetric (f 0) (f 1), hReverse] at hForward
    contradiction
  · rw [h]
    exact k4Cut22_deleted_noK4

/-- Four strictly increasing vertices 10,22,23,24 constitute K4. -/
def k4Cut22Embedding (a : Fin 4) : Nat :=
  if a = 0 then 10 else if a = 1 then 22 else if a = 2 then 23 else 24

theorem k4Cut22_realizesK4 :
    ∃ f : Fin 4 → Nat,
      k4Cut22Continuation.Realizes (cliquePattern 4) f := by
  refine ⟨k4Cut22Embedding, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · intro a
    fin_cases a <;> simp [k4Cut22Embedding, k4Cut22Continuation]
  · intro a b hab t
    fin_cases a <;> fin_cases b <;> fin_cases t <;>
      simp_all [k4Cut22Embedding, k4Cut22Continuation, cliquePattern]
  · intro a t
    exact Fin.elim0 t
  · intro a t
    rfl

/-- This is a full 23-vertex initial-socle corrected-B3 failure
using only repetitions of ONE complete prescribed upper L-type. -/
theorem k4Cut22_singleUpper_B3_fails :
    ¬ CommonSocleAgeTest
      (hensonForbiddenFamily 4 (by decide))
      k4Cut22Socle 22
      (fun R => R = k4Cut22Upper) := by
  intro hB3
  have hK4mem :
      (NormalizedForbidden.nontrivial 4
        (cliquePattern 4) (by decide) (cliquePattern_irreducible 4)) ∈
        hensonForbiddenFamily 4 (by decide) := by
    simp [hensonForbiddenFamily]
  have hFullAvoid :=
    hB3 k4Cut22Continuation k4Cut22_finite k4Cut22_sameSocle
      k4Cut22_upper_types k4Cut22_deleted_avoids
      (NormalizedForbidden.nontrivial 4
        (cliquePattern 4) (by decide) (cliquePattern_irreducible 4))
      hK4mem
  exact hFullAvoid k4Cut22_realizesK4

end Kk
