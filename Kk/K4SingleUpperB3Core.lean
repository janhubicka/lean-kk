import Kk.K4AuxiliaryShadow
import Kk.HensonEncoding
import SuccessorTree.V10.LocalAgeForbiddenTest
import Mathlib.Tactic

/-!
# Small explicit K4 continuation defeating single-upper-type B3

This is the minimal combinatorial age-test obstruction behind the
second reserved cut of the Henson clique-block audit.

The lower socle has two adjacent vertices 0--1, the tested cut
is 1, and each of two future vertices 2,3 has the identical
complete K4-free upper L-type adjacent to both lower vertices.
The future vertices are adjacent. Thus the four vertices make
K4, but deleting the tested cut leaves only three vertices and
avoids the entire normalized forbidden family (loop, both
asymmetries, K4).

The theorem gives a genuine failure of the actual
CommonSocleAgeTest on the ONE complete future L-type, not just
an abstract graph-age-function cover. The separate application
to numerical H requires transporting this small age test to the
full initial L-socle 0,...,22, showing that all its extra old
vertices are harmless. No Kpt shape map is assumed.
-/

namespace Kk

open SuccessorTree.V10

/-- The symmetric complete four-vertex graph, with a finite carrier
and neutral diagonal. Its L-only age-test may fail K4 even though
its one-cut-deleted reduct is K4-free. -/
def fourCliqueCore : AgeTestModel 1 0 1 where
  carrier := {x | x < 4}
  binary := fun x y _ => decide (x ≠ y)
  unary := fun _ t => Fin.elim0 t
  diagonal := fun _ _ => false

def fourCliqueSocle : AgeTestModel 1 0 1 :=
  fourCliqueCore.restrictCarrier (fun x => x ≤ 1)

def fourCliqueUpper : RelationalPrefixType 2 1 0 1 :=
  RelationalPrefixType.ofAgeModel fourCliqueCore 2 2

theorem fourCliqueCore_finite : fourCliqueCore.BoundedCarrier := by
  exact ⟨4,fun x hx => hx⟩

theorem fourCliqueCore_sameSocle :
    SameInitialL fourCliqueCore fourCliqueSocle 1 := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x hx
    change (x < 4 ↔ x < 4 ∧ x ≤ 1)
    omega
  · intro x y hx hy t
    rfl
  · intro x hx t
    exact Fin.elim0 t
  · intro x hx t
    rfl

/-- The two upper vertices have exactly the same complete L-type
on the common lower socle. Both directed orientations, loop bits
and the (empty) unary language are included. -/
theorem fourCliqueCore_upper_types :
    UpperTypesPrescribed fourCliqueCore 1
      (fun R => R = fourCliqueUpper) := by
  intro x hx hAbove
  have hxBound : x < 4 := hx
  have hxEq : x = 2 ∨ x = 3 := by omega
  rcases hxEq with rfl | rfl
  · rfl
  · apply RelationalPrefixType.eq_of_atoms
    · intro a b t
      fin_cases t
      cases a with
      | none =>
        cases b with
        | none => decide
        | some j => fin_cases j <;> decide
      | some i =>
        fin_cases i
        · cases b with
          | none => decide
          | some j => fin_cases j <;> decide
        · cases b with
          | none => decide
          | some j => fin_cases j <;> decide
    · intro a t
      exact Fin.elim0 t
    · intro a t
      fin_cases t
      rfl

/-- Deleting cut 1 leaves exactly three vertices. Hence no
four-vertex ordered induced clique can survive in the carrier. -/
theorem fourCliqueCore_deleted_noK4 :
    ¬ ∃ f : Fin 4 → Nat,
      (fourCliqueCore.withoutVertex 1).Realizes
        (cliquePattern 4) f := by
  rintro ⟨f,hCopy⟩
  have h0 := hCopy.2.1 (0 : Fin 4)
  have h1 := hCopy.2.1 (1 : Fin 4)
  have h2 := hCopy.2.1 (2 : Fin 4)
  have h3 := hCopy.2.1 (3 : Fin 4)
  change f 0 < 4 ∧ f 0 ≠ 1 at h0
  change f 1 < 4 ∧ f 1 ≠ 1 at h1
  change f 2 < 4 ∧ f 2 ≠ 1 at h2
  change f 3 < 4 ∧ f 3 ≠ 1 at h3
  have h01 : f 0 < f 1 := hCopy.1 (by decide)
  have h12 : f 1 < f 2 := hCopy.1 (by decide)
  have h23 : f 2 < f 3 := hCopy.1 (by decide)
  omega

/-- After deleting the tested cut the finite L-structure avoids
ALL FOUR components of the normalized Henson K4 signature,
not only the symmetric clique itself. -/
theorem fourCliqueCore_deleted_avoids :
    ∀ bad, bad ∈ hensonForbiddenFamily 4 (by decide) →
      bad.Avoids (fourCliqueCore.withoutVertex 1) := by
  intro bad hBad
  simp [hensonForbiddenFamily] at hBad
  rcases hBad with h | h | h | h
  · rw [h]
    change ¬ ∃ f : Fin 1 → Nat,
      (fourCliqueCore.withoutVertex 1).Realizes loopPattern f
    rintro ⟨f,hCopy⟩
    have hDiag := hCopy.2.2.2.2 (0 : Fin 1) (0 : Fin 1)
    simp [fourCliqueCore, loopPattern] at hDiag
  · rw [h]
    change ¬ ∃ f : Fin 2 → Nat,
      (fourCliqueCore.withoutVertex 1).Realizes forwardAsymPattern f
    rintro ⟨f,hCopy⟩
    have hNE : f 1 ≠ f 0 := (ne_of_gt (hCopy.1 (by decide)))
    have hRev := hCopy.2.2.1 (1 : Fin 2) (0 : Fin 2) (by decide) (0 : Fin 1)
    simp [fourCliqueCore, forwardAsymPattern, hNE] at hRev
  · rw [h]
    change ¬ ∃ f : Fin 2 → Nat,
      (fourCliqueCore.withoutVertex 1).Realizes backwardAsymPattern f
    rintro ⟨f,hCopy⟩
    have hNE : f 0 ≠ f 1 := (ne_of_lt (hCopy.1 (by decide)))
    have hForward := hCopy.2.2.1 (0 : Fin 2) (1 : Fin 2) (by decide) (0 : Fin 1)
    simp [fourCliqueCore, backwardAsymPattern, hNE] at hForward
  · rw [h]
    exact fourCliqueCore_deleted_noK4

theorem fourCliqueCore_realizesK4 :
    ∃ f : Fin 4 → Nat,
      fourCliqueCore.Realizes (cliquePattern 4) f := by
  refine ⟨Fin.val, ?_, ?_, ?_, ?_, ?_⟩
  · exact Fin.val_strictMono
  · intro a
    exact a.isLt
  · intro a b hNE t
    fin_cases t
    change decide ((a : Nat) ≠ (b : Nat)) = decide (a ≠ b)
    have hv : (a : Nat) ≠ (b : Nat) := by
      intro h
      exact hNE (Fin.ext h)
    simp [hv,hNE]
  · intro a t
    exact Fin.elim0 t
  · intro a t
    rfl

/-- A genuinely bounded finite K4 continuation, using only TWO
copies of ONE upper L-type, witnesses the failure of corrected B3
at the second gadget cut in the minimal two-vertex socle model. -/
theorem fourCliqueCore_singleUpper_B3_fails :
    ¬ CommonSocleAgeTest
      (hensonForbiddenFamily 4 (by decide))
      fourCliqueSocle 1
      (fun R => R = fourCliqueUpper) := by
  intro hB3
  have hK4mem :
      (NormalizedForbidden.nontrivial 4
        (cliquePattern 4) (by decide) (cliquePattern_irreducible 4)) ∈
        hensonForbiddenFamily 4 (by decide) := by
    simp [hensonForbiddenFamily]
  have hNoForbidden :
      ∀ bad, bad ∈ hensonForbiddenFamily 4 (by decide) →
        bad.Avoids (fourCliqueCore.withoutVertex 1) :=
    fourCliqueCore_deleted_avoids
  have hFullAvoid :=
    hB3 fourCliqueCore fourCliqueCore_finite fourCliqueCore_sameSocle
      fourCliqueCore_upper_types hNoForbidden
      (NormalizedForbidden.nontrivial 4
        (cliquePattern 4) (by decide) (cliquePattern_irreducible 4))
      hK4mem
  exact hFullAvoid fourCliqueCore_realizesK4

end Kk
