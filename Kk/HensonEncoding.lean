import SuccessorTree.V10.BinaryUnaryAgeAdapter
import SuccessorTree.V10.AdmissibleKptPrefix
import Mathlib.Tactic

/-!
# The undirected K_ell-free age in the normalized binary language

An irreflexive undirected graph is represented by one directed Boolean
binary symbol with a separate diagonal record. Since the generic
successor machinery admits all directed structures, its forbidden
family must additionally exclude loops and BOTH asymmetric
two-vertex configurations.

These are genuine normalized forbidden patterns: the loop is a
non-neutral singleton, and the other three patterns are irreducible.
The last one is the complete symmetric K_ell pattern.

The graph-age equivalence and concrete Henson/Fraisse limit adapter
are tracked separately. In particular, merely defining this family
does not assert the published K_k-specific upper bound.
-/

namespace Kk

open SuccessorTree.V10

/-- The normalized model of a one-binary-symbol graph. Unary types
are absent, and loops occupy the distinct diagonal channel. -/
def normalizedGraphModel (E : Nat → Nat → Bool) :
    AgeTestModel 1 0 1 :=
  binaryUnaryAgeModel Set.univ (fun x y _ => E x y)
    (fun _ t => Fin.elim0 t)

/-- Exclude positive loops. -/
def loopPattern : ForbiddenAtomicPattern 1 1 0 1 where
  binary := fun _ _ _ => false
  unary := fun _ t => Fin.elim0 t
  diagonal := fun _ _ => true

theorem loopPattern_nonNeutral :
    loopPattern.NonNeutralSingleton :=
  Or.inr ⟨0, rfl⟩

/-- An asymmetric pair whose forward directed bit is one. -/
def forwardAsymPattern : ForbiddenAtomicPattern 2 1 0 1 where
  binary := fun a b _ => decide (a < b)
  unary := fun _ t => Fin.elim0 t
  diagonal := fun _ _ => false

/-- The reverse asymmetric pair. Both orientations must be forbidden
because forbidden-pattern embeddings preserve the enumeration. -/
def backwardAsymPattern : ForbiddenAtomicPattern 2 1 0 1 where
  binary := fun a b _ => decide (b < a)
  unary := fun _ t => Fin.elim0 t
  diagonal := fun _ _ => false

theorem forwardAsymPattern_irreducible :
    forwardAsymPattern.Irreducible := by
  intro a b hab
  refine ⟨0, ?_⟩
  rcases lt_or_gt_of_ne hab with h | h
  · exact Or.inl (by simp [forwardAsymPattern, h])
  · exact Or.inr (by simp [forwardAsymPattern, h])

theorem backwardAsymPattern_irreducible :
    backwardAsymPattern.Irreducible := by
  intro a b hab
  refine ⟨0, ?_⟩
  rcases lt_or_gt_of_ne hab with h | h
  · exact Or.inr (by simp [backwardAsymPattern, h])
  · exact Or.inl (by simp [backwardAsymPattern, h])

/-- A complete undirected clique encoded by both positive directed
bits for every distinct pair, with a false diagonal. -/
def cliquePattern (ell : Nat) : ForbiddenAtomicPattern ell 1 0 1 where
  binary := fun a b _ => decide (a ≠ b)
  unary := fun _ t => Fin.elim0 t
  diagonal := fun _ _ => false

theorem cliquePattern_irreducible (ell : Nat) :
    (cliquePattern ell).Irreducible := by
  intro a b hab
  exact ⟨0, Or.inl (by simp [cliquePattern, hab])⟩

/-- Exactly the four kinds of forbidden induced ordered patterns
needed to encode loop-free symmetric K_ell-free graphs. The
asymmetric configurations are essential: the successor library
does not implicitly assume symmetry of its binary symbols. -/
def hensonForbiddenFamily (ell : Nat) (hell : 2 ≤ ell) :
    List (NormalizedForbidden 1 0 1) :=
  [ .singleton loopPattern loopPattern_nonNeutral,
    .nontrivial 2 forwardAsymPattern (by omega)
      forwardAsymPattern_irreducible,
    .nontrivial 2 backwardAsymPattern (by omega)
      backwardAsymPattern_irreducible,
    .nontrivial ell (cliquePattern ell) (by omega)
      (cliquePattern_irreducible ell) ]

/-- Any model avoiding the concrete family has no loops. This is
proved directly from the induced singleton avoidance, not assumed
as part of the normalized language. -/
theorem hensonForbiddenFamily_no_loops
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E)) :
    ∀ i : Nat, E i i = false := by
  intro i
  cases hE : E i i with
  | false => rfl
  | true =>
      exfalso
      let f : Fin 1 → Nat := fun _ => i
      have hRealizes :
          (normalizedGraphModel E).Realizes loopPattern f := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro a b hab
          exact ((ne_of_lt hab) (Subsingleton.elim a b)).elim
        · intro a
          simp [normalizedGraphModel, binaryUnaryAgeModel]
        · intro a b hab t
          exact (hab (Subsingleton.elim a b)).elim
        · intro a t
          exact Fin.elim0 t
        · intro a t
          simpa [normalizedGraphModel, binaryUnaryAgeModel,
            loopPattern, f] using hE
      have hBad :
          (NormalizedForbidden.singleton loopPattern
            loopPattern_nonNeutral) ∈ hensonForbiddenFamily ell hell := by
        simp [hensonForbiddenFamily]
      exact (hAvoid _ hBad) ⟨f, hRealizes⟩

end Kk
