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


/-- The complete symmetric clique is the only remaining irreducible
obstruction once positive loops and asymmetric pairs have been excluded.

Here clique-freeness is stated on increasing enumerations, exactly as
the normalized induced forbidden-pattern semantics require. Every
undirected clique has such an increasing enumeration. -/
theorem hensonForbiddenFamily_no_cliques
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E)) :
    ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true) := by
  rintro ⟨f, hf, hEdges⟩
  have hLoops := hensonForbiddenFamily_no_loops ell hell E hAvoid
  have hRealizes :
      (normalizedGraphModel E).Realizes (cliquePattern ell) f := by
    refine ⟨hf, ?_, ?_, ?_, ?_⟩
    · intro a
      simp [normalizedGraphModel, binaryUnaryAgeModel]
    · intro a b hab t
      change E (f a) (f b) = decide (a ≠ b)
      simpa [hab] using hEdges a b hab
    · intro a t
      exact Fin.elim0 t
    · intro a t
      change E (f a) (f a) = false
      exact hLoops (f a)
  have hBad :
      (NormalizedForbidden.nontrivial ell (cliquePattern ell)
        (by omega) (cliquePattern_irreducible ell)) ∈
        hensonForbiddenFamily ell hell := by
    simp [hensonForbiddenFamily]
  exact (hAvoid _ hBad) ⟨f, hRealizes⟩


/-- Given an irreflexive directed graph, a positive forward edge
and an absent reverse edge literally realise the ordered forbidden
forward-asymmetric pair. -/
private theorem forwardAsym_realizes
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (x y : Nat) (hxy : x < y)
    (hForward : E x y = true)
    (hBackward : E y x = false) :
    (normalizedGraphModel E).Realizes forwardAsymPattern
      (fun z : Fin 2 => if z = 0 then x else y) := by
  let f : Fin 2 → Nat := fun z => if z = 0 then x else y
  have hMono : StrictMono f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f]
  refine ⟨hMono, ?_, ?_, ?_, ?_⟩
  · intro a
    simp [normalizedGraphModel, binaryUnaryAgeModel]
  · intro a b hab t
    fin_cases a <;> fin_cases b <;>
      simp_all [normalizedGraphModel, binaryUnaryAgeModel,
        forwardAsymPattern, f]
  · intro a t
    exact Fin.elim0 t
  · intro a t
    fin_cases a <;>
      simp [normalizedGraphModel, binaryUnaryAgeModel,
        forwardAsymPattern, f, hLoops]

/-- The other orientation is an independently forbidden induced
two-vertex configuration: ordered embeddings cannot swap its labels. -/
private theorem backwardAsym_realizes
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (x y : Nat) (hxy : x < y)
    (hForward : E x y = false)
    (hBackward : E y x = true) :
    (normalizedGraphModel E).Realizes backwardAsymPattern
      (fun z : Fin 2 => if z = 0 then x else y) := by
  let f : Fin 2 → Nat := fun z => if z = 0 then x else y
  have hMono : StrictMono f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f]
  refine ⟨hMono, ?_, ?_, ?_, ?_⟩
  · intro a
    simp [normalizedGraphModel, binaryUnaryAgeModel]
  · intro a b hab t
    fin_cases a <;> fin_cases b <;>
      simp_all [normalizedGraphModel, binaryUnaryAgeModel,
        backwardAsymPattern, f]
  · intro a t
    exact Fin.elim0 t
  · intro a t
    fin_cases a <;>
      simp [normalizedGraphModel, binaryUnaryAgeModel,
        backwardAsymPattern, f, hLoops]

/-- Avoiding both asymmetric induced ordered pairs forces a genuinely
symmetric binary relation. Symmetry is a conclusion, not an implicit
assumption of the general successor library. -/
theorem hensonForbiddenFamily_symmetric
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E)) :
    ∀ x y : Nat, E x y = E y x := by
  have hLoops := hensonForbiddenFamily_no_loops ell hell E hAvoid
  have hNoForward :
      ¬ ∃ f : Fin 2 → Nat,
        (normalizedGraphModel E).Realizes forwardAsymPattern f := by
    apply hAvoid (.nontrivial 2 forwardAsymPattern (by omega)
      forwardAsymPattern_irreducible)
    simp [hensonForbiddenFamily]
  have hNoBackward :
      ¬ ∃ f : Fin 2 → Nat,
        (normalizedGraphModel E).Realizes backwardAsymPattern f := by
    apply hAvoid (.nontrivial 2 backwardAsymPattern (by omega)
      backwardAsymPattern_irreducible)
    simp [hensonForbiddenFamily]
  have hOrdered : ∀ x y : Nat, x < y → E x y = E y x := by
    intro x y hxy
    cases hf : E x y with
    | false =>
        cases hb : E y x with
        | false => rfl
        | true =>
            exfalso
            exact hNoBackward ⟨_,
              backwardAsym_realizes E hLoops x y hxy hf hb⟩
    | true =>
        cases hb : E y x with
        | false =>
            exfalso
            exact hNoForward ⟨_,
              forwardAsym_realizes E hLoops x y hxy hf hb⟩
        | true => rfl
  intro x y
  rcases lt_trichotomy x y with h | h | h
  · exact hOrdered x y h
  · subst y
    rfl
  · exact (hOrdered y x h).symm


/-- The complete elementary language dictionary: avoidance of the
actual normalized irreducible forbidden family is equivalent to being
an irreflexive symmetric graph with no ordered complete K_ell.

No graph symmetry, looplessness or clique-freeness is tacitly built
into AgeTestModel; all are recovered from explicit forbidden data. -/
theorem hensonForbiddenFamily_avoids_iff
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool) :
    (∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E)) ↔
    (∀ i, E i i = false) ∧
    (∀ x y, E x y = E y x) ∧
    (¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true)) := by
  constructor
  · intro hAvoid
    exact ⟨hensonForbiddenFamily_no_loops ell hell E hAvoid,
      hensonForbiddenFamily_symmetric ell hell E hAvoid,
      hensonForbiddenFamily_no_cliques ell hell E hAvoid⟩
  · rintro ⟨hLoops, hSym, hNoCliques⟩
    intro bad hBad
    simp [hensonForbiddenFamily] at hBad
    rcases hBad with rfl | rfl | rfl | rfl
    · change ¬ ∃ f : Fin 1 → Nat,
        (normalizedGraphModel E).Realizes loopPattern f
      rintro ⟨f, hRealizes⟩
      have he : E (f 0) (f 0) = true := by
        have h := hRealizes.2.2.2.2 (0 : Fin 1) (0 : Fin 1)
        simpa [normalizedGraphModel, binaryUnaryAgeModel,
          loopPattern] using h
      rw [hLoops (f 0)] at he
      cases he
    · change ¬ ∃ f : Fin 2 → Nat,
        (normalizedGraphModel E).Realizes forwardAsymPattern f
      rintro ⟨f, hRealizes⟩
      have hf : E (f 0) (f 1) = true := by
        have h := hRealizes.2.2.1
          (0 : Fin 2) (1 : Fin 2) (by decide) (0 : Fin 1)
        simpa [normalizedGraphModel, binaryUnaryAgeModel,
          forwardAsymPattern] using h
      have hb : E (f 1) (f 0) = false := by
        have h := hRealizes.2.2.1
          (1 : Fin 2) (0 : Fin 2) (by decide) (0 : Fin 1)
        simpa [normalizedGraphModel, binaryUnaryAgeModel,
          forwardAsymPattern] using h
      have hs := hSym (f 0) (f 1)
      rw [hf, hb] at hs
      cases hs
    · change ¬ ∃ f : Fin 2 → Nat,
        (normalizedGraphModel E).Realizes backwardAsymPattern f
      rintro ⟨f, hRealizes⟩
      have hf : E (f 0) (f 1) = false := by
        have h := hRealizes.2.2.1
          (0 : Fin 2) (1 : Fin 2) (by decide) (0 : Fin 1)
        simpa [normalizedGraphModel, binaryUnaryAgeModel,
          backwardAsymPattern] using h
      have hb : E (f 1) (f 0) = true := by
        have h := hRealizes.2.2.1
          (1 : Fin 2) (0 : Fin 2) (by decide) (0 : Fin 1)
        simpa [normalizedGraphModel, binaryUnaryAgeModel,
          backwardAsymPattern] using h
      have hs := hSym (f 0) (f 1)
      rw [hf, hb] at hs
      cases hs
    · change ¬ ∃ f : Fin ell → Nat,
        (normalizedGraphModel E).Realizes (cliquePattern ell) f
      rintro ⟨f, hRealizes⟩
      have hComplete :
          ∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true := by
        intro a b hab
        have h := hRealizes.2.2.1 a b hab (0 : Fin 1)
        simpa [normalizedGraphModel, binaryUnaryAgeModel,
          cliquePattern, hab] using h
      exact hNoCliques ⟨f, hRealizes.1, hComplete⟩

end Kk
