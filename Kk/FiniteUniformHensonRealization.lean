import Kk.UniformFiniteHensonFront
import Kk.RelativeUniversalFiniteTarget
import Mathlib.Tactic

/-!
# KK Track A: ONE actual Henson-original future realizes EVERY finite age profile

English proof and adversarial audit were committed BEFORE this Lean file:
  docs/finite_uniform_henson_realization_english_audit.md

The input is ONLY one fixed normalized left-dense Henson original E,
one literal old initial segment [0,b), and arbitrary complete typed
old-to-new columns c(p,t). The bounded finite ordinary-L target A is
NOT assumed to exist: it is explicitly built from the old prefix and
the finite tagged universal future of ALL raw-feasible normalized
integer clique vectors. The all-support mixed-clique condition proves
A is genuinely K_ell-free.

The already verified pinned-Henson single-embedding transport then
provides ONE induced chronological embedding f, identity on the entire
old prefix, that realizes ALL B_P-feasible labelled clique profiles
simultaneously in ONE actual physical finite future f(W) with no
spurious profiles. Every omitted earlier original has zero adjacency
to the new original in BOTH ordered directions.

The result does NOT construct a coherent infinite resolved diary,
a fixed numerical-H top pool with full auxiliary H+ E relations,
parameter-closed corrected B3 or common labelled inverse-source
orbit, and does not establish the final big Ramsey degrees.
-/

namespace Kk

/-- Genuine *uniform finite relative* Henson realization for EVERY
normalized clique vector permitted by the COMPLETE original old
prefix's clique-capacity bounds.

There is NO existence hypothesis for a compatible finite universal
target: it is a concrete finite graph A, formed over the literal old
prefix E and the exact tagged universal future; its K_ell-freeness,
every permitted component clique, and absence of spurious cliques
follow from the explicitly checked combinatorial source proofs.

One f witnesses ALL feasible vectors in its common finite image W'.
The supported-sort test on W' is literal membership in a finite
image of the typed target pool and needs no global Henson colouring.

The finite target's future vertices are abstractly numbered in
[b,b+card V); the physical f-images are genuinely later original
indices of the UNCHANGED E, not consecutive dummy indices.
-/
theorem henson_leftDense_realizes_all_finite_relative_age_profiles
    (d ell b : Nat) (hell : 2 ≤ ell) (hd : 0 < d)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool) :
    let B := finiteOldColumnRawBound E ell d (Finset.range b) c
    let V := RelativeUniversalTaggedVertex d ell B
    let N := b + Fintype.card V
    let W : Finset Nat := finiteTaggedFuturePool (V := V) b
    let A : Nat → Nat → Bool := finiteTaggedOldFutureEdge b E
      (relativeUniversalTaggedEdge d ell B)
      (relativeUniversalTaggedSort d ell B) c
    let tau : Nat → Fin d := finiteTaggedFutureSort hd
      (relativeUniversalTaggedSort d ell B) b
    ∃ f : Nat → Nat,
      (∀ i, i < b → f i = i) ∧
      (∀ i j, i < N → j < N → i < j → f i < f j) ∧
      (∀ i j, i < N → j < N → i ≠ j →
        E (f i) (f j) = A i j) ∧
      (∀ m, b ≤ m → m < N → ∀ z, z < f m →
        z ∉ (Finset.range m).image f →
          E z (f m) = false ∧ E (f m) z = false) ∧
      (∀ x ∈ W, b ≤ f x) ∧
      (∀ v : IntegerCliqueWeights d ell,
        v ∈ feasibleIntegerCliqueVectors d ell B ↔
        ∃ t : Finset Nat,
          t ⊆ W.image f ∧ IsDirectedCliqueOn E t ∧
          (∀ T : IntegerGraphSupport d ell,
            (t.filter (pulledBackFiniteSortIn W tau f T)).card =
              integerCliqueOnSupport v T)) := by
  classical
  let B : IntegerGraphSupport d ell → Nat :=
    finiteOldColumnRawBound E ell d (Finset.range b) c
  let V := RelativeUniversalTaggedVertex d ell B
  let N : Nat := b + Fintype.card V
  let R : V → V → Bool := relativeUniversalTaggedEdge d ell B
  let sort : V → Fin d := relativeUniversalTaggedSort d ell B
  let A : Nat → Nat → Bool := finiteTaggedOldFutureEdge b E R sort c
  let W : Finset Nat := finiteTaggedFuturePool (V := V) b
  let tau : Nat → Fin d := finiteTaggedFutureSort hd sort b
  have hSymE : ∀ x y : Nat, E x y = E y x :=
    hensonForbiddenFamily_symmetric ell hell E hAvoid
  have hLoopsE : ∀ x : Nat, E x x = false :=
    hensonForbiddenFamily_no_loops ell hell E hAvoid
  have hOldFree : finitePoolCliqueCheck E ell (Finset.range b) = false := by
    apply (finitePoolCliqueCheck_false_iff E ell (Finset.range b)).2
    rintro ⟨s, hsP, hsCard, hsClique⟩
    have hBad : HasCliqueBelow E b ell := by
      refine ⟨s, hsCard, ?_, hsClique⟩
      intro x hx
      exact Finset.mem_range.mp (hsP hx)
    exact (hensonForbiddenFamily_no_prefix_cliques
      ell hell E hAvoid b) hBad
  have hASym : ∀ x y : Nat, A x y = A y x := by
    intro x y
    exact finiteTaggedEdge_symmetric b E R sort c
      (fun i j _ _ => hSymE i j)
      (by
        intro v w
        exact relativeUniversalTaggedEdge_symmetric d ell B v w)
      x y
  have hALoops : ∀ x : Nat, A x x = false := by
    intro x
    exact finiteTaggedEdge_irreflexive b E R sort c
      (fun i _ => hLoopsE i)
      (by
        intro v
        exact relativeUniversalTaggedEdge_irreflexive d ell B v)
      x
  have hOldEq : ∀ i j, i < b → j < b → i ≠ j →
      A i j = E i j := by
    intro i j hi hj _
    exact finiteTaggedEdge_old_old b E R sort c i j hi hj
  have hN : b ≤ N := by dsimp [N]; omega
  have hSafeTarget : finitePoolCliqueCheck A ell (Finset.range N) = false :=
    finiteOldPrefix_universal_tagged_target_KFree
      d ell b hell hd E c hOldFree
  have hAFree : ¬ HasCliqueBelow A N ell := by
    rintro ⟨s, hsCard, hsN, hsClique⟩
    have hsP : s ⊆ Finset.range N := by
      intro x hx
      exact Finset.mem_range.mpr (hsN x hx)
    exact ((finitePoolCliqueCheck_false_iff
      A ell (Finset.range N)).1 hSafeTarget)
      ⟨s, hsP, hsCard, hsClique⟩
  have hWAfter : ∀ x ∈ W, b ≤ x ∧ x < N := by
    intro x hx
    exact (finiteTaggedFuturePool_mem_iff (V := V) b x).mp hx
  have hAllVectors : ∀ v : IntegerCliqueWeights d ell,
      v ∈ feasibleIntegerCliqueVectors d ell B →
        ∃ s : Finset Nat,
          s ⊆ W ∧ IsDirectedCliqueOn A s ∧
          (∀ T : IntegerGraphSupport d ell,
            (s.filter (fun x => tau x ∈ T.1)).card =
              integerCliqueOnSupport v T) := by
    intro v hv
    exact finiteOldPrefix_universal_tagged_target_realizes_every
      d ell b hell hd E c B v hv
  have hNoSpurious : ∀ s : Finset Nat,
      s ⊆ W → IsDirectedCliqueOn A s →
      ∀ T : IntegerGraphSupport d ell,
        (s.filter (fun x => tau x ∈ T.1)).card ≤ B T := by
    exact finiteOldPrefix_universal_tagged_target_no_spurious
      d ell b hell hd E c B
  exact henson_leftDense_uniform_finite_profiles_over_fixed_prefix
    ell b N d hell hN A E hASym hALoops hOldEq hAvoid hDense
    hAFree W tau B hWAfter hAllVectors hNoSpurious

#print axioms Kk.henson_leftDense_realizes_all_finite_relative_age_profiles

end Kk
