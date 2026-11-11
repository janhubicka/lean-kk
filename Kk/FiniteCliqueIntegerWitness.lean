import Kk.IntegerAgeUniversalProperties
import Kk.FiniteCliqueSupportWitness
import Mathlib.Tactic

/-!
# Real finite clique witnesses as exact normalized integer graph-age vectors

English proof and hostile audit were committed BEFORE this file:
  docs/finite_clique_to_integer_age_witness_english_audit.md

The fiber cardinalities of every finite vertex set with < ell vertices
are an actual IntegerCliqueWeights d ell, with exact counts on EVERY
support. A normalized vector need not be realized by any given future
vertex pool: a verified empty-pool counterexample rules out that shortcut.
Canonicalization preserves the JOINT support-bound system on each small
realized clique, never an arbitrary single bound by itself.

For arbitrary W, the verified old-plus-future K_ell-free test implies
that every directed clique subset of W is small enough to normalize.
These claims concern ordinary finite L-clique graphs, not auxiliary
Kpt E, full parameter-closed B3, or a common labelled source orbit.
-/

namespace Kk

/-- Exact number of vertices of a given sort. -/
def finiteCliqueSortCount {d : Nat} (sort : Nat → Fin d)
    (s : Finset Nat) (j : Fin d) : Nat :=
  (s.filter (fun v => sort v = j)).card

theorem finiteCliqueSortCount_le {d : Nat} (sort : Nat → Fin d)
    (s : Finset Nat) (j : Fin d) :
    finiteCliqueSortCount sort s j ≤ s.card := by
  unfold finiteCliqueSortCount
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem finiteCliqueSortCount_sum_support {d : Nat}
    (sort : Nat → Fin d) (s : Finset Nat) (T : Finset (Fin d)) :
    (∑ j ∈ T, finiteCliqueSortCount sort s j) =
      (s.filter (fun v => sort v ∈ T)).card := by
  classical
  exact Finset.sum_card_fiberwise_eq_card_filter s T sort

theorem finiteCliqueSortCount_sum_univ {d : Nat}
    (sort : Nat → Fin d) (s : Finset Nat) :
    (∑ j : Fin d, finiteCliqueSortCount sort s j) = s.card := by
  classical
  have h : (s : Set Nat).MapsTo sort (Finset.univ : Finset (Fin d)) := by
    intro x hx
    exact Finset.mem_univ (sort x)
  exact (Finset.card_eq_sum_card_fiberwise h).symm

/-- Every finite set below the clique threshold is represented by
    the *actual* normalized integer graph-age witness type. -/
def integerCliqueWeightsOfFinset {d ell : Nat}
    (sort : Nat → Fin d) (s : Finset Nat) (hsize : s.card < ell) :
    IntegerCliqueWeights d ell := by
  classical
  refine ⟨(fun j => ⟨finiteCliqueSortCount sort s j,
      Nat.lt_of_le_of_lt (finiteCliqueSortCount_le sort s j) hsize⟩), ?_⟩
  change (∑ j : Fin d, finiteCliqueSortCount sort s j) ≤ ell - 1
  rw [finiteCliqueSortCount_sum_univ]
  omega

theorem integerCliqueOnSupport_of_finset {d ell : Nat}
    (sort : Nat → Fin d) (s : Finset Nat) (hsize : s.card < ell)
    (T : IntegerGraphSupport d ell) :
    integerCliqueOnSupport (integerCliqueWeightsOfFinset sort s hsize) T =
      (s.filter (fun v => sort v ∈ T.1)).card := by
  change (∑ j ∈ T.1, finiteCliqueSortCount sort s j) = _
  exact finiteCliqueSortCount_sum_support sort s T.1

/-- The subtype's global weight is not just bounded: it is EXACTLY
    the number of vertices of the original finite clique. -/
theorem integerCliqueWeightsOfFinset_total_eq {d ell : Nat}
    (sort : Nat → Fin d) (s : Finset Nat) (hsize : s.card < ell) :
    (∑ j : Fin d, ((integerCliqueWeightsOfFinset sort s hsize).1 j).val) =
      s.card := by
  change (∑ j : Fin d, finiteCliqueSortCount sort s j) = s.card
  exact finiteCliqueSortCount_sum_univ sort s

/-- For every finite set with size below ell there EXISTS a normalized
    witness whose counts on EVERY admissible support agree exactly. -/
theorem integerCliqueWeights_exists_of_finset {d ell : Nat}
    (sort : Nat → Fin d) (s : Finset Nat) (hsize : s.card < ell) :
    ∃ w : IntegerCliqueWeights d ell,
      ∀ T : IntegerGraphSupport d ell,
        integerCliqueOnSupport w T =
          (s.filter (fun v => sort v ∈ T.1)).card := by
  exact ⟨integerCliqueWeightsOfFinset sort s hsize,
    integerCliqueOnSupport_of_finset sort s hsize⟩

theorem integerCliqueWeightsOfFinset_respects_iff {d ell : Nat}
    (sort : Nat → Fin d) (s : Finset Nat) (hsize : s.card < ell)
    (B : IntegerGraphSupport d ell → Nat) :
    WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell)) B
      (integerCliqueWeightsOfFinset sort s hsize) ↔
    ∀ T : IntegerGraphSupport d ell,
      (s.filter (fun v => sort v ∈ T.1)).card ≤ B T := by
  constructor
  · intro h T
    rw [← integerCliqueOnSupport_of_finset sort s hsize T]
    exact h T
  · intro h T
    rw [integerCliqueOnSupport_of_finset sort s hsize T]
    exact h T

/-- The exact finite-clique raw-constraint transfer is valid for an
arbitrary canonicalizer that preserves the *entire* system of normalized
integer vector constraints. -/
theorem finiteCliqueSortConstraints_canonical_iff
    {d ell : Nat}
    (sort : Nat → Fin d) (s : Finset Nat) (hsize : s.card < ell)
    (B C : IntegerGraphSupport d ell → Nat)
    (hPreserves : ∀ w : IntegerCliqueWeights d ell,
      WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell)) C w ↔
        WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell)) B w) :
    (∀ T : IntegerGraphSupport d ell,
      (s.filter (fun v => sort v ∈ T.1)).card ≤ C T) ↔
    (∀ T : IntegerGraphSupport d ell,
      (s.filter (fun v => sort v ∈ T.1)).card ≤ B T) := by
  let w := integerCliqueWeightsOfFinset sort s hsize
  have hCanon := integerCliqueWeightsOfFinset_respects_iff sort s hsize C
  have hRaw := integerCliqueWeightsOfFinset_respects_iff sort s hsize B
  exact hCanon.symm.trans ((hPreserves w).trans hRaw)

/-- The all-clique version requires ONLY the independently established
K_ell-free size bound for the realized cliques of W. -/
theorem finiteCliqueSortConstraints_all_canonical_iff
    {d ell : Nat} (sort : Nat → Fin d) (W : Finset Nat)
    (B C : IntegerGraphSupport d ell → Nat)
    (IsClique : Finset Nat → Prop)
    (hSmall : ∀ s, s ⊆ W → IsClique s → s.card < ell)
    (hPreserves : ∀ w : IntegerCliqueWeights d ell,
      WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell)) C w ↔
        WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell)) B w) :
    (∀ s : Finset Nat, s ⊆ W → IsClique s →
      ∀ T : IntegerGraphSupport d ell,
        (s.filter (fun v => sort v ∈ T.1)).card ≤ C T) ↔
    (∀ s : Finset Nat, s ⊆ W → IsClique s →
      ∀ T : IntegerGraphSupport d ell,
        (s.filter (fun v => sort v ∈ T.1)).card ≤ B T) := by
  constructor
  · intro h s hsW hsClique
    exact (finiteCliqueSortConstraints_canonical_iff sort s
      (hSmall s hsW hsClique) B C hPreserves).mp (h s hsW hsClique)
  · intro h s hsW hsClique
    exact (finiteCliqueSortConstraints_canonical_iff sort s
      (hSmall s hsW hsClique) B C hPreserves).mpr (h s hsW hsClique)

/-- A counterexample to surjectivity of the normalized weight map:
the all-zero image of an empty future pool cannot realize the 1-vertex
weight vector, even though that vector is normalized below ell=3. -/
def oneSortOneWeight : IntegerCliqueWeights 1 3 := by
  refine ⟨(fun _ => (1 : Fin 3)), ?_⟩
  decide

theorem oneSortOneWeight_not_from_empty :
    ¬ ∃ (s : Finset Nat) (hsize : s.card < 3),
      s ⊆ (∅ : Finset Nat) ∧
      integerCliqueWeightsOfFinset (fun _ : Nat => (0 : Fin 1)) s hsize =
        oneSortOneWeight := by
  rintro ⟨s, hsize, hsEmpty, hEq⟩
  have hs : s = ∅ := Finset.subset_empty.mp hsEmpty
  subst s
  have hVal := congrArg (fun w : IntegerCliqueWeights 1 3 => (w.1 (0 : Fin 1)).val) hEq
  have hZero :
      ((integerCliqueWeightsOfFinset (fun _ : Nat => (0 : Fin 1))
        (∅ : Finset Nat) hsize).1 (0 : Fin 1)).val = 0 := rfl
  have hOne : (oneSortOneWeight.1 (0 : Fin 1)).val = 1 := rfl
  rw [hZero, hOne] at hVal
  cases hVal

/-- The existing integer graph-age canonicalizer preserves the ENTIRE
support-bound system for the concrete finite clique's multiplicity
vector. This is NOT an equivalence for an arbitrary support in isolation. -/
theorem finiteCliqueSortConstraints_integerCanonical_iff
    {d ell : Nat} (sort : Nat → Fin d)
    (s : Finset Nat) (hsize : s.card < ell)
    (B : IntegerGraphSupport d ell → Nat) :
    (∀ T : IntegerGraphSupport d ell,
      (s.filter (fun v => sort v ∈ T.1)).card ≤
        integerGraphAgeCanonical d ell B T) ↔
    (∀ T : IntegerGraphSupport d ell,
      (s.filter (fun v => sort v ∈ T.1)).card ≤ B T) := by
  exact finiteCliqueSortConstraints_canonical_iff sort s hsize
    B (integerGraphAgeCanonical d ell B)
    (fun w => integerGraphAgeCanonical_preserves_clique_vectors d ell B w)

/-- In a finite K_ell-free directed graph W, every directed clique
subset s has fewer than ell vertices and therefore produces a normalized
integer witness. No completeness assumption on W is used. -/
theorem finiteClique_card_lt_of_pool_cliqueFree
    (E : Nat → Nat → Bool) (ell : Nat) (W s : Finset Nat)
    (hFree : finitePoolCliqueCheck E ell W = false)
    (hsW : s ⊆ W) (hsClique : IsDirectedCliqueOn E s) :
    s.card < ell := by
  exact lt_of_le_of_lt
    (directedClique_card_le_capacity E W s hsW hsClique)
    ((finitePoolCliqueCheck_false_iff_capacity_lt E ell W).mp hFree)

/-- Exact full-system canonicalization invariance for ALL realized
cliques in an arbitrary K_ell-free finite W. -/
theorem finiteClique_all_constraints_integerCanonical_iff
    {d ell : Nat} (E : Nat → Nat → Bool)
    (W : Finset Nat) (sort : Nat → Fin d)
    (B : IntegerGraphSupport d ell → Nat)
    (hFree : finitePoolCliqueCheck E ell W = false) :
    (∀ s : Finset Nat, s ⊆ W → IsDirectedCliqueOn E s →
      ∀ T : IntegerGraphSupport d ell,
        (s.filter (fun v => sort v ∈ T.1)).card ≤
          integerGraphAgeCanonical d ell B T) ↔
    (∀ s : Finset Nat, s ⊆ W → IsDirectedCliqueOn E s →
      ∀ T : IntegerGraphSupport d ell,
        (s.filter (fun v => sort v ∈ T.1)).card ≤ B T) := by
  exact finiteCliqueSortConstraints_all_canonical_iff
    sort W B (integerGraphAgeCanonical d ell B)
    (IsDirectedCliqueOn E)
    (fun s hsW hsClique =>
      finiteClique_card_lt_of_pool_cliqueFree E ell W s hFree hsW hsClique)
    (fun w => integerGraphAgeCanonical_preserves_clique_vectors d ell B w)

/-- The independent old-plus-future K_ell-free test in the actual
four-pool gluing theorem already implies that W is K_ell-free.
The result uses the exact directed clique-capacity monotonicity. -/
theorem finitePoolCliqueCheck_oldFuture_implies_future_false
    (E : Nat → Nat → Bool) (ell : Nat) (P W : Finset Nat)
    (hOldFuture : finitePoolCliqueCheck E ell (P ∪ W) = false) :
    finitePoolCliqueCheck E ell W = false := by
  have hSub : W ⊆ P ∪ W := by
    intro x hx
    exact Finset.mem_union.mpr (Or.inr hx)
  have hBound := finiteDirectedCliqueCapacity_mono E W (P ∪ W) hSub
  have hLess :=
    (finitePoolCliqueCheck_false_iff_capacity_lt E ell (P ∪ W)).mp hOldFuture
  exact (finitePoolCliqueCheck_false_iff_capacity_lt E ell W).mpr
    (lt_of_le_of_lt hBound hLess)

/-- The canonicalizer preserves the joint support constraints for
EVERY finite continuation clique as soon as the gluing theorem's
old-plus-future test holds. No new age or realization assumption. -/
theorem finiteClique_oldFuture_all_constraints_canonical_iff
    {d ell : Nat} (E : Nat → Nat → Bool)
    (P W : Finset Nat) (sort : Nat → Fin d)
    (B : IntegerGraphSupport d ell → Nat)
    (hOldFuture : finitePoolCliqueCheck E ell (P ∪ W) = false) :
    (∀ s : Finset Nat, s ⊆ W → IsDirectedCliqueOn E s →
      ∀ T : IntegerGraphSupport d ell,
        (s.filter (fun v => sort v ∈ T.1)).card ≤
          integerGraphAgeCanonical d ell B T) ↔
    (∀ s : Finset Nat, s ⊆ W → IsDirectedCliqueOn E s →
      ∀ T : IntegerGraphSupport d ell,
        (s.filter (fun v => sort v ∈ T.1)).card ≤ B T) := by
  exact finiteClique_all_constraints_integerCanonical_iff
    E W sort B
    (finitePoolCliqueCheck_oldFuture_implies_future_false E ell P W
      hOldFuture)

-- Exact finite clique sort fibers and normalized weight constructor.
#print axioms Kk.finiteCliqueSortCount_sum_support
#print axioms Kk.finiteCliqueSortCount_sum_univ
#print axioms Kk.integerCliqueWeightsOfFinset_total_eq
#print axioms Kk.integerCliqueWeights_exists_of_finset
#print axioms Kk.integerCliqueOnSupport_of_finset
#print axioms Kk.integerCliqueWeightsOfFinset_respects_iff
-- Generic + actual joint canonicalizer, and negative surjectivity control.
#print axioms Kk.finiteCliqueSortConstraints_canonical_iff
#print axioms Kk.finiteCliqueSortConstraints_all_canonical_iff
#print axioms Kk.oneSortOneWeight_not_from_empty
#print axioms Kk.finiteCliqueSortConstraints_integerCanonical_iff
#print axioms Kk.finiteClique_card_lt_of_pool_cliqueFree
#print axioms Kk.finiteClique_all_constraints_integerCanonical_iff
#print axioms Kk.finitePoolCliqueCheck_oldFuture_implies_future_false
#print axioms Kk.finiteClique_oldFuture_all_constraints_canonical_iff

end Kk
