import Kk.IntegerWitnessCompleteComponent
import Kk.ExtensionProfileAge
import Mathlib.Tactic

/-!
# Concrete complete typed cliques attaining canonical graph-age bounds

English proof and hostile audit committed FIRST:
  docs/concrete_canonical_maximizers_english_audit.md

Every raw bound B (not necessarily itself a graph age) admits the zero
normalized labelled vector when ell>0. Each coordinate of its canonical
age G_B is thus attained by a feasible vector, represented by the actual
complete L-clique on the dependent finite type Sigma j, Fin (w_j).
All subcliques of any feasible component satisfy EVERY raw bound B(U).

The maximizer depends on T. Neither a single component simultaneously
attaining every coordinate nor a relative extension over a fixed Henson
prefix is asserted. No auxiliary Kpt E or full B3 equivalence follows.
-/

namespace Kk

/-- The genuine normalized all-zero multiplicity vector. The positivity
premise is needed: coordinatewise Fin 0 has no zero element. -/
def zeroIntegerCliqueWeight (d ell : Nat) (hell : 0 < ell) :
    IntegerCliqueWeights d ell := by
  classical
  refine ⟨(fun _ => (⟨0,hell⟩ : Fin ell)), ?_⟩
  simp

/-- The normalized zero vector respects ANY raw nonnegative support
bound, including an arbitrary noncanonical function B. -/
theorem zeroIntegerCliqueWeight_respects
    (d ell : Nat) (hell : 0 < ell)
    (B : IntegerGraphSupport d ell → Nat) :
    WitnessRespects
      (integerCliqueOnSupport (d := d) (ell := ell)) B
      (zeroIntegerCliqueWeight d ell hell) := by
  intro T
  change T.1.sum (fun _ => 0) ≤ B T
  simp

/-- For ell>0, the actual finite set of feasible normalized vectors
is nonempty for EVERY raw bound B. -/
theorem feasibleIntegerCliqueVectors_nonempty
    (d ell : Nat) (hell : 0 < ell)
    (B : IntegerGraphSupport d ell → Nat) :
    (feasibleIntegerCliqueVectors d ell B).Nonempty := by
  classical
  refine ⟨zeroIntegerCliqueWeight d ell hell, ?_⟩
  change (zeroIntegerCliqueWeight d ell hell) ∈
    Finset.univ.filter
      (WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell)) B)
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, zeroIntegerCliqueWeight_respects d ell hell B⟩

/-- Every coordinate T of the canonical graph age is attained by
a particular normalized labelled clique vector respecting the full
joint constraint system of arbitrary raw B. The vector may depend on T. -/
theorem integerGraphAgeCanonical_has_feasible_maximizer
    (d ell : Nat) (hell : 0 < ell)
    (B : IntegerGraphSupport d ell → Nat)
    (T : IntegerGraphSupport d ell) :
    ∃ w : IntegerCliqueWeights d ell,
      WitnessRespects
        (integerCliqueOnSupport (d := d) (ell := ell)) B w ∧
      integerCliqueOnSupport w T =
        integerGraphAgeCanonical d ell B T := by
  classical
  obtain ⟨w, hw, hMax⟩ := Finset.exists_mem_eq_sup
    (feasibleIntegerCliqueVectors d ell B)
    (feasibleIntegerCliqueVectors_nonempty d ell hell B)
    (fun v => integerCliqueOnSupport v T)
  have hwB :
      WitnessRespects
        (integerCliqueOnSupport (d := d) (ell := ell)) B w := by
    have hh : w ∈ Finset.univ.filter
        (WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell)) B) := by
      exact hw
    exact (Finset.mem_filter.mp hh).2
  refine ⟨w, hwB, ?_⟩
  simpa only [integerGraphAgeCanonical, finiteWitnessCanonical,
    feasibleIntegerCliqueVectors] using hMax.symm

/-- Concrete, complete, symmetric, irreflexive finite L-clique
witnessing the exact canonical value G_B(T), for arbitrary raw B.
Its total size is strictly less than ell. -/
theorem integerGraphAgeCanonical_has_concrete_clique_maximizer
    (d ell : Nat) (hell : 0 < ell)
    (B : IntegerGraphSupport d ell → Nat)
    (T : IntegerGraphSupport d ell) :
    ∃ w : IntegerCliqueWeights d ell,
      WitnessRespects
        (integerCliqueOnSupport (d := d) (ell := ell)) B w ∧
      ((Finset.univ : Finset (IntegerWitnessVertex w)).filter
         (fun v => v.1 ∈ T.1)).card =
          integerGraphAgeCanonical d ell B T ∧
      Fintype.card (IntegerWitnessVertex w) < ell ∧
      (∀ x ∈ (Finset.univ : Finset (IntegerWitnessVertex w)),
        ∀ y ∈ (Finset.univ : Finset (IntegerWitnessVertex w)),
          x ≠ y → integerWitnessCompleteEdge w x y = true) := by
  obtain ⟨w, hwB, hwMax⟩ :=
    integerGraphAgeCanonical_has_feasible_maximizer d ell hell B T
  refine ⟨w,hwB,?_,integerWitnessVertex_card_lt w hell,?_⟩
  · exact (integerWitnessVertex_support_eq_integerCliqueOnSupport w T).trans
      hwMax
  · exact integerWitnessCompleteEdge_clique w Finset.univ

/-- EVERY subclique of a B-feasible complete component respects the
entire raw-support upper-bound system, not merely the support at
which this component happened to maximize the canonical age. -/
theorem integerWitnessComponent_subclique_respects_raw
    {d ell : Nat} (B : IntegerGraphSupport d ell → Nat)
    (w : IntegerCliqueWeights d ell)
    (hw : WitnessRespects
      (integerCliqueOnSupport (d := d) (ell := ell)) B w)
    (s : Finset (IntegerWitnessVertex w))
    (T : IntegerGraphSupport d ell) :
    (s.filter (fun v => v.1 ∈ T.1)).card ≤ B T := by
  classical
  have hSub :
      s.filter (fun v => v.1 ∈ T.1) ⊆
        ((Finset.univ : Finset (IntegerWitnessVertex w)).filter
          (fun v => v.1 ∈ T.1)) := by
    intro v hv
    have ht := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩
  exact (Finset.card_le_card hSub).trans
    (integerWitnessVertex_respects_raw_bound B w hw T)

/-- For a genuine age F, the maximum labelled clique size supported
on T is attained by an actual abstract complete finite L-clique.
This is STILL not an extension over an arbitrary prescribed old graph. -/
theorem integerGraphAge_has_concrete_clique_attaining_support
    (d ell : Nat) (hell : 0 < ell)
    (F : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell F)
    (T : IntegerGraphSupport d ell) :
    ∃ w : IntegerCliqueWeights d ell,
      WitnessRespects
        (integerCliqueOnSupport (d := d) (ell := ell)) F w ∧
      ((Finset.univ : Finset (IntegerWitnessVertex w)).filter
          (fun v => v.1 ∈ T.1)).card = F T ∧
      Fintype.card (IntegerWitnessVertex w) < ell := by
  obtain ⟨w,hwB,hMax,hSmall,_⟩ :=
    integerGraphAgeCanonical_has_concrete_clique_maximizer
      d ell hell F T
  refine ⟨w,hwB,?_,hSmall⟩
  rw [integerGraphAgeCanonical_fixed_of_age d ell F hAge] at hMax
  exact hMax

#print axioms zeroIntegerCliqueWeight_respects
#print axioms feasibleIntegerCliqueVectors_nonempty
#print axioms integerGraphAgeCanonical_has_feasible_maximizer
#print axioms integerGraphAgeCanonical_has_concrete_clique_maximizer
#print axioms integerWitnessComponent_subclique_respects_raw
#print axioms integerGraphAge_has_concrete_clique_attaining_support

end Kk
