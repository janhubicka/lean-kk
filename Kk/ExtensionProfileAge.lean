import Kk.IntegerAgeUniversalProperties
import Mathlib.Tactic

/-!
# Exact abstract extension profile of a genuine integer graph age

The English proof and adversarial repair were committed FIRST:
  docs/extension_profile_vs_relative_realisation_english_audit.md

A genuine graph-age F is recovered exactly as the finite supremum of
the support multiplicities of its permitted normalized labelled clique
vectors. Therefore the FULL feasible-vector profile determines F.
More generally equal feasible-vector systems give equal canonicalized
raw bounds, but NOT necessarily equal raw bounds.

IMPORTANT: these are abstract finite sorted clique patterns; the
theorems do NOT assert that all such patterns can be realized over an
arbitrary fixed Henson prefix with separately prescribed old-to-future
L columns, or that auxiliary Kpt E/parameter records agree. That
relative-realization obligation belongs to the resolved-copy proof.
-/

namespace Kk

/-- All normalized integer clique vectors feasible for the complete
family of raw support bounds. The filter tests EVERY support, not
just one coordinate. -/
noncomputable def feasibleIntegerCliqueVectors (d ell : Nat)
    (F : IntegerGraphSupport d ell → Nat) :
    Finset (IntegerCliqueWeights d ell) := by
  classical
  exact Finset.univ.filter
    (WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell)) F)

/-- Precise extension-profile lemma: for a genuine integer graph age,
the maximum multiplicity on EVERY admissible support T among all
feasible normalized labelled cliques equals exactly F(T).
No fixed-ambient relative Henson realization is assumed. -/
theorem integerGraphAge_eq_sup_feasible_vectors
    (d ell : Nat) (F : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell F)
    (T : IntegerGraphSupport d ell) :
    F T = (feasibleIntegerCliqueVectors d ell F).sup
      (fun w => integerCliqueOnSupport w T) := by
  classical
  have hFixed := integerGraphAgeCanonical_fixed_of_age d ell F hAge
  have hAt := congrArg (fun f : IntegerGraphSupport d ell → Nat => f T) hFixed
  exact hAt.symm

/-- For arbitrary raw bounds, equality of the FULL sets of permitted
normalized clique vectors implies equality of their canonicalizations.
It need not imply equality of the original non-canonical raw bounds. -/
theorem integerGraphAgeCanonical_eq_of_same_feasible_vectors
    (d ell : Nat)
    (B C : IntegerGraphSupport d ell → Nat)
    (hSame : ∀ w : IntegerCliqueWeights d ell,
      WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell)) B w ↔
      WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell)) C w) :
    integerGraphAgeCanonical d ell B = integerGraphAgeCanonical d ell C := by
  classical
  have hSets :
      (Finset.univ.filter (WitnessRespects
          (integerCliqueOnSupport (d := d) (ell := ell)) B)) =
        (Finset.univ.filter (WitnessRespects
          (integerCliqueOnSupport (d := d) (ell := ell)) C)) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hSame w
  funext T
  exact congrArg (fun s : Finset (IntegerCliqueWeights d ell) =>
    s.sup (fun w => integerCliqueOnSupport w T)) hSets

/-- Two genuine graph ages with precisely the same feasible full
labelled clique patterns have exactly the same graph-age function. -/
theorem integerGraphAge_eq_of_same_feasible_vectors
    (d ell : Nat)
    (F G : IntegerGraphSupport d ell → Nat)
    (hF : IsIntegerGraphAge d ell F)
    (hG : IsIntegerGraphAge d ell G)
    (hSame : ∀ w : IntegerCliqueWeights d ell,
      WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell)) F w ↔
      WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell)) G w) :
    F = G := by
  calc
    F = integerGraphAgeCanonical d ell F :=
      (integerGraphAgeCanonical_fixed_of_age d ell F hF).symm
    _ = integerGraphAgeCanonical d ell G :=
      integerGraphAgeCanonical_eq_of_same_feasible_vectors d ell F G hSame
    _ = G := integerGraphAgeCanonical_fixed_of_age d ell G hG

/-- Complete abstract characterization by feasible normalized labelled
cliques. No claim that a fixed physical continuation W is universal. -/
theorem integerGraphAge_eq_iff_same_feasible_vectors
    (d ell : Nat)
    (F G : IntegerGraphSupport d ell → Nat)
    (hF : IsIntegerGraphAge d ell F)
    (hG : IsIntegerGraphAge d ell G) :
    F = G ↔
      ∀ w : IntegerCliqueWeights d ell,
        WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell)) F w ↔
        WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell)) G w := by
  constructor
  · intro hEq w
    subst G
    exact Iff.rfl
  · exact integerGraphAge_eq_of_same_feasible_vectors d ell F G hF hG

#print axioms integerGraphAge_eq_sup_feasible_vectors
#print axioms integerGraphAgeCanonical_eq_of_same_feasible_vectors
#print axioms integerGraphAge_eq_of_same_feasible_vectors
#print axioms integerGraphAge_eq_iff_same_feasible_vectors

end Kk
