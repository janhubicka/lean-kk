import Kk.ExtensionProfileAge
import Mathlib.Tactic

/-!
# Conditional full-relative-profile interface for a corrected (B3) cut

English-first mathematical repair and hostile audit:
  docs/boring_level_relative_profiles_english_audit.md

We fix two GENUINE graph-age functions and arbitrary predicates on
normalized labelled clique vectors recording compatibility with the
complete old finite L+ source (including its auxiliary E/parameters).
The main substantive assumptions -- the exact fidelity of BOTH
relative predicates to their ages, and monotonicity on insertion --
are displayed rather than silently inferred from selected shadow data.

These lemmas do NOT establish either fidelity hypothesis, compare
complete L+ successor assignments of distinct source nodes, exclude
structural (I1)/(I2) levels, or construct the full corrected (B3)
witness loss equivalence in numerical H. They are a verified
conditional interface, not the full resolved-copy theorem.
-/

namespace Kk

/-- Equality of two genuine graph ages is exactly equality of the
entire relative continuation profiles, IF each relative profile is
faithfully represented by the corresponding joint support constraints.
The predicates may encode all required old L+ source/parameter data. -/
theorem integerGraphAge_eq_iff_faithful_relative_profiles
    (d ell : Nat)
    (Fbefore Fafter : IntegerGraphSupport d ell → Nat)
    (hBeforeAge : IsIntegerGraphAge d ell Fbefore)
    (hAfterAge : IsIntegerGraphAge d ell Fafter)
    (RelBefore RelAfter : IntegerCliqueWeights d ell → Prop)
    (hBefore : ∀ w, RelBefore w ↔
      WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell)) Fbefore w)
    (hAfter : ∀ w, RelAfter w ↔
      WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell)) Fafter w) :
    Fbefore = Fafter ↔ ∀ w, RelBefore w ↔ RelAfter w := by
  rw [integerGraphAge_eq_iff_same_feasible_vectors
    d ell Fbefore Fafter hBeforeAge hAfterAge]
  constructor
  · intro h w
    exact (hBefore w).trans ((h w).trans (hAfter w).symm)
  · intro h w
    exact (hBefore w).symm.trans ((h w).trans (hAfter w))

/-- If insertion cannot create newly permitted complete relative
continuations, the graph-age state changes precisely when some
NORMALIZED labelled clique was possible before but is no longer
possible afterward. Genuine fidelity remains a premise. -/
theorem integerGraphAge_ne_iff_lost_relative_witness
    (d ell : Nat)
    (Fbefore Fafter : IntegerGraphSupport d ell → Nat)
    (hBeforeAge : IsIntegerGraphAge d ell Fbefore)
    (hAfterAge : IsIntegerGraphAge d ell Fafter)
    (RelBefore RelAfter : IntegerCliqueWeights d ell → Prop)
    (hBefore : ∀ w, RelBefore w ↔
      WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell)) Fbefore w)
    (hAfter : ∀ w, RelAfter w ↔
      WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell)) Fafter w)
    (hShrink : ∀ w, RelAfter w → RelBefore w) :
    Fbefore ≠ Fafter ↔ ∃ w, RelBefore w ∧ ¬ RelAfter w := by
  classical
  have hEqual := integerGraphAge_eq_iff_faithful_relative_profiles
    d ell Fbefore Fafter hBeforeAge hAfterAge
    RelBefore RelAfter hBefore hAfter
  constructor
  · intro hNe
    by_contra hNo
    apply hNe
    apply hEqual.mpr
    intro w
    constructor
    · intro hAllowed
      by_contra hForbidden
      exact hNo ⟨w,hAllowed,hForbidden⟩
    · exact hShrink w
  · rintro ⟨w,hAllowed,hForbidden⟩ hEq
    have hProfile := hEqual.mp hEq w
    exact hForbidden (hProfile.mp hAllowed)

/-- Conditional equivalence between absence of corrected B3 failure
and equality of the two selected-front age states.

The input hB3 explicitly identifies ACTUAL full corrected-B3
failure with loss of one complete relative labelled clique witness.
This is NOT automatically true in numerical-H/Kpt: the recorded K4
auxiliary microevent defeats the naive selected-shadow projection.
Furthermore, no assertion of boringness follows if (I1) or (I2) is
structurally required; those exclusions are separate. -/
theorem faithful_relative_noB3_iff_age_eq
    (d ell : Nat)
    (Fbefore Fafter : IntegerGraphSupport d ell → Nat)
    (hBeforeAge : IsIntegerGraphAge d ell Fbefore)
    (hAfterAge : IsIntegerGraphAge d ell Fafter)
    (RelBefore RelAfter : IntegerCliqueWeights d ell → Prop)
    (hBefore : ∀ w, RelBefore w ↔
      WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell)) Fbefore w)
    (hAfter : ∀ w, RelAfter w ↔
      WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell)) Fafter w)
    (hShrink : ∀ w, RelAfter w → RelBefore w)
    (fullB3Fails : Prop)
    (hB3 : fullB3Fails ↔ ∃ w, RelBefore w ∧ ¬ RelAfter w) :
    ¬ fullB3Fails ↔ Fbefore = Fafter := by
  have hLoss := integerGraphAge_ne_iff_lost_relative_witness
    d ell Fbefore Fafter hBeforeAge hAfterAge
    RelBefore RelAfter hBefore hAfter hShrink
  constructor
  · intro hNoB3
    by_contra hNe
    exact hNoB3 (hB3.mpr (hLoss.mp hNe))
  · intro hEq hFailure
    exact (hLoss.mpr (hB3.mp hFailure)) hEq

#print axioms integerGraphAge_eq_iff_faithful_relative_profiles
#print axioms integerGraphAge_ne_iff_lost_relative_witness
#print axioms faithful_relative_noB3_iff_age_eq

end Kk
