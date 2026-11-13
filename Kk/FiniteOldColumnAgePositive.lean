import Kk.FiniteOldColumnAge
import Kk.FiniteCliqueIntegerWitness
import Mathlib.Tactic

/-!
# Track A: safe singleton columns make the finite old reference canonical age genuine

English proof and hostile audit committed FIRST:
  docs/finite_old_column_positive_age_english_audit.md

The old-column raw bounds B_P(T)=ell-1-cap(common-neighbourhood(P,T))
may be zero; in that case the canonicalizer is NOT automatically a
genuine positive (D,ell) graph-age function. Under the exact
negative K_(ell-1) certificate for EVERY marked singleton sort,
the common-neighbour capacity of every nonempty support is below
ell-1. The raw bounds then dominate the genuine constant-one
integer age, so the existing canonicalizer theorem proves that
G_(B_P) is a genuine integer graph age.

This is a finite ordinary L statement, not actual recursive
one-point existence, auxiliary Kpt E/B3 or a labelled source orbit.
-/

namespace Kk

/-- The constant-one age is a genuine normalized integer witness age
for ell >= 2. A support witness is a one-vertex labelled clique on
any sort belonging to the nonempty support. When d=0 the condition
is vacuous, and the proof does not fabricate a sort of Fin 0. -/
theorem integerGraphAge_const_one_is_age
    (d ell : Nat) (hell : 2 ≤ ell) :
    IsIntegerGraphAge d ell (fun _ => 1) := by
  classical
  constructor
  · intro T
    change 1 ≤ (1 : Nat) ∧ (1 : Nat) ≤ ell - 1
    omega
  · intro T
    obtain ⟨t, ht⟩ := T.2.1
    let sort : Nat → Fin d := fun _ => t
    let s : Finset Nat := {0}
    have hSize : s.card < ell := by
      simp [s]
      omega
    let w : IntegerCliqueWeights d ell :=
      integerCliqueWeightsOfFinset sort s hSize
    refine ⟨w, ?_, ?_⟩
    · intro U
      change integerCliqueOnSupport w U ≤ 1
      rw [show integerCliqueOnSupport w U =
          (s.filter (fun v => sort v ∈ U.1)).card from
        integerCliqueOnSupport_of_finset sort s hSize U]
      have hSub : s.filter (fun v => sort v ∈ U.1) ⊆ s :=
        Finset.filter_subset _ _
      have hCard := Finset.card_le_card hSub
      simpa [s] using hCard
    · change integerCliqueOnSupport w T = 1
      rw [show integerCliqueOnSupport w T =
          (s.filter (fun v => sort v ∈ T.1)).card from
        integerCliqueOnSupport_of_finset sort s hSize T]
      simp [s, sort, ht]

/-- Complete one-point negative clique certificates for EACH marked
sort ensure the old-column raw bound is positive on EVERY nonempty
support simultaneously, not merely on a selected shadow.

No global symmetry, old K-freeness, or physical schedule is required
for this purely monotone capacity estimate. -/
theorem finiteOldColumnRawBound_positive_of_singleton_safe
    (E : Nat → Nat → Bool) (ell d : Nat)
    (P : Finset Nat) (c : Nat → Fin d → Bool)
    (hSingleton : ∀ t : Fin d,
      finiteDirectedCliqueCapacity E
        (P.filter (fun p => c p t = true)) < ell - 1) :
    ∀ T : IntegerGraphSupport d ell,
      1 ≤ finiteOldColumnRawBound E ell d P c T := by
  classical
  intro T
  obtain ⟨t, ht⟩ := T.2.1
  have hSub :
      oldSupportCommonNeighbourPool P c T.1 ⊆
        P.filter (fun p => c p t = true) := by
    intro p hp
    have hMem : p ∈ P ∧ ∀ u ∈ T.1, c p u = true := by
      simpa [oldSupportCommonNeighbourPool] using hp
    exact Finset.mem_filter.mpr ⟨hMem.1, hMem.2 t ht⟩
  have hCap := finiteDirectedCliqueCapacity_mono E
    (oldSupportCommonNeighbourPool P c T.1)
    (P.filter (fun p => c p t = true)) hSub
  have hLess := hSingleton t
  change 1 ≤ ell - 1 -
    finiteDirectedCliqueCapacity E
      (oldSupportCommonNeighbourPool P c T.1)
  omega

/-- The exact physical finite-old-column canonical bound is a
GENUINE (D,ell) integer graph age once every marked singleton
type passes its complete old-neighbour K_(ell-1)-free certificate.

The result follows by exhibiting the constant-one age below the raw
bounds and invoking the previously verified greatest-age
canonicalizer. The raw function itself need not be an age. -/
theorem finiteOldColumnCanonical_is_age_of_singleton_safe
    (E : Nat → Nat → Bool) (ell d : Nat) (hell : 2 ≤ ell)
    (P : Finset Nat) (c : Nat → Fin d → Bool)
    (hSingleton : ∀ t : Fin d,
      finiteDirectedCliqueCapacity E
        (P.filter (fun p => c p t = true)) < ell - 1) :
    IsIntegerGraphAge d ell
      (integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d P c)) := by
  apply integerGraphAgeCanonical_is_age d ell
    (finiteOldColumnRawBound E ell d P c) (fun _ => 1)
  · exact integerGraphAge_const_one_is_age d ell hell
  · intro T
    exact finiteOldColumnRawBound_positive_of_singleton_safe
      E ell d P c hSingleton T

#print axioms Kk.integerGraphAge_const_one_is_age
#print axioms Kk.finiteOldColumnRawBound_positive_of_singleton_safe
#print axioms Kk.finiteOldColumnCanonical_is_age_of_singleton_safe

end Kk
