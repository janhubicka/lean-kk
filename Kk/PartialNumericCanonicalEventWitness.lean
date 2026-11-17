import Kk.PartialNumericRawSupportEvents
import Kk.PartialNumericAgeMonotonicity
import Kk.IntegerAgeUniversalProperties
import Mathlib.Tactic

/-!
# Track A: a canonical physical old-age change has a raw U-event witness

The English proof and hostile audit were committed BEFORE Lean:
  docs/partial_numeric_canonical_change_witness_english_audit.md

For the SAME E, height, current original b, finite Boolean carrier
and GIVEN later top-original family j, any difference of the
canonically normalized integer graph ages at two partial numerical-H
cuts g<=h<=k requires one NONEMPTY admissible support U witnessing
a strict actual RAW age decrease. The verified physical raw-event
iff then identifies b U-eligibility, c_U=p_U, the unique threshold
g<=p_U<h, and the non-saturation condition p_U<ell-1.

This is NECESSARY only, not sufficient: a raw U-event can be
redundant in the canonical integer age, and neither age difference
nor its raw certificate classifies full parameter-closed Kpt E/B3
or resolves a common labelled diary source.
-/

namespace Kk

open SuccessorTree.V10

/-- The TRUE physical raw old age against later TOP original names
for a literal numbered partial original-block cut. This is an
abbreviation only: all numbered old vertices and actual binary-L
crossing columns are present in the two inputs. -/
noncomputable def finiteNumericHPhysicalPartialOldRaw
    {d : Nat} (E : Nat → Nat → Bool)
    (ell k b g M : Nat) (j : Fin d → Nat) :
    IntegerGraphSupport d ell → Nat :=
  finiteOldColumnRawBound
    (fun x y => (finiteNumericHL
      (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
    ell d (Finset.range (hPosition k b g))
    (fun z t => (finiteNumericHL
      (normalizedGraphModel E) k M).binary
        z (hPosition k (j t) k) (0 : Fin 1))

/-- If the ACTUAL canonical integer graph ages differ between
physical cuts g<=h<=k, at least one nonempty support U must
witness the raw transition. The exact numerical-H raw event
iff identifies an eligible current b, an original linked
maximum clique, a straddled generation threshold, and a
strictly unsaturated raw bound.

No converse canonical-cover assertion is made. -/
theorem finiteNumericH_partial_canonical_change_has_raw_certificate
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (ell k b g h M : Nat) (hgh : g ≤ h) (hh : h ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t)
    (hDifferent :
      integerGraphAgeCanonical d ell
        (finiteNumericHPhysicalPartialOldRaw E ell k b h M j) ≠
      integerGraphAgeCanonical d ell
        (finiteNumericHPhysicalPartialOldRaw E ell k b g M j)) :
    ∃ U : IntegerGraphSupport d ell,
      (∀ t ∈ U.1, E b (j t) = true) ∧
      finiteDirectedCliqueCapacity E
        ((oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1).filter
          (fun i => E i b = true)) =
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1) ∧
      g ≤ finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1) ∧
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1) < h ∧
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1) < ell-1 := by
  classical
  by_contra hNoCertificate
  have hRawEq :
      finiteNumericHPhysicalPartialOldRaw E ell k b h M j =
        finiteNumericHPhysicalPartialOldRaw E ell k b g M j := by
    funext U
    have hMono :
        finiteNumericHPhysicalPartialOldRaw E ell k b h M j U ≤
          finiteNumericHPhysicalPartialOldRaw E ell k b g M j U :=
      finiteNumericH_partial_actual_raw_age_antitone
        E ell k b M g h hgh j U
    have hNotStrict :
        ¬ finiteNumericHPhysicalPartialOldRaw E ell k b h M j U <
          finiteNumericHPhysicalPartialOldRaw E ell k b g M j U := by
      intro hStrict
      have hCriterion :=
        (finiteNumericH_partial_actual_raw_support_event_iff
          E hSym ell k b g h M hgh hh j hj U).mp hStrict
      exact hNoCertificate ⟨U,hCriterion⟩
    omega
  exact hDifferent
    (congrArg (integerGraphAgeCanonical d ell) hRawEq)

#print axioms Kk.finiteNumericH_partial_canonical_change_has_raw_certificate

end Kk
