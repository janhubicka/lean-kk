import Kk.FiniteOldColumnAge
import Kk.FiniteCliqueIntegerWitness
import Kk.PartialNumericLateAgeStability
import Kk.PartialNumericForbiddenSharpStability
import Mathlib.Tactic

/-!
# Track A: canonical integer graph ages are exact on all singleton raw supports

English FIRST, hostile audit and sharp canonical event construction:
  docs/track_a_singleton_canonical_sharpness_english_audit_20261120.md

For arbitrary actual finite old-to-future binary-L columns, canonicalizing
the raw clique-capacity continuation age does NOT change singleton bounds.
A one-sort normalized witness saturates each singleton while satisfying
all larger-support constraints. This is independent of Henson-freeness,
raw positivity, selected diaries, Kpt E/B3, or the global BRD claim.

Lean source and proof bodies are UNVERIFIED until an exact-head
lake build and strictly standard-only named axiom gate pass.
-/

namespace Kk

open SuccessorTree.V10

/-- A singleton original-column raw bound is canonically tight.
The original Boolean graph need not be symmetric or K_ell-free.
The raw singleton bound may even be zero. -/
theorem trackA_finite_old_column_canonical_singleton_eq_raw
    (E : Nat → Nat → Bool) (ell d : Nat)
    (hell : 2 ≤ ell)
    (P : Finset Nat) (c : Nat → Fin d → Bool)
    (t : Fin d) (T : IntegerGraphSupport d ell)
    (hT : T.1 = ({t} : Finset (Fin d))) :
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d P c) T =
    finiteOldColumnRawBound E ell d P c T := by
  classical
  let B := finiteOldColumnRawBound E ell d P c
  let r : Nat := B T
  have hrLe : r ≤ ell - 1 := by
    change ell - 1 - finiteDirectedCliqueCapacity E
      (oldSupportCommonNeighbourPool P c T.1) ≤ ell - 1
    omega
  have hrSmall : r < ell := by omega
  let s : Finset Nat := Finset.range r
  have hsSmall : s.card < ell := by
    simpa [s] using hrSmall
  let sort : Nat → Fin d := fun _ => t
  let w : IntegerCliqueWeights d ell :=
    integerCliqueWeightsOfFinset sort s hsSmall
  have hWeight (U : IntegerGraphSupport d ell) :
      integerCliqueOnSupport w U =
        if t ∈ U.1 then r else 0 := by
    rw [show integerCliqueOnSupport w U =
        (s.filter (fun v => sort v ∈ U.1)).card from
          integerCliqueOnSupport_of_finset sort s hsSmall U]
    by_cases htU : t ∈ U.1
    · simp [sort, s, htU]
    · simp [sort, s, htU]
  have hMonotone (U : IntegerGraphSupport d ell)
      (htU : t ∈ U.1) : r ≤ B U := by
    have hPool : oldSupportCommonNeighbourPool P c U.1 ⊆
        oldSupportCommonNeighbourPool P c T.1 := by
      intro x hx
      have hxFilter : x ∈ P.filter
          (fun p => ∀ u ∈ U.1, c p u = true) := by
        simpa [oldSupportCommonNeighbourPool] using hx
      have hxData := Finset.mem_filter.mp hxFilter
      have hxT : ∀ u ∈ T.1, c x u = true := by
        intro u hu
        have hut : u = t := by
          rw [hT] at hu
          simpa using hu
        subst u
        exact hxData.2 t htU
      change x ∈ P.filter (fun p => ∀ u ∈ T.1, c p u = true)
      exact Finset.mem_filter.mpr ⟨hxData.1, hxT⟩
    have hCap := finiteDirectedCliqueCapacity_mono E
      (oldSupportCommonNeighbourPool P c U.1)
      (oldSupportCommonNeighbourPool P c T.1) hPool
    change ell - 1 - finiteDirectedCliqueCapacity E
      (oldSupportCommonNeighbourPool P c T.1) ≤
        ell - 1 - finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool P c U.1)
    omega
  have hFeasible :
      WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell))
        B w := by
    intro U
    rw [hWeight U]
    by_cases htU : t ∈ U.1
    · simpa [htU] using (hMonotone U htU)
    · simp [htU]
  have htT : t ∈ T.1 := by
    rw [hT]
    simp
  have hSaturates : integerCliqueOnSupport w T = r := by
    rw [hWeight T]
    simp [htT]
  have hLower : r ≤ integerGraphAgeCanonical d ell B T := by
    rw [← hSaturates]
    exact witnessValue_le_canonical
      (integerCliqueOnSupport (d := d) (ell := ell))
      B w hFeasible T
  exact Nat.le_antisymm
    (integerGraphAgeCanonical_le_raw d ell B T)
    hLower

/-- Apply the singleton exactness theorem to the LITERAL complete
numbered numerical-H old prefix, including odd dummy coordinates
and the actual old-to-top crossing columns. No hypothetical source
shadow is used. -/
theorem trackA_physical_partial_canonical_singleton_eq_raw
    {d : Nat} (E : Nat → Nat → Bool)
    (ell : Nat) (hell : 2 ≤ ell)
    (k b g M : Nat) (j : Fin d → Nat)
    (t : Fin d) (T : IntegerGraphSupport d ell)
    (hT : T.1 = ({t} : Finset (Fin d))) :
    integerGraphAgeCanonical d ell
      (finiteNumericHPartialActualRawAt E ell k b g M j) T =
      finiteNumericHPartialActualRawAt E ell k b g M j T := by
  exact trackA_finite_old_column_canonical_singleton_eq_raw
    (fun x y => (finiteNumericHL
      (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
    ell d hell
    (Finset.range (hPosition k b g))
    (fun z t => (finiteNumericHL
      (normalizedGraphModel E) k M).binary
        z (hPosition k (j t) k) (0 : Fin 1))
    t T hT


/-- Exact CANONICAL singleton age drop at a genuine Henson numerical-H
partial-generation step: it happens precisely when the current original
is singleton-eligible and its linked common-old clique capacity equals
the full original capacity AND the current generation. This is an age
change, not an assertion that the age forms a COVER in the full poset. -/
theorem trackA_henson_partial_canonical_singleton_step_iff
    {d : Nat} (E : Nat → Nat → Bool)
    (ell : Nat) (hell : 2 ≤ ell)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (k b g M : Nat) (hg : g+1 ≤ k)
    (j : Fin d → Nat) (hj : ∀ u, b < j u)
    (t : Fin d) (T : IntegerGraphSupport d ell)
    (hT : T.1 = ({t} : Finset (Fin d))) :
    integerGraphAgeCanonical d ell
      (finiteNumericHPartialActualRawAt E ell k b (g+1) M j) T <
    integerGraphAgeCanonical d ell
      (finiteNumericHPartialActualRawAt E ell k b g M j) T ↔
    (∀ u ∈ T.1, E b (j u) = true) ∧
      finiteDirectedCliqueCapacity E
        ((oldSupportCommonNeighbourPool (Finset.range b)
          (fun i u => E i (j u)) T.1).filter
            (fun i => E i b = true)) =
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i u => E i (j u)) T.1) ∧
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i u => E i (j u)) T.1) = g := by
  rw [trackA_physical_partial_canonical_singleton_eq_raw
        E ell hell k b (g+1) M j t T hT,
      trackA_physical_partial_canonical_singleton_eq_raw
        E ell hell k b g M j t T hT]
  exact trackA_henson_partial_raw_single_step_iff
    E ell hell hAvoid k b g M hg j hj T

#print axioms Kk.trackA_henson_partial_canonical_singleton_step_iff
#print axioms Kk.trackA_finite_old_column_canonical_singleton_eq_raw
#print axioms Kk.trackA_physical_partial_canonical_singleton_eq_raw

end Kk
