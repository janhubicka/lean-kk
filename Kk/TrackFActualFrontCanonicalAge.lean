import Kk.FiniteOldColumnAgePositive
import Kk.TrackFMultiSortRawIsolation
import Mathlib.Tactic

/-!
# Track F: genuine physical one-type fronts have genuine canonical ages

The English proof and hostile audit were committed FIRST:
docs/track_f_actual_one_type_front_canonical_age_english_audit_20261121.md

For any true finite family of genuine HensonOneType nodes at the same
actual original-prefix level H, the full physical mixed common-old-
neighbour RAW bound is POSITIVE on every admissible nonempty support:
a selected sort's true old-neighbour safety bounds its actual common
old pool. Hence the integer-witness canonicalizer is a GENUINE
normalized graph age by the already verified constant-one age lower
bound and canonical-age theorem.

This validates the actual canonical-age hypothesis needed in the
algebraic zero-code preprofile rigidity (#430) when an intermediate
precode profile is read from true target Henson prefix types.
No full history-realization or diary/BRD claim is made.
-/

namespace Kk

/-- Every nonempty physical common-old-neighbour pool is contained
in each of its genuine source sort neighbourhoods. Since each
Henson one-type's old neighbour set is K_(ell-1)-free, the RAW
clique-capacity bound on EVERY nonempty support is at least 1.

This includes every mixed pair/triple support, and works when d=0
(vacuously). No source/target embedding, age hypothesis or actual
coding-fibre largeness is assumed. -/
theorem trackFActualFront_raw_positive
    (d ell H : Nat)
    (E : Nat → Nat → Bool)
    (u : Fin d → HensonOneType ell E)
    (_hLevel : ∀ i, (u i).level = H) :
    ∀ T : IntegerGraphSupport d ell,
      1 ≤ trackFCommonRawAge d ell H E
        (fun i => (u i).neighbours) T.1 := by
  classical
  intro T
  obtain ⟨i, hi⟩ := T.2.1
  have hCommonSub :
      trackFCommonNeighbourPool d H
        (fun j => (u j).neighbours) T.1 ⊆
      (u i).neighbours := by
    intro x hx
    have hxPool :
        x ∈ (Finset.range H).filter
          (fun a => ∀ j ∈ T.1, a ∈ (u j).neighbours) := hx
    exact (Finset.mem_filter.mp hxPool).2 i hi
  have hCapMono :=
    finiteDirectedCliqueCapacity_mono E
      (trackFCommonNeighbourPool d H
        (fun j => (u j).neighbours) T.1)
      (u i).neighbours hCommonSub
  have hSafe :
      finiteDirectedCliqueCapacity E (u i).neighbours < ell - 1 :=
    (finitePoolCliqueCheck_false_iff_capacity_lt
      E (ell - 1) (u i).neighbours).mp (u i).safe
  change 1 ≤ ell - 1 -
    finiteDirectedCliqueCapacity E
      (trackFCommonNeighbourPool d H
        (fun j => (u j).neighbours) T.1)
  omega

/-- The COMPLETE canonical integer-witness age of any actual tuple
of genuine same-level Henson one-types is itself a genuine normalized
integer graph age, even though its RAW capacity table need not be
canonical. The target is the full support system, not a selected shadow.

In particular this gives the true-age premise of the verified
zero-code mixed preprofile rigidity once the actual immediate
pre-code target prefix tuple has been constructed. -/
theorem trackFActualFront_canonical_is_integer_graph_age
    (d ell H : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (u : Fin d → HensonOneType ell E)
    (hLevel : ∀ i, (u i).level = H) :
    IsIntegerGraphAge d ell
      (integerGraphAgeCanonical d ell
        (fun T : IntegerGraphSupport d ell =>
          trackFCommonRawAge d ell H E
            (fun i => (u i).neighbours) T.1)) := by
  apply integerGraphAgeCanonical_is_age d ell
    (fun T : IntegerGraphSupport d ell =>
      trackFCommonRawAge d ell H E
        (fun i => (u i).neighbours) T.1)
    (fun _ => 1)
  · exact integerGraphAge_const_one_is_age d ell hell
  · intro T
    exact trackFActualFront_raw_positive d ell H E u hLevel T

end Kk
