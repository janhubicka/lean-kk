import Kk.TrackFCompleteNatWitnessNumericAge
import Kk.TrackFK4CompleteTupleSynchronization
import Kk.TrackFZeroCodeSurvivorSynchronization
import Kk.TrackFPrecodeEndpointAgeSandwich
import Mathlib.Tactic

/-!
# Track F: genuine source/target synchronizations have equal NUMERIC ages

English mathematical proof and 16 hostile scope checks were written
FIRST in docs/track_f_physical_numeric_endpoint_from_classes_english_audit_20261122.md.

The complete Nat-clique witness encoding of Track F numeric-age
extraction, combined with genuine safe-front age consistency, turns
UNIVERSAL finite sorted K4 graph-class equivalence into EXACT numeric
equality of the full canonical integer age functions, including all
mixed/triple supports.

The verified full K4 synchronization (#410) and actual zero-code
survivor synchronization (#433) construct common-level target fronts
with exactly the required class equivalence for EVERY B and σ.
Thus both yield genuine numeric source-versus-target age equality,
without claiming equality of redundant raw tables.

This is still a COMPONENT of a code event. The old/later survivor
label matching and legal code zero-branch history require further
application. No full diary or BRD lower theorem is asserted.
-/

namespace Kk

/-- Universal all-finite-symmetric-K4 graph-class equality between
two ACTUAL safe common-level Henson sorted fronts implies the
complete NUMERIC equality of their true canonical integer ages.

Every actual front age is genuine by the checked safe-singleton
positivity theorem. No equality of redundant raw support values is
assumed or deduced; every mixed/triple canonical value is recovered
from normalized finite labelled clique witnesses. -/
theorem trackFPhysical_numeric_age_eq_of_full_K4_tests
    (d m H : Nat)
    (Esrc Etgt : Nat → Nat → Bool)
    (u : Fin d → HensonOneType 4 Esrc)
    (v : Fin d → HensonOneType 4 Etgt)
    (huLevel : ∀ i, (u i).level = m)
    (hvLevel : ∀ i, (v i).level = H)
    (hTests : ∀ N : Nat, ∀ B : Nat → Nat → Bool,
      ∀ σ : Nat → Fin d,
        (∀ i j, B i j = B j i) →
        finitePoolCliqueCheck B 4 (Finset.range N) = false →
        (k4CanonicalSortedFiniteTest d m N Esrc B u σ ↔
         k4CanonicalSortedFiniteTest d H N Etgt B v σ)) :
    trackFPhysicalFrontCanonicalAge d 4 m Esrc u =
      trackFPhysicalFrontCanonicalAge d 4 H Etgt v := by
  have hUage :
      IsIntegerGraphAge d 4
        (trackFPhysicalFrontCanonicalAge d 4 m Esrc u) :=
    trackFActualFront_canonical_is_integer_graph_age
      d 4 m (by decide) Esrc u huLevel
  have hVage :
      IsIntegerGraphAge d 4
        (trackFPhysicalFrontCanonicalAge d 4 H Etgt v) :=
    trackFActualFront_canonical_is_integer_graph_age
      d 4 H (by decide) Etgt v hvLevel
  apply trackF_numeric_integer_age_eq_of_all_finite_K4_tests
    d _ _ hUage hVage
  intro N B σ hSym hFree
  exact hTests N B σ hSym hFree

/-- The verified ACTUAL K4 simultaneous compatible-front construction
now also gives a pairwise-independent NUMERIC age equality endpoint.
The same target fronts are chosen before quantifying over finite B.

The output retains common levels, target type injectivity and
source-to-target actual rank-large coding fibre compatibility, but
does not assert diary history occurrence or target raw-table equality. -/
theorem k4_sync_complete_tuple_numeric_canonical_age
    (d m cutoff : Nat)
    (Esrc Etgt : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily 4 (by decide) →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (u : Fin d → HensonOneType 4 Esrc)
    (v : Fin d → HensonOneType 4 Etgt)
    (huLevel : ∀ i, (u i).level = m)
    (huInj : Function.Injective u)
    (hRank : ∀ i, HensonOneType.rank (v i) =
      HensonOneType.rank (u i))
    (hLarge : ∀ i,
      RankLargeness.Large HensonOneType.rank
        (HensonOneType.sourceCodingFibre (E := Esrc) Etgt e (v i))
        (HensonOneType.rank (u i)) (u i)) :
    ∃ H M : Nat,
    ∃ uNew : Fin d → HensonOneType 4 Esrc,
    ∃ vNew : Fin d → HensonOneType 4 Etgt,
      cutoff ≤ H ∧
      (∀ i, (uNew i).level = M ∧ u i ≤ uNew i) ∧
      (∀ i, (vNew i).level = H ∧
        HensonOneType.rank (vNew i) = HensonOneType.rank (u i) ∧
        RankLargeness.Large HensonOneType.rank
          (HensonOneType.sourceCodingFibre (E := Esrc) Etgt e (vNew i))
          (HensonOneType.rank (uNew i)) (uNew i)) ∧
      Function.Injective vNew ∧
      trackFPhysicalFrontCanonicalAge d 4 m Esrc u =
        trackFPhysicalFrontCanonicalAge d 4 H Etgt vNew := by
  classical
  obtain ⟨H, M, uNew, vNew, hCut, hU, hV,
    hVinj, _hPrivate, _hRaw, hTests⟩ :=
    k4_sync_complete_tuple_canonical_class
      d m cutoff Esrc Etgt hAvoid e he hInduced
      u v huLevel huInj hRank hLarge
  have hvLevel : ∀ i, (vNew i).level = H :=
    fun i => (hV i).2.1
  have hAgeEq :=
    trackFPhysical_numeric_age_eq_of_full_K4_tests
      d m H Esrc Etgt u vNew huLevel hvLevel hTests
  refine ⟨H, M, uNew, vNew, hCut, ?_, ?_, hVinj, hAgeEq⟩
  · intro i
    exact ⟨(hU i).1, (hU i).2.1⟩
  · intro i
    exact ⟨hvLevel i, (hV i).2.2.1,
      (hV i).2.2.2⟩

/-- The ACTUAL K4 survivor resynchronization after an already
selected independent source original r also produces NUMERIC
equality of the original source survivor age and the later target
survivor age, on EVERY admissible nonempty support.

This is the new exact ENDPOINT equality ingredient for the
pre-code age sandwich. It does not automatically match the full
old target tuple's survivor sort order, which is a separate
deletion/reindexing step in the actual history proof. -/
theorem k4_survivor_sync_numeric_canonical_age_after_code
    (d m r cutoff : Nat) (hmR : m ≤ r)
    (Esrc Etgt : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily 4 (by decide) →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (u : Fin d → HensonOneType 4 Esrc)
    (v : Fin d → HensonOneType 4 Etgt)
    (huLevel : ∀ i, (u i).level = m)
    (huInj : Function.Injective u)
    (hRank : ∀ i, HensonOneType.rank (v i) =
      HensonOneType.rank (u i))
    (hLarge : ∀ i,
      RankLargeness.Large HensonOneType.rank
        (HensonOneType.sourceCodingFibre (E := Esrc) Etgt e (v i))
        (HensonOneType.rank (u i)) (u i)) :
    ∃ H M : Nat,
    ∃ uNew : Fin d → HensonOneType 4 Esrc,
    ∃ vNew : Fin d → HensonOneType 4 Etgt,
      cutoff < H ∧ e r < H ∧
      (∀ i, (vNew i).level = H ∧
        e r ∉ (vNew i).neighbours ∧
        RankLargeness.Large HensonOneType.rank
          (HensonOneType.sourceCodingFibre (E := Esrc) Etgt e (vNew i))
          (HensonOneType.rank (uNew i)) (uNew i)) ∧
      Function.Injective vNew ∧
      trackFPhysicalFrontCanonicalAge d 4 m Esrc u =
        trackFPhysicalFrontCanonicalAge d 4 H Etgt vNew := by
  classical
  obtain ⟨H, M, uNew, vNew, hCut, hrCut,
    _hU, hV, hInj, _hRaw, hTests⟩ :=
    k4_survivor_sync_after_zero_code
      d m r cutoff hmR Esrc Etgt hAvoid e he hInduced
      u v huLevel huInj hRank hLarge
  have hvLevel : ∀ i, (vNew i).level = H :=
    fun i => (hV i).2.1
  have hAgeEq :=
    trackFPhysical_numeric_age_eq_of_full_K4_tests
      d m H Esrc Etgt u vNew huLevel hvLevel hTests
  refine ⟨H, M, uNew, vNew, hCut, hrCut, ?_, hInj, hAgeEq⟩
  intro i
  exact ⟨hvLevel i, (hV i).2.2.2.2,
    (hV i).2.2.2.1⟩

end Kk
