import Kk.CriticalNeutralPhysicalCover
import Mathlib.Tactic

/-!
# Track B: TWO consecutive genuine physical Henson canonical cover stages

English mathematical proof and hostile scope audit were committed first:
docs/track_b_two_physical_covers_english_audit.md

Under two genuine successive integer-witness graph-age covers in the
SAME fixed d-dimensional future-sort system, the already kernel-checked
one-stage Henson construction can be applied twice in ONE unchanged
original graph E. The first physical resulting complete old canonical
age is exactly the second stage's hPrior — it is DERIVED, not assumed.

The result includes both real reserved original clique blocks, their
physical positions, actual between-block NONEDGES IN BOTH DIRECTIONS,
complete gap-inclusive future columns and two stage-by-stage canonical
age identities, with a genuine numerical-H uniform top stage each time.

It is finite and conditional. It does NOT produce the unbounded diary,
simultaneous coherent selected-front copies, dependent auxiliary Kpt
L+ microevents or a common labelled inverse source orbit.
-/

namespace Kk

/-- Two consecutive physical canonical age covers can be realized
in the SAME fixed left-dense normalized Henson original graph.

The updated complete old column after the first stage is passed
literally into the second. Consequently the second hPrior is the
derived first physical canonical-age identity, not a new premise.
All new/old and inter-block nonedges are true physical E atoms. -/
theorem henson_leftDense_exists_two_physical_canonical_cover_stages
    (d ell b k0 k1 r0 r1 : Nat)
    (hell : 2 ≤ ell) (hd : 0 < d)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool)
    (T0 T1 : IntegerGraphSupport d ell)
    (lower middle upper : IntegerGraphSupport d ell → Nat)
    (hCover0 : AgeCover (IsIntegerGraphAge d ell) middle upper)
    (hCover1 : AgeCover (IsIntegerGraphAge d ell) lower middle)
    (hEll0 : ell = middle T0 + r0 + 1)
    (hAt0 : upper T0 = middle T0 + 1)
    (hEll1 : ell = lower T1 + r1 + 1)
    (hAt1 : middle T1 = lower T1 + 1)
    (hPrior : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) = upper) :
    ∃ (Q0 : Finset Nat) (F0 : Nat) (Q1 : Finset Nat) (F1 : Nat),
      Q0.card = r0 ∧
      (∀ q ∈ Q0, b ≤ q ∧ q < F0) ∧
      Q1.card = r1 ∧
      (∀ q ∈ Q1, F0 ≤ q ∧ q < F1) ∧
      IsDirectedCliqueOn E Q0 ∧
      IsDirectedCliqueOn E Q1 ∧
      (∀ q0 ∈ Q0, ∀ q1 ∈ Q1,
        E q0 q1 = false ∧ E q1 q0 = false) ∧
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range F0)
          (supportBlockGappedColumn b Q0 T0.1 c)) = middle ∧
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range F1)
          (supportBlockGappedColumn F0 Q1 T1.1
            (supportBlockGappedColumn b Q0 T0.1 c))) = lower ∧
      HasUniformPositiveSupportStage E d ell b F0 k0 hd c Q0 T0 ∧
      HasUniformPositiveSupportStage E d ell F0 F1 k1 hd
        (supportBlockGappedColumn b Q0 T0.1 c) Q1 T1 := by
  classical
  obtain ⟨Q0, F0, h0card, h0within, h0clique, _h0iso,
      h0age, _h0feasible, h0stage⟩ :=
    henson_leftDense_exists_physical_finite_canonical_cover_stage
      d ell b k0 r0 hell hd E hAvoid hDense c T0
      middle upper hCover0 hEll0 hAt0 hPrior
  obtain ⟨Q1, F1, h1card, h1within, h1clique, h1iso,
      h1age, _h1feasible, h1stage⟩ :=
    henson_leftDense_exists_physical_finite_canonical_cover_stage
      d ell F0 k1 r1 hell hd E hAvoid hDense
      (supportBlockGappedColumn b Q0 T0.1 c) T1
      lower middle hCover1 hEll1 hAt1 h0age
  refine ⟨Q0, F0, Q1, F1, h0card, h0within, h1card,
    h1within, h0clique, h1clique, ?_, h0age, h1age,
    h0stage, h1stage⟩
  intro q0 hq0 q1 hq1
  exact h1iso q0 (h0within q0 hq0).2 q1 hq1

#print axioms Kk.henson_leftDense_exists_two_physical_canonical_cover_stages

end Kk
