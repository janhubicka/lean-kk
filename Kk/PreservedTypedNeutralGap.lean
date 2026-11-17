import Kk.ZeroTailPhysicalCoverSpacing
import Kk.CriticalNeutralPhysicalCover
import Mathlib.Tactic

/-!
# Track B: a second physical cover AFTER an unmodified typed neutral interval

English mathematical proof and ten hostile scope checks were committed
BEFORE this Lean file in
docs/track_b_preserved_typed_gap_and_dedup_english_audit.md.

The previously verified finite two-cover theorem can place its second
physical reserved clique immediately after the first cutoff. Arbitrarily
postponing it with \`oldColumnZeroTail\` is safe for the old-age equation,
but can erase passing bits needed by previously realized selected future
witnesses. This file isolates the strictly stronger conditional bridge:

* the ENTIRE full typed column is held unchanged through the gap;
* the actual critical-original count is ZERO on every nonempty support;
* one real second Henson cover can then be made after any designated
  finite set of old original vertices W0;
* the resulting complete updated column agrees at EVERY old vertex
  and EVERY sort, including W0, and Q1 is physically nonadjacent to W0;
* a given first genuine finite uniform stage remains a valid statement
  about exactly the same first original graph, cutoff and column.

The hypothesis of ZERO critical counts is NOT generated here, need not
hold for the actual images of the first top witnesses, and is stronger
than mere equality of canonical old ages. This does NOT prove a global
resolved diary, a joint selected-front embedding, full dependent Kpt
L+ source coherence, or a common labelled inverse source orbit.
-/

namespace Kk

/-- A new gapped support block placed at or above the genuine cut N
preserves the COMPLETE old-to-future column at every original p < N.
The identity is literal and works even if c has positive bits there.
It depends only on the stage positions, not on clique freeness. -/
theorem supportBlockGappedColumn_eq_before_cut
    {d : Nat} (N : Nat) (Q : Finset Nat)
    (T : Finset (Fin d)) (c : Nat → Fin d → Bool)
    (hQAfter : ∀ q ∈ Q, N ≤ q)
    (p : Nat) (hp : p < N) (t : Fin d) :
    supportBlockGappedColumn N Q T c p t = c p t := by
  classical
  have hNotQ : p ∉ Q := by
    intro hpQ
    have hpAfter := hQAfter p hpQ
    omega
  simp [supportBlockGappedColumn, supportBlockOldColumn,
    delayedOldColumn, hp, hNotQ]

/-- True full old common-neighbour pools depend only on typed columns below N. -/
theorem oldSupportCommonNeighbourPool_eq_of_column_prefix
    {d : Nat} (N : Nat)
    (c cNext : Nat → Fin d → Bool)
    (hSame : ∀ p, p < N → ∀ t, c p t = cNext p t)
    (U : Finset (Fin d)) :
    oldSupportCommonNeighbourPool (Finset.range N) c U =
      oldSupportCommonNeighbourPool (Finset.range N) cNext U := by
  classical
  ext p
  change
    (p ∈ (Finset.range N).filter
      (fun q => ∀ t ∈ U, c q t = true)) ↔
    (p ∈ (Finset.range N).filter
      (fun q => ∀ t ∈ U, cNext q t = true))
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hp, hAll⟩
    refine ⟨hp, ?_⟩
    intro t ht
    rw [← hSame p hp t]
    exact hAll t ht
  · rintro ⟨hp, hAll⟩
    refine ⟨hp, ?_⟩
    intro t ht
    rw [hSame p hp t]
    exact hAll t ht

/-- Full raw and canonical ages depend only on the complete typed
column on the actual original prefix, not later extensions. -/
theorem integerGraphAgeCanonical_eq_of_column_prefix
    (E : Nat → Nat → Bool) (ell d N : Nat)
    (c cNext : Nat → Fin d → Bool)
    (hSame : ∀ p, p < N → ∀ t, c p t = cNext p t) :
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range N) c) =
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range N) cNext) := by
  have hRaw :
      finiteOldColumnRawBound E ell d (Finset.range N) c =
      finiteOldColumnRawBound E ell d (Finset.range N) cNext := by
    funext U
    change ell - 1 -
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range N) c U.1) =
      ell - 1 -
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range N) cNext U.1)
    rw [oldSupportCommonNeighbourPool_eq_of_column_prefix
      N c cNext hSame U.1]
  rw [hRaw]

/-- Conditional finite passage from a GENUINE first positive-support
stage to one later physical canonical-age cover without resetting
the old typed future column to zero.

W0 is ANY FINITE SET OF ACTUAL ORIGINAL INDICES known to lie below
the later cutoff F0+m. A caller may instantiate it as the true
physical images of first-stage top witnesses; this theorem does NOT
derive that identification or the crucial all-support neutrality
certificate for such a set.

All first-stage original E facts are kept; the second reserved clique
Q1 is physically negative to all original indices below the later
cut, and the new full future column is literally unchanged on W0.
The complete canonical age at the later cut is DERIVED from the
unmodified c1 and zero actual critical counts, not independently
postulated or obtained by zero-tail rewriting. -/
theorem henson_leftDense_second_cover_after_preserved_typed_neutral_gap
    (d ell b F0 m k0 k1 r1 : Nat)
    (hell : 2 ≤ ell) (hd : 0 < d)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c cNext : Nat → Fin d → Bool)
    (Q0 W0 : Finset Nat)
    (T0 T1 : IntegerGraphSupport d ell)
    (lower middle : IntegerGraphSupport d ell → Nat)
    (hQ0Within : ∀ q ∈ Q0, b ≤ q ∧ q < F0)
    (hFirstStage : HasUniformPositiveSupportStage
      E d ell b F0 k0 hd c Q0 T0)
    (hFirstAge : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range F0)
        (supportBlockGappedColumn b Q0 T0.1 c)) = middle)
    (hNextPrefix : ∀ p, p < F0 → ∀ t,
      cNext p t = supportBlockGappedColumn b Q0 T0.1 c p t)
    (hWBefore : ∀ w ∈ W0, w < F0+m)
    (hZero : ∀ U : IntegerGraphSupport d ell,
      originalCriticalCount E ell d F0 cNext U m = 0)
    (hCover1 : AgeCover (IsIntegerGraphAge d ell) lower middle)
    (hEll1 : ell = lower T1 + r1 + 1)
    (hAt1 : middle T1 = lower T1 + 1) :
    ∃ (Q1 : Finset Nat) (F1 : Nat),
      Q1.card = r1 ∧
      (∀ q ∈ Q1, F0+m ≤ q ∧ q < F1) ∧
      IsDirectedCliqueOn E Q1 ∧
      (∀ p, p < F0+m → ∀ q ∈ Q1,
        E p q = false ∧ E q p = false) ∧
      (∀ q0 ∈ Q0, ∀ q1 ∈ Q1,
        E q0 q1 = false ∧ E q1 q0 = false) ∧
      (∀ w ∈ W0, ∀ q ∈ Q1,
        E w q = false ∧ E q w = false) ∧
      (∀ w ∈ W0, ∀ t : Fin d,
        supportBlockGappedColumn (F0+m) Q1 T1.1
          cNext w t = cNext w t) ∧
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range F1)
          (supportBlockGappedColumn (F0+m) Q1 T1.1 cNext)) = lower ∧
      HasUniformPositiveSupportStage E d ell b F0 k0 hd c Q0 T0 ∧
      HasUniformPositiveSupportStage E d ell (F0+m) F1 k1 hd
        cNext Q1 T1 := by
  classical
  have hNextAge :
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range F0) cNext) = middle :=
    (integerGraphAgeCanonical_eq_of_column_prefix E ell d F0
      cNext (supportBlockGappedColumn b Q0 T0.1 c)
      hNextPrefix).trans hFirstAge
  obtain ⟨Q1, F1, hCard, hWithin, hClique, hIso,
      hAge, _hFeasible, hSecondStage⟩ :=
    henson_leftDense_physical_cover_after_zero_critical_interval
      d ell F0 m k1 r1 hell hd E hAvoid hDense
      cNext T1 lower middle hCover1 hEll1 hAt1 hNextAge hZero
  refine ⟨Q1, F1, hCard, hWithin, hClique, hIso,
    ?_, ?_, ?_, hAge, hFirstStage, hSecondStage⟩
  · intro q0 hq0 q1 hq1
    have hq0N : q0 < F0+m := by
      have hq0F := (hQ0Within q0 hq0).2
      omega
    exact hIso q0 hq0N q1 hq1
  · intro w hw q hq
    exact hIso w (hWBefore w hw) q hq
  · intro w hw t
    exact supportBlockGappedColumn_eq_before_cut
      (F0+m) Q1 T1.1
      cNext (fun q hq => (hWithin q hq).1)
      w (hWBefore w hw) t

#print axioms Kk.supportBlockGappedColumn_eq_before_cut
#print axioms Kk.oldSupportCommonNeighbourPool_eq_of_column_prefix
#print axioms Kk.integerGraphAgeCanonical_eq_of_column_prefix
#print axioms Kk.henson_leftDense_second_cover_after_preserved_typed_neutral_gap

end Kk
