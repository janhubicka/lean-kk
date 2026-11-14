import Kk.CofinalNeutralOldColumnAge
import Kk.IsolatedSupportBlockRawAge
import Mathlib.Tactic

/-!
# Track A: exact actual old-column age with a nonconsecutive reserved block AND all gaps

English proof and hostile audit BEFORE code:
  docs/physical_isolated_support_stage_english_audit.md

All genuine original indices in [0,F) are retained, including
intervening gaps between nonconsecutive reserved originals Q.
Every gap in [b,F)\Q is assigned a COMPLETE zero typed
old-to-future column; it cannot join any NONEMPTY common
future support neighbourhood. Hence the raw old-column age
computed over the ENTIRE literal prefix [0,F) equals the
raw age computed over [0,b) ∪ Q, with Q connected precisely
to the designated sort support T.

This is literal equality of the complete finite common
neighbour pools in the unchanged E, not an abstract selected
shadow or unproved re-enumeration. It is valid even when gaps
have arbitrary original edges among themselves and to Q,
and when raw bounds may be zero. Does not construct a
genuine reserved stage or prove H+ parameter-closed B3.
-/

namespace Kk

/-- One exact complete future type column over an actual enlarged
prefix: old p<b retains c, reserved p∈Q sees precisely T,
every other intervening original p≥b sees NO future sort. -/
def supportBlockGappedColumn {d : Nat}
    (b : Nat) (Q : Finset Nat) (T : Finset (Fin d))
    (c : Nat → Fin d → Bool) (p : Nat) (t : Fin d) : Bool :=
  supportBlockOldColumn Q T (delayedOldColumn b c) p t

/-- On the actual old-plus-reserved subpool the complete gapped
column agrees with the direct reserved-block update. The
disjointness follows from every q∈Q lying after the old cutoff b. -/
theorem supportBlockGappedColumn_agrees_on_old_and_Q
    {d : Nat} (b : Nat) (Q : Finset Nat)
    (hQAfter : ∀ q ∈ Q, b ≤ q)
    (T : Finset (Fin d)) (c : Nat → Fin d → Bool)
    (p : Nat) (hp : p ∈ Finset.range b ∪ Q)
    (t : Fin d) :
    supportBlockGappedColumn b Q T c p t =
      supportBlockOldColumn Q T c p t := by
  classical
  by_cases hpQ : p ∈ Q
  · simp [supportBlockGappedColumn, supportBlockOldColumn, hpQ]
  · have hpOld : p < b := by
      rcases Finset.mem_union.mp hp with hpB | hpQ'
      · exact Finset.mem_range.mp hpB
      · exact False.elim (hpQ hpQ')
    simp [supportBlockGappedColumn, supportBlockOldColumn,
      delayedOldColumn, hpQ, hpOld]

/-- Complete exact old common-neighbourhood pool identity.
Every real gap original in [b,F)\Q has all-zero future columns,
and therefore cannot be adjacent to ALL sorts in the NONEMPTY
support U. The formula retains every original vertex of the
unchanged actual prefix. -/
theorem supportBlockGappedCommonNeighbourPool_eq
    {d ell : Nat} (b F : Nat) (hBF : b ≤ F)
    (Q : Finset Nat)
    (hQWithin : ∀ q ∈ Q, b ≤ q ∧ q < F)
    (T U : IntegerGraphSupport d ell)
    (c : Nat → Fin d → Bool) :
    oldSupportCommonNeighbourPool (Finset.range F)
        (supportBlockGappedColumn b Q T.1 c) U.1 =
      oldSupportCommonNeighbourPool (Finset.range b ∪ Q)
        (supportBlockOldColumn Q T.1 c) U.1 := by
  classical
  have hQAfter : ∀ q ∈ Q, b ≤ q :=
    fun q hq => (hQWithin q hq).1
  have hAgree : ∀ p ∈ Finset.range b ∪ Q,
      ∀ t : Fin d,
      supportBlockGappedColumn b Q T.1 c p t =
        supportBlockOldColumn Q T.1 c p t := by
    intro p hp t
    exact supportBlockGappedColumn_agrees_on_old_and_Q
      b Q hQAfter T.1 c p hp t
  ext p
  constructor
  · intro hp
    obtain ⟨hpF,hAll⟩ := Finset.mem_filter.mp hp
    have hpOldQ : p ∈ Finset.range b ∪ Q := by
      by_contra hNotOldQ
      have hpNotQ : p ∉ Q := by
        intro hpQ
        exact hNotOldQ (Finset.mem_union.mpr (Or.inr hpQ))
      have hpNotB : ¬ p < b := by
        intro hpB
        exact hNotOldQ
          (Finset.mem_union.mpr
            (Or.inl (Finset.mem_range.mpr hpB)))
      obtain ⟨t,ht⟩ := U.2.1
      have hBit := hAll t ht
      have hZero :
          supportBlockGappedColumn b Q T.1 c p t = false := by
        simp [supportBlockGappedColumn,
          supportBlockOldColumn, delayedOldColumn, hpNotQ, hpNotB]
      rw [hZero] at hBit
      contradiction
    apply Finset.mem_filter.mpr
    refine ⟨hpOldQ,?_⟩
    intro t ht
    rw [← hAgree p hpOldQ t]
    exact hAll t ht
  · intro hp
    obtain ⟨hpOldQ,hAll⟩ := Finset.mem_filter.mp hp
    have hpF : p < F := by
      rcases Finset.mem_union.mp hpOldQ with hpOld | hpQ
      · exact lt_of_lt_of_le (Finset.mem_range.mp hpOld) hBF
      · exact (hQWithin p hpQ).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hpF,?_⟩
    intro t ht
    rw [hAgree p hpOldQ t]
    exact hAll t ht

/-- Pointwise equality of the TRUE physical entire-original-prefix
raw old-column age after inserting Q and making all actual
intervening gaps zero, and the raw age of the direct old+Q pool.
No gap original is silently deleted or re-enumerated. -/
theorem supportBlockGappedRawBound_eq
    (E : Nat → Nat → Bool) (ell d b F : Nat) (hBF : b ≤ F)
    (Q : Finset Nat)
    (hQWithin : ∀ q ∈ Q, b ≤ q ∧ q < F)
    (T : IntegerGraphSupport d ell)
    (c : Nat → Fin d → Bool) :
    finiteOldColumnRawBound E ell d (Finset.range F)
      (supportBlockGappedColumn b Q T.1 c) =
    finiteOldColumnRawBound E ell d (Finset.range b ∪ Q)
      (supportBlockOldColumn Q T.1 c) := by
  funext U
  unfold finiteOldColumnRawBound
  rw [supportBlockGappedCommonNeighbourPool_eq
    b F hBF Q hQWithin T U c]

/-- The normalized integer graph-age canonicalizers also agree
pointwise because the complete RAW age functions are equal.
This is not an assertion of pointwise equality to the separate
IDEAL one-coordinate raw clique-block cover function. -/
theorem supportBlockGappedCanonicalAge_eq
    (E : Nat → Nat → Bool) (ell d b F : Nat) (hBF : b ≤ F)
    (Q : Finset Nat)
    (hQWithin : ∀ q ∈ Q, b ≤ q ∧ q < F)
    (T : IntegerGraphSupport d ell)
    (c : Nat → Fin d → Bool) :
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range F)
        (supportBlockGappedColumn b Q T.1 c)) =
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b ∪ Q)
        (supportBlockOldColumn Q T.1 c)) := by
  rw [supportBlockGappedRawBound_eq E ell d b F hBF Q hQWithin T c]

#print axioms Kk.supportBlockGappedColumn_agrees_on_old_and_Q
#print axioms Kk.supportBlockGappedCommonNeighbourPool_eq
#print axioms Kk.supportBlockGappedRawBound_eq
#print axioms Kk.supportBlockGappedCanonicalAge_eq

end Kk
