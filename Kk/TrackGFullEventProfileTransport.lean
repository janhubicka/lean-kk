import Kk.NumericHStructuralCutClassifier
import Kk.NumericHPhysicalI2Fork
import Kk.IndexedPhysicalStructuralEvents
import Mathlib.Tactic

/-!
# Track G: the FULL local Kpt I1/I2/I3 test is determined by a
# terminal flag and the complete old/upper dependent L+/E crossing relation.

English proof and 20 hostile checks committed BEFORE Lean:
docs/track_g_full_event_profile_english_audit_20261118.md

Unlike source inclusion or same-run results, this compares two DISTINCT
actual Kpt source sets Z,W without matching their members one-to-one.
Matching the complete raw ancestor-pair RELATION at the same numerical
cut supplies a physical mate for each crossing, so the genuine monoid
skip constraint transfers. Adding the terminal flag handles the I1
blindness of crossing-only profiles; I1 OR I2 is read from the complete
crossing relation's nonfunctionality.

This is an exact one-CUT source comparison in one fixed normalized Kpt
tree. It does NOT identify different diary cut coordinates, construct
matching profiles from selected macrodiaries, compare total monoid
embeddings or settle any global Kk-free big Ramsey degree.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

/-- Equal complete physical old/upper Kpt crossing relations give
each genuine source node crossing the cut a potentially DIFFERENT
physical mate in the other source with literally equal old AND upper
ancestors. No equal source cardinality, source injection, E1 or
no-I2 hypothesis. -/
theorem kpt_full_crossing_eq_has_physical_ancestor_mate
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z W : Set (AdmissibleKptNode family))
    (cut : Nat)
    (hPairs : FullPhysicalClosureCrossing family Z cut =
      FullPhysicalClosureCrossing family W cut)
    (z : AdmissibleKptNode family) (hz : z ∈ Z)
    (hCut : cut < LevelTree.lev z) :
    ∃ w : AdmissibleKptNode family,
      w ∈ W ∧ ∃ (hw : cut < LevelTree.lev w),
        LevelTree.ancestor z cut (Nat.le_of_lt hCut) =
          LevelTree.ancestor w cut (Nat.le_of_lt hw) ∧
        LevelTree.ancestor z (cut+1) (Nat.succ_le_iff.mpr hCut) =
          LevelTree.ancestor w (cut+1) (Nat.succ_le_iff.mpr hw) := by
  obtain ⟨T,U,hZPair,hOldZ,hUpperZ⟩ :=
    kpt_actual_crossing_has_physical_full_pair
      family Z cut z hz hCut
  have hWPair :
      (T,U) ∈ FullPhysicalClosureCrossing family W cut := by
    rw [← hPairs]
    exact hZPair
  obtain ⟨w,hw,hWCut,hOldW,hUpperW⟩ := hWPair
  have hZTypes := kpt_full_old_upper_types_of_crossing z cut hCut
  have hZOldRaw :
      (⟨cut,T⟩ : RawPartialTypeNode db du dd) =
        (LevelTree.ancestor z cut (Nat.le_of_lt hCut)).val :=
    Option.some.inj (hOldZ.symm.trans hZTypes.1)
  have hZUpperRaw :
      (⟨cut+1,U⟩ : RawPartialTypeNode db du dd) =
        (LevelTree.ancestor z (cut+1)
          (Nat.succ_le_iff.mpr hCut)).val :=
    Option.some.inj (hUpperZ.symm.trans hZTypes.2)
  refine ⟨w,hw,hWCut,?_,?_⟩
  · apply Subtype.ext
    exact hZOldRaw.symm.trans hOldW
  · apply Subtype.ext
    exact hZUpperRaw.symm.trans hUpperW

/-- For EACH genuine total Kpt monoid map D, the entire one-cut
skipping equation on all crossing source nodes is determined by
the FULL old/upper Kpt crossing relation, not the actual source
node enumeration. The pair relation includes auxiliary E bits. -/
theorem kpt_actual_skipLaw_iff_of_full_crossing_eq
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z W : Set (AdmissibleKptNode family))
    (cut : Nat)
    (hPairs : FullPhysicalClosureCrossing family Z cut =
      FullPhysicalClosureCrossing family W cut)
    (D : MMap (normalizedKptSMTree family)) :
    (∀ ⦃z : AdmissibleKptNode family⦄,
      z ∈ Z → ∀ (hc : cut < LevelTree.lev z),
        D (LevelTree.ancestor z cut (Nat.le_of_lt hc)) =
          LevelTree.ancestor z (cut+1) (Nat.succ_le_iff.mpr hc)) ↔
    (∀ ⦃z : AdmissibleKptNode family⦄,
      z ∈ W → ∀ (hc : cut < LevelTree.lev z),
        D (LevelTree.ancestor z cut (Nat.le_of_lt hc)) =
          LevelTree.ancestor z (cut+1) (Nat.succ_le_iff.mpr hc)) := by
  constructor
  · intro hZ z hz hc
    obtain ⟨w,hw,hwc,hEqOld,hEqUpper⟩ :=
      kpt_full_crossing_eq_has_physical_ancestor_mate
        family W Z cut hPairs.symm z hz hc
    calc
      D (LevelTree.ancestor z cut (Nat.le_of_lt hc)) =
          D (LevelTree.ancestor w cut (Nat.le_of_lt hwc)) :=
        congrArg D hEqOld
      _ = LevelTree.ancestor w (cut+1)
            (Nat.succ_le_iff.mpr hwc) := hZ hw hwc
      _ = LevelTree.ancestor z (cut+1)
            (Nat.succ_le_iff.mpr hc) := hEqUpper.symm
  · intro hW z hz hc
    obtain ⟨w,hw,hwc,hEqOld,hEqUpper⟩ :=
      kpt_full_crossing_eq_has_physical_ancestor_mate
        family Z W cut hPairs z hz hc
    calc
      D (LevelTree.ancestor z cut (Nat.le_of_lt hc)) =
          D (LevelTree.ancestor w cut (Nat.le_of_lt hwc)) :=
        congrArg D hEqOld
      _ = LevelTree.ancestor w (cut+1)
            (Nat.succ_le_iff.mpr hwc) := hW hw hwc
      _ = LevelTree.ancestor z (cut+1)
            (Nat.succ_le_iff.mpr hc) := hEqUpper.symm

/-- TRUE cross-occurrence local event criterion: matching terminal
presence and COMPLETE dependent old/upper physical Kpt crossing
relations at ONE COMMON cut determines all three I1/I2/I3 branches
of the genuine normalized Algorithm 5.4 interestingness test.

Source Z and source W can be disjoint, use differently sized indices,
and contain genuine I2 forks. The two sources must be in the SAME
normalized Kpt tree at the SAME numerical cut. No equality of
selected ordinary graph ages is used. -/
theorem kpt_IsInterestingAt_iff_of_terminal_and_full_crossing_eq
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z W : Set (AdmissibleKptNode family))
    (cut : Nat)
    (hTerminal :
      KptI1AtCut family Z cut ↔ KptI1AtCut family W cut)
    (hPairs : FullPhysicalClosureCrossing family Z cut =
      FullPhysicalClosureCrossing family W cut) :
    SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family) Z cut ↔
    SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family) W cut := by
  have hNonfunctional :
      (∃ T : PartialTypeWithE cut db du dd,
        ∃ U V : PartialTypeWithE (cut+1) db du dd,
          (T,U) ∈ FullPhysicalClosureCrossing family Z cut ∧
          (T,V) ∈ FullPhysicalClosureCrossing family Z cut ∧
          U ≠ V) ↔
      (∃ T : PartialTypeWithE cut db du dd,
        ∃ U V : PartialTypeWithE (cut+1) db du dd,
          (T,U) ∈ FullPhysicalClosureCrossing family W cut ∧
          (T,V) ∈ FullPhysicalClosureCrossing family W cut ∧
          U ≠ V) := by
    rw [hPairs]
  have hStructural :
      (KptI1AtCut family Z cut ∨ KptI2MeetAtCut family Z cut) ↔
      (KptI1AtCut family W cut ∨ KptI2MeetAtCut family W cut) := by
    calc
      (KptI1AtCut family Z cut ∨ KptI2MeetAtCut family Z cut) ↔
        (KptI1AtCut family Z cut ∨
          ∃ T : PartialTypeWithE cut db du dd,
            ∃ U V : PartialTypeWithE (cut+1) db du dd,
              (T,U) ∈ FullPhysicalClosureCrossing family Z cut ∧
              (T,V) ∈ FullPhysicalClosureCrossing family Z cut ∧
              U ≠ V) :=
        kpt_I1_or_I2_iff_I1_or_physical_nonfunctional family Z cut
      _ ↔
        (KptI1AtCut family W cut ∨
          ∃ T : PartialTypeWithE cut db du dd,
            ∃ U V : PartialTypeWithE (cut+1) db du dd,
              (T,U) ∈ FullPhysicalClosureCrossing family W cut ∧
              (T,V) ∈ FullPhysicalClosureCrossing family W cut ∧
              U ≠ V) :=
        or_congr hTerminal hNonfunctional
      _ ↔
        (KptI1AtCut family W cut ∨ KptI2MeetAtCut family W cut) :=
        (kpt_I1_or_I2_iff_I1_or_physical_nonfunctional
          family W cut).symm
  let CanSkip (C : Set (AdmissibleKptNode family)) : Prop :=
    ∃ D : MMap (normalizedKptSMTree family),
      D.map.SkipsOnly cut ∧
      ∀ ⦃z : AdmissibleKptNode family⦄,
        z ∈ C → ∀ (hc : cut < LevelTree.lev z),
          D (LevelTree.ancestor z cut (Nat.le_of_lt hc)) =
            LevelTree.ancestor z (cut+1) (Nat.succ_le_iff.mpr hc)
  have hSkip : CanSkip Z ↔ CanSkip W := by
    constructor
    · rintro ⟨D,hD,hCross⟩
      exact ⟨D,hD,
        (kpt_actual_skipLaw_iff_of_full_crossing_eq
          family Z W cut hPairs D).mp hCross⟩
    · rintro ⟨D,hD,hCross⟩
      exact ⟨D,hD,
        (kpt_actual_skipLaw_iff_of_full_crossing_eq
          family Z W cut hPairs D).mpr hCross⟩
  change
    (KptI1AtCut family Z cut ∨
      KptI2MeetAtCut family Z cut ∨ ¬ CanSkip Z) ↔
    (KptI1AtCut family W cut ∨
      KptI2MeetAtCut family W cut ∨ ¬ CanSkip W)
  simpa only [or_assoc] using
    (or_congr hStructural (not_congr hSkip))

/-- Finite, independently EXHAUSTIVE indices on two DIFFERENT
Kpt sources need not be related by any node bijection.
Equality of their indexed terminal flag and full old/upper
L+/E pair relation suffices for exactly the same genuine
Algorithm 5.4 I1/I2/I3 decision at the aligned cut.

This is the honest local source-matching interface for different
diary occurrences. Constructing those profile equalities from the
macrodiary, and the cross-cut labelled orbit, remain OPEN. -/
theorem kpt_two_independent_indices_same_full_event_profile_implies_interesting
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {Params₁ Params₂ : Type}
    (Z W : Set (AdmissibleKptNode family))
    (node₁ : Params₁ → AdmissibleKptNode family)
    (node₂ : Params₂ → AdmissibleKptNode family)
    (live₁ : Nat → Params₁ → Bool)
    (live₂ : Nat → Params₂ → Bool)
    (cut : Nat)
    (hExact₁ : ∀ z : AdmissibleKptNode family,
      z ∈ Z ↔ ∃ j : Params₁,
        node₁ j = z ∧ live₁ cut j = true)
    (hExact₂ : ∀ z : AdmissibleKptNode family,
      z ∈ W ↔ ∃ j : Params₂,
        node₂ j = z ∧ live₂ cut j = true)
    (hTerminal :
      (∃ j : Params₁, live₁ cut j = true ∧
        LevelTree.lev (node₁ j) = cut) ↔
      (∃ j : Params₂, live₂ cut j = true ∧
        LevelTree.lev (node₂ j) = cut))
    (hCrossing :
      IndexedPhysicalCrossing family node₁ live₁ cut =
        IndexedPhysicalCrossing family node₂ live₂ cut) :
    SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family) Z cut ↔
    SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family) W cut := by
  have hFirst :=
    (physical_I1_I2_iff_indexed_active_nodes
      family node₁ live₁ Z cut hExact₁).1
  have hSecond :=
    (physical_I1_I2_iff_indexed_active_nodes
      family node₂ live₂ W cut hExact₂).1
  have hTerminalActual :
      KptI1AtCut family Z cut ↔ KptI1AtCut family W cut :=
    hFirst.trans (hTerminal.trans hSecond.symm)
  have hFullPairs :
      FullPhysicalClosureCrossing family Z cut =
        FullPhysicalClosureCrossing family W cut := by
    calc
      FullPhysicalClosureCrossing family Z cut =
        IndexedPhysicalCrossing family node₁ live₁ cut :=
        (indexed_physical_crossing_eq_full_closure_relation
          family node₁ live₁ Z cut hExact₁).symm
      _ = IndexedPhysicalCrossing family node₂ live₂ cut := hCrossing
      _ = FullPhysicalClosureCrossing family W cut :=
        indexed_physical_crossing_eq_full_closure_relation
          family node₂ live₂ W cut hExact₂
  exact kpt_IsInterestingAt_iff_of_terminal_and_full_crossing_eq
    family Z W cut hTerminalActual hFullPairs

end Kk
