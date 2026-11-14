import Kk.PriorityPhysicalB3Transfer
import Kk.NumericHPhysicalI2Fork
import SuccessorTree.V10.I3AlgorithmInterestingBridge
import Mathlib.Tactic

/-!
# Track E: genuine Kpt I3 and full Algorithm-5.4 interestingness are
# determined by the complete physical old/upper L+ crossing relation

A Kpt one-level shape map respects the full closure iff it respects
each old/upper pair of the canonical complete physical relation.
Thus the SAME concrete ShapeMap in the genuine Kpt monoid witnesses
one-level skippability in either of two sources with identical
full crossing relations. This is **not** a corrected-B3 assertion.

With the terminal I1 flag, Track C's no-I1 I2/fork theorem gives
equality of the FULL I1/I2/I3/noninteresting event classification
at a common source-coordinate cut.

English-first proof and hostile audit:
  docs/track_e_priority_cut_comparison_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- One-sided transfer of all Kpt crossing equations for a fixed,
GENUINE ShapeMap. Every crossing pair in Z₂ is realized by some
actual source crossing in Z₁, so exactly the same old and upper
Kpt ancestors occur. Neither monoid membership nor any skip law
is needed for this elementary extensionality step.

No assumption of injective source-node index maps is used. -/
theorem kpt_crossing_map_respects_of_physical_inclusion
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z₁ Z₂ : Set (AdmissibleKptNode family))
    (cut : Nat)
    (Φ : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hSubset :
      FullPhysicalClosureCrossing family Z₂ cut ⊆
        FullPhysicalClosureCrossing family Z₁ cut)
    (hRespect : ∀ z : AdmissibleKptNode family, z ∈ Z₁ →
      ∀ (hCut : cut < LevelTree.lev z),
        Φ (LevelTree.ancestor z cut (Nat.le_of_lt hCut)) =
          LevelTree.ancestor z (cut+1) (Nat.succ_le_iff.mpr hCut)) :
    ∀ z : AdmissibleKptNode family, z ∈ Z₂ →
      ∀ (hCut : cut < LevelTree.lev z),
        Φ (LevelTree.ancestor z cut (Nat.le_of_lt hCut)) =
          LevelTree.ancestor z (cut+1) (Nat.succ_le_iff.mpr hCut) := by
  intro z hz hCutZ
  obtain ⟨T,U,hPairZ,hOldZ,hUpperZ⟩ :=
    kpt_actual_crossing_has_physical_full_pair
      family Z₂ cut z hz hCutZ
  obtain ⟨w,hw,hCutW,hOldW,hUpperW⟩ :=
    hSubset hPairZ
  have hRecordsZ :=
    kpt_full_old_upper_types_of_crossing z cut hCutZ
  have hOldRawZ :
      (⟨cut,T⟩ : RawPartialTypeNode db du dd) =
        (LevelTree.ancestor z cut (Nat.le_of_lt hCutZ)).val :=
    Option.some.inj (hOldZ.symm.trans hRecordsZ.1)
  have hUpperRawZ :
      (⟨cut+1,U⟩ : RawPartialTypeNode db du dd) =
        (LevelTree.ancestor z (cut+1)
          (Nat.succ_le_iff.mpr hCutZ)).val :=
    Option.some.inj (hUpperZ.symm.trans hRecordsZ.2)
  have hOldNode :
      LevelTree.ancestor z cut (Nat.le_of_lt hCutZ) =
        LevelTree.ancestor w cut (Nat.le_of_lt hCutW) := by
    apply Subtype.ext
    exact hOldRawZ.symm.trans hOldW
  have hUpperNode :
      LevelTree.ancestor z (cut+1) (Nat.succ_le_iff.mpr hCutZ) =
        LevelTree.ancestor w (cut+1) (Nat.succ_le_iff.mpr hCutW) := by
    apply Subtype.ext
    exact hUpperRawZ.symm.trans hUpperW
  calc
    Φ (LevelTree.ancestor z cut (Nat.le_of_lt hCutZ)) =
        Φ (LevelTree.ancestor w cut (Nat.le_of_lt hCutW)) := by
          rw [hOldNode]
    _ = LevelTree.ancestor w (cut+1) (Nat.succ_le_iff.mpr hCutW) :=
      hRespect w hw hCutW
    _ = LevelTree.ancestor z (cut+1) (Nat.succ_le_iff.mpr hCutZ) :=
      hUpperNode.symm

/-- Equality of FULL dependent old/upper crossing relations is
equivalent to equivalence of the real Kpt one-level non-skippability
obstruction (the genuine I3 clause). The SAME monoid ShapeMap is
transferred: no arbitrary selected-shadow graph map and no B3
age-witness/extra E expansion appears.

The result is valid even at a cut having I1 or I2 structural events;
their PRIORITY is handled separately by Algorithm 5.4. -/
theorem kpt_nonSkippable_iff_of_equal_physical_crossing
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z₁ Z₂ : Set (AdmissibleKptNode family))
    (cut : Nat)
    (hPhysical :
      FullPhysicalClosureCrossing family Z₁ cut =
        FullPhysicalClosureCrossing family Z₂ cut) :
    NonSkippableClosureCrossing family Z₁ cut ↔
      NonSkippableClosureCrossing family Z₂ cut := by
  have h12 :
      FullPhysicalClosureCrossing family Z₁ cut ⊆
        FullPhysicalClosureCrossing family Z₂ cut := by
    intro p hp
    rw [← hPhysical]
    exact hp
  have h21 :
      FullPhysicalClosureCrossing family Z₂ cut ⊆
        FullPhysicalClosureCrossing family Z₁ cut := by
    intro p hp
    rw [hPhysical]
    exact hp
  constructor
  · intro hNo₁
    rintro ⟨Φ,hMem,hSkip,hRespect₂⟩
    have hRespect₁ :=
      kpt_crossing_map_respects_of_physical_inclusion
        family Z₂ Z₁ cut Φ h12 hRespect₂
    exact hNo₁ ⟨Φ,hMem,hSkip,hRespect₁⟩
  · intro hNo₂
    rintro ⟨Φ,hMem,hSkip,hRespect₁⟩
    have hRespect₂ :=
      kpt_crossing_map_respects_of_physical_inclusion
        family Z₁ Z₂ cut Φ h21 hRespect₁
    exact hNo₂ ⟨Φ,hMem,hSkip,hRespect₂⟩

/-- The genuine generic successor-tree IsInterestingAt definition is
EXACTLY the union of physical terminal I1, physical meet I2 and
monoid non-skippable I3, because normalizedKptSMTree has actual
monoid KptM. No extra axioms, finite B3 assumptions or shadow
embeddings are introduced. -/
theorem kpt_actual_interesting_iff_I1_or_I2_or_nonskippable
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family))
    (cut : Nat) :
    SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family) Z cut ↔
    (KptI1AtCut family Z cut ∨
      KptI2MeetAtCut family Z cut ∨
      NonSkippableClosureCrossing family Z cut) := by
  constructor
  · intro hInteresting
    rcases hInteresting with hI1 | hOther
    · exact Or.inl hI1
    · rcases hOther with hI2 | hI3
      · exact Or.inr (Or.inl hI2)
      · refine Or.inr (Or.inr ?_)
        rintro ⟨Φ,hMem,hSkip,hRespect⟩
        let D : SuccessorTree.SMTree.MMap (normalizedKptSMTree family) :=
          ⟨Φ,hMem⟩
        apply hI3
        refine ⟨D,hSkip,?_⟩
        intro z hz hCutZ
        exact hRespect z hz hCutZ
  · intro h
    rcases h with hI1 | hI2OrSkip
    · exact Or.inl hI1
    · rcases hI2OrSkip with hI2 | hNoSkip
      · exact Or.inr (Or.inl hI2)
      · refine Or.inr (Or.inr ?_)
        rintro ⟨D,hSkip,hRespect⟩
        rcases D with ⟨Φ,hMem⟩
        apply hNoSkip
        refine ⟨Φ,hMem,hSkip,?_⟩
        intro z hz hCutZ
        exact hRespect hz hCutZ

/-- The ACTUAL Algorithm-5.4 interestingness decision (including the
real monoid I3 obstruction) is invariant across two different Kpt
closures if the terminal I1 flags and complete physical full-L+
crossing relations agree at the same SOURCE-coordinate cut.

This does not assert the (unrefined) KK macrodiary supplies either
agreement; it removes the need to compare all meet incidences
just to classify LOCAL I1/I2/I3 interestingness. -/
theorem kpt_actual_interesting_iff_of_terminal_and_crossing_eq
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z₁ Z₂ : Set (AdmissibleKptNode family))
    (cut : Nat)
    (hTerminal : KptI1AtCut family Z₁ cut ↔
      KptI1AtCut family Z₂ cut)
    (hPhysical :
      FullPhysicalClosureCrossing family Z₁ cut =
        FullPhysicalClosureCrossing family Z₂ cut) :
    SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family) Z₁ cut ↔
    SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family) Z₂ cut := by
  have hFlags :=
    kpt_priority_structural_flags_eq_of_terminal_and_crossings
      family Z₁ Z₂ cut hTerminal hPhysical
  have hSkip :=
    kpt_nonSkippable_iff_of_equal_physical_crossing
      family Z₁ Z₂ cut hPhysical
  have hStructural :
      (KptI1AtCut family Z₁ cut ∨ KptI2MeetAtCut family Z₁ cut) ↔
      (KptI1AtCut family Z₂ cut ∨ KptI2MeetAtCut family Z₂ cut) := by
    constructor
    · intro h
      rcases h with hI1 | hI2
      · exact Or.inl (hTerminal.mp hI1)
      · by_cases hI1 : KptI1AtCut family Z₁ cut
        · exact Or.inl (hTerminal.mp hI1)
        · exact Or.inr (hFlags.2.1.mp ⟨hI1,hI2⟩).2
    · intro h
      rcases h with hI1 | hI2
      · exact Or.inl (hTerminal.mpr hI1)
      · by_cases hI1 : KptI1AtCut family Z₂ cut
        · exact Or.inl (hTerminal.mpr hI1)
        · exact Or.inr (hFlags.2.1.mpr ⟨
            (fun ht => hI1 (hTerminal.mpr ht)),hI2⟩).2
  calc
    SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family) Z₁ cut ↔
        (KptI1AtCut family Z₁ cut ∨
          KptI2MeetAtCut family Z₁ cut ∨
          NonSkippableClosureCrossing family Z₁ cut) :=
      kpt_actual_interesting_iff_I1_or_I2_or_nonskippable
        family Z₁ cut
    _ ↔ ((KptI1AtCut family Z₁ cut ∨
            KptI2MeetAtCut family Z₁ cut) ∨
          NonSkippableClosureCrossing family Z₁ cut) := by
      simp only [or_assoc]
    _ ↔ ((KptI1AtCut family Z₂ cut ∨
            KptI2MeetAtCut family Z₂ cut) ∨
          NonSkippableClosureCrossing family Z₂ cut) :=
      or_congr hStructural hSkip
    _ ↔ (KptI1AtCut family Z₂ cut ∨
            KptI2MeetAtCut family Z₂ cut ∨
          NonSkippableClosureCrossing family Z₂ cut) := by
      simp only [or_assoc]
    _ ↔ SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family) Z₂ cut :=
      (kpt_actual_interesting_iff_I1_or_I2_or_nonskippable
        family Z₂ cut).symm

end Kk
