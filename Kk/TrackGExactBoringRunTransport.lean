import Kk.TrackGBoringOnlyNoNoveltyRunTransfer
import Kk.TrackGUniqueBoringBlockFactor
import Mathlib.Tactic

/-!
# Track G: exact old-boring source/monoid criterion for preserving
# the entire selected I and TOTAL monoid F of an actual AlgorithmRun

English proof and 16 hostile checks committed FIRST:
docs/track_g_exact_boring_transport_criterion_english_audit_20261119.md

The physical no-novelty of G365 and empty canonical Bad of G371
are SUFFICIENT, not necessary, for same-I/F run transport. Here the
actual exact criterion is characterized: every OLD-BORING cut must
remain boring in the target complete source and admit SOME genuine
target one-level skipping MMap compatible with the prescribed old
TOTAL F-step equation. Old interesting cuts remain interesting
automatically under nested seed source inclusion.

No E1, source bijection, cut-coordinate reindexing or uniform
labelled inverse-source orbit is assumed. An explicit second theorem
replaces the target boringness predicate with the full I1 terminal
absence, I2 genuine same-component meet absence and a genuine
compatible full-source skip monoid equation.
-/

namespace Kk

universe u v

open SuccessorTree
open SuccessorTree.SMTree

/-- Exact criterion (IFF) for transporting an actual
AlgorithmRun's selected I and TOTAL monoid F without changes
to a larger nested seed source X ⊆ Y.

Only OLD-BORING cuts require a certificate. The target need not
have the same full physical crossing relation as the old source:
a compatible total step map may exist despite new crossings. -/
theorem actualRun_transport_iff_old_boring_compatible
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    {S : STree T Label}
    (H : SMTree S)
    (X Y : Set T) (hXY : X ⊆ Y)
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun H X top) :
    (∃ RY : SMTree.Envelope.AlgorithmRun H Y top,
      RY.I = RX.I ∧ RY.F = RX.F) ↔
    (∀ cut : Nat, cut < top →
      ¬ SMTree.Envelope.IsInterestingAt H
        (SMTree.Envelope.closure S (RX.I (cut+1)) X) cut →
      ¬ SMTree.Envelope.IsInterestingAt H
        (SMTree.Envelope.closure S (RX.I (cut+1)) Y) cut ∧
      ∃ D : MMap H,
        D.map.SkipsOnly cut ∧
        (∀ ⦃z : T⦄,
          z ∈ SMTree.Envelope.closure S (RX.I (cut+1)) Y →
          ∀ (hCross : cut < LevelTree.lev z),
            D (LevelTree.ancestor z cut (Nat.le_of_lt hCross)) =
              LevelTree.ancestor z (cut+1)
                (Nat.succ_le_iff.mpr hCross)) ∧
        RX.F cut = MMap.comp H (RX.F (cut+1)) D) := by
  have hSubset (cut : Nat) :
      SMTree.Envelope.closure S (RX.I (cut+1)) X ⊆
        SMTree.Envelope.closure S (RX.I (cut+1)) Y :=
    envelope_closure_mono_seeds_and_levels
      S (RX.I (cut+1)) (RX.I (cut+1)) X Y
      (by intro i hi; exact hi) hXY
  constructor
  · rintro ⟨RY,hIEq,hFEq⟩
    intro cut hCut hOldBoring
    have hTargetBoring :
        ¬ SMTree.Envelope.IsInterestingAt H
          (SMTree.Envelope.closure S (RX.I (cut+1)) Y) cut := by
      intro hTarget
      have hTargetForRY :
          SMTree.Envelope.IsInterestingAt H
            (SMTree.Envelope.closure S (RY.I (cut+1)) Y) cut := by
        simpa only [hIEq] using hTarget
      have hMem : cut ∈ RY.I cut := by
        rw [(RY.interesting_step cut hCut hTargetForRY).1]
        simp
      rw [hIEq] at hMem
      obtain ⟨_D,_hSkip,_hCross,hOldI,_hOldF⟩ :=
        RX.noninteresting_step cut hCut hOldBoring
      rw [hOldI] at hMem
      have hImpossible : cut+1 ≤ cut :=
        (RX.I_mem_bounds (cut+1) (by omega) cut hMem).1
      omega
    have hTargetForRY :
        ¬ SMTree.Envelope.IsInterestingAt H
          (SMTree.Envelope.closure S (RY.I (cut+1)) Y) cut := by
      simpa only [hIEq] using hTargetBoring
    obtain ⟨D,hSkip,hCross,hI,hF⟩ :=
      RY.noninteresting_step cut hCut hTargetForRY
    refine ⟨hTargetBoring,D,hSkip,?_,?_⟩
    · simpa only [hIEq] using hCross
    · simpa only [hFEq] using hF
  · intro hCompat
    let RY : SMTree.Envelope.AlgorithmRun H Y top :=
      { I := RX.I
        F := RX.F
        topI := RX.topI
        topF := RX.topF
        interesting_step := by
          intro cut hCut hTarget
          by_cases hOld :
              SMTree.Envelope.IsInterestingAt H
                (SMTree.Envelope.closure S (RX.I (cut+1)) X) cut
          · exact RX.interesting_step cut hCut hOld
          · exact False.elim ((hCompat cut hCut hOld).1 hTarget)
        noninteresting_step := by
          intro cut hCut hTargetBoring
          have hOldBoring :
              ¬ SMTree.Envelope.IsInterestingAt H
                (SMTree.Envelope.closure S (RX.I (cut+1)) X) cut := by
            intro hOldInteresting
            exact hTargetBoring
              (kpt_generic_IsInterestingAt_mono_of_source_subset
                H
                (SMTree.Envelope.closure S (RX.I (cut+1)) X)
                (SMTree.Envelope.closure S (RX.I (cut+1)) Y)
                cut (hSubset cut) hOldInteresting)
          obtain ⟨_hNewBoring,D,hSkip,hCross,hOldF⟩ :=
            hCompat cut hCut hOldBoring
          obtain ⟨_E,_hOldSkip,_hOldCross,hOldI,_hOldFStep⟩ :=
            RX.noninteresting_step cut hCut hOldBoring
          exact ⟨D,hSkip,hCross,hOldI,hOldF⟩ }
    exact ⟨RY,rfl,rfl⟩

/-- A geometric sufficient condition for exact same-I same-TOTAL-F
run transfer at all old-boring cuts. I1 and I2 must both be absent
in the complete candidate target source, and some actual target
skip map must satisfy the prescribed original TOTAL F equation.

This is weaker than physical crossing-pair equality/no-novelty:
new crossings are allowed if the chosen compatible skip map
satisfies all of their extra equations. -/
theorem actualRun_transport_of_old_boring_explicit_physical_compatible
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    {S : STree T Label}
    (H : SMTree S)
    (X Y : Set T) (hXY : X ⊆ Y)
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun H X top)
    (hPhysical : ∀ cut : Nat, cut < top →
      ¬ SMTree.Envelope.IsInterestingAt H
        (SMTree.Envelope.closure S (RX.I (cut+1)) X) cut →
      (¬ ∃ z : T, z ∈ SMTree.Envelope.closure S
          (RX.I (cut+1)) Y ∧ LevelTree.lev z = cut) ∧
      (¬ ∃ a : T, a ∈ SMTree.Envelope.closure S
          (RX.I (cut+1)) Y ∧
        ∃ b : T, b ∈ SMTree.Envelope.closure S
          (RX.I (cut+1)) Y ∧
          SMTree.Envelope.SameComponent a b ∧
          LevelTree.lev (LevelTree.meet a b) = cut) ∧
      ∃ D : MMap H,
        D.map.SkipsOnly cut ∧
        (∀ ⦃z : T⦄,
          z ∈ SMTree.Envelope.closure S (RX.I (cut+1)) Y →
          ∀ (hCross : cut < LevelTree.lev z),
            D (LevelTree.ancestor z cut (Nat.le_of_lt hCross)) =
              LevelTree.ancestor z (cut+1)
                (Nat.succ_le_iff.mpr hCross)) ∧
        RX.F cut = MMap.comp H (RX.F (cut+1)) D) :
    ∃ RY : SMTree.Envelope.AlgorithmRun H Y top,
      RY.I = RX.I ∧ RY.F = RX.F := by
  apply (actualRun_transport_iff_old_boring_compatible
    H X Y hXY top RX).mpr
  intro cut hCut hOldBoring
  obtain ⟨hNoNode,hNoMeet,D,hSkip,hCross,hF⟩ :=
    hPhysical cut hCut hOldBoring
  have hNewBoring :
      ¬ SMTree.Envelope.IsInterestingAt H
        (SMTree.Envelope.closure S (RX.I (cut+1)) Y) cut := by
    intro hInteresting
    unfold SMTree.Envelope.IsInterestingAt at hInteresting
    rcases hInteresting with hNode | hMeet | hNoSkip
    · exact hNoNode hNode
    · exact hNoMeet hMeet
    · exact hNoSkip ⟨D,hSkip,hCross⟩
  exact ⟨hNewBoring,D,hSkip,hCross,hF⟩

/-- Sharp geometric characterization of EXACT same-I same-total-F
actual run transport, using the UNIQUE old boring-step factor.

At an old-boring cut, the target complete source must have no
terminal I1 and no genuine same-component I2 meet; each actual
old step factor (which is unique by total monoid left cancellation)
must satisfy all new complete crossing equations. Equality of
old/new full physical crossing RELATIONS is not required. -/
theorem actualRun_transport_iff_old_boring_original_factor_extends
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    {S : STree T Label}
    (H : SMTree S)
    (X Y : Set T) (hXY : X ⊆ Y)
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun H X top) :
    (∃ RY : SMTree.Envelope.AlgorithmRun H Y top,
      RY.I = RX.I ∧ RY.F = RX.F) ↔
    (∀ cut : Nat, cut < top →
      ¬ SMTree.Envelope.IsInterestingAt H
        (SMTree.Envelope.closure S (RX.I (cut+1)) X) cut →
      (¬ ∃ z : T,
        z ∈ SMTree.Envelope.closure S (RX.I (cut+1)) Y ∧
        LevelTree.lev z = cut) ∧
      (¬ ∃ a : T,
        a ∈ SMTree.Envelope.closure S (RX.I (cut+1)) Y ∧
        ∃ b : T,
          b ∈ SMTree.Envelope.closure S (RX.I (cut+1)) Y ∧
          SMTree.Envelope.SameComponent a b ∧
          LevelTree.lev (LevelTree.meet a b) = cut) ∧
      ∀ (D : MMap H),
        D.map.SkipsOnly cut →
        (∀ ⦃z : T⦄,
          z ∈ SMTree.Envelope.closure S (RX.I (cut+1)) X →
          ∀ (hCross : cut < LevelTree.lev z),
            D (LevelTree.ancestor z cut (Nat.le_of_lt hCross)) =
              LevelTree.ancestor z (cut+1)
                (Nat.succ_le_iff.mpr hCross)) →
        RX.F cut = MMap.comp H (RX.F (cut+1)) D →
        (∀ ⦃z : T⦄,
          z ∈ SMTree.Envelope.closure S (RX.I (cut+1)) Y →
          ∀ (hCross : cut < LevelTree.lev z),
            D (LevelTree.ancestor z cut (Nat.le_of_lt hCross)) =
              LevelTree.ancestor z (cut+1)
                (Nat.succ_le_iff.mpr hCross))) := by
  constructor
  · intro hTransfer cut hCut hOldBoring
    have hCertified :=
      (actualRun_transport_iff_old_boring_compatible
        H X Y hXY top RX).mp hTransfer
        cut hCut hOldBoring
    obtain ⟨hNewBoring,Q,_hSkipQ,hNewCrossQ,hFactorQ⟩ :=
      hCertified
    have hNoI1 :
        ¬ ∃ z : T,
          z ∈ SMTree.Envelope.closure S (RX.I (cut+1)) Y ∧
          LevelTree.lev z = cut := by
      intro hI1
      exact hNewBoring (Or.inl hI1)
    have hNoI2 :
        ¬ ∃ a : T,
          a ∈ SMTree.Envelope.closure S (RX.I (cut+1)) Y ∧
          ∃ b : T,
            b ∈ SMTree.Envelope.closure S (RX.I (cut+1)) Y ∧
            SMTree.Envelope.SameComponent a b ∧
            LevelTree.lev (LevelTree.meet a b) = cut := by
      intro hI2
      exact hNewBoring (Or.inr (Or.inl hI2))
    refine ⟨hNoI1,hNoI2,?_⟩
    intro D _hSkipD _hOldCrossD hFactorD
    have hDQ : D = Q :=
      kpt_MMap_comp_left_cancel H (RX.F (cut+1)) D Q
        (hFactorD.symm.trans hFactorQ)
    simpa only [hDQ] using hNewCrossQ
  · intro hPhysical
    apply (actualRun_transport_iff_old_boring_compatible
      H X Y hXY top RX).mpr
    intro cut hCut hOldBoring
    obtain ⟨hNoI1,hNoI2,hFactorExtension⟩ :=
      hPhysical cut hCut hOldBoring
    obtain ⟨D,hSkipD,hOldCrossD,_hOldI,hFactorD⟩ :=
      RX.noninteresting_step cut hCut hOldBoring
    have hNewCrossD :=
      hFactorExtension D hSkipD hOldCrossD hFactorD
    have hNewBoring :
        ¬ SMTree.Envelope.IsInterestingAt H
          (SMTree.Envelope.closure S (RX.I (cut+1)) Y) cut := by
      intro hInteresting
      unfold SMTree.Envelope.IsInterestingAt at hInteresting
      rcases hInteresting with hI1 | hI2 | hNoSkip
      · exact hNoI1 hI1
      · exact hNoI2 hI2
      · exact hNoSkip ⟨D,hSkipD,hNewCrossD⟩
    exact ⟨hNewBoring,D,hSkipD,hNewCrossD,hFactorD⟩

end Kk
