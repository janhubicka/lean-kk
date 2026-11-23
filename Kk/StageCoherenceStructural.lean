import Kk.NumericHI2FullFork
import Kk.NumericHFullClosureSource
import Kk.TrackDPreCutStageSource
import Mathlib.Tactic

/-!
# Whole-original coherence excludes full structural cut events

English proof and independent reviews were published before this source:
`docs/stage_coherence_structural_lift_english_20261123.md`.

These are the actual meet, I1, strict-fork, and I2 source arguments with
complete old-to-next type coherence as the precise local input. The
concrete positive-generation construction supplies that input separately.
No ordinary zero-bit assumption, chosen-age verdict, or final-pool
identification is substituted for the complete physical source.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Two actual same-component originals which both genuinely reach cut+1
cannot meet exactly at cut when equal complete old types imply equal complete
next types for this pair. No closure-membership premise is needed. -/
theorem actual_coherent_cut_originals_meet_level_ne_cut
    (family : List (NormalizedForbidden 1 0 1))
    (A : EnumeratedPartialStructure 1 0 1)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (cut : Nat) (v w : Fin A.size)
    (hFreeV : cut+1 ≤ A.freeLevel v.val)
    (hFreeW : cut+1 ≤ A.freeLevel w.val)
    (hNext : A.partialTypeAt cut v.val = A.partialTypeAt cut w.val →
      A.partialTypeAt (cut+1) v.val = A.partialTypeAt (cut+1) w.val)
    (hComp : SMTree.Envelope.SameComponent
      (A.kptOriginal family hAvoid v)
      (A.kptOriginal family hAvoid w)) :
    LevelTree.lev
      (LevelTree.meet
        (A.kptOriginal family hAvoid v)
        (A.kptOriginal family hAvoid w)) ≠ cut := by
  let a : AdmissibleKptNode family := A.kptOriginal family hAvoid v
  let b : AdmissibleKptNode family := A.kptOriginal family hAvoid w
  intro hMeet
  have hLevA : cut < LevelTree.lev a := by
    change cut < A.freeLevel v.val
    omega
  have hLevB : cut < LevelTree.lev b := by
    change cut < A.freeLevel w.val
    omega
  have hMeetA :
      LevelTree.meet a b =
        LevelTree.ancestor a cut (Nat.le_of_lt hLevA) :=
    LevelTree.eq_ancestor_of_le
      (LevelTree.meet_le_left hComp) hMeet (Nat.le_of_lt hLevA)
  have hMeetB :
      LevelTree.meet a b =
        LevelTree.ancestor b cut (Nat.le_of_lt hLevB) :=
    LevelTree.eq_ancestor_of_le
      (LevelTree.meet_le_right hComp) hMeet (Nat.le_of_lt hLevB)
  have hOldAnc :
      LevelTree.ancestor a cut (Nat.le_of_lt hLevA) =
        LevelTree.ancestor b cut (Nat.le_of_lt hLevB) :=
    hMeetA.symm.trans hMeetB
  have hNextAncNe :
      LevelTree.ancestor a (cut+1)
        (Nat.succ_le_iff.mpr hLevA) ≠
      LevelTree.ancestor b (cut+1)
        (Nat.succ_le_iff.mpr hLevB) := by
    intro hNext
    have hCommon :
        LevelTree.ancestor a (cut+1)
          (Nat.succ_le_iff.mpr hLevA) ≤ LevelTree.meet a b := by
      apply LevelTree.le_meet
      · exact LevelTree.ancestor_le a (cut+1)
          (Nat.succ_le_iff.mpr hLevA)
      · rw [hNext]
        exact LevelTree.ancestor_le b (cut+1)
          (Nat.succ_le_iff.mpr hLevB)
    have hLev := LevelTree.level_le_of_le hCommon
    have hAncLev := LevelTree.level_ancestor
      a (cut+1) (Nat.succ_le_iff.mpr hLevA)
    have hMeetLevel : LevelTree.lev (LevelTree.meet a b) = cut := by
      simpa only [a, b] using hMeet
    have hImpossible : cut + 1 ≤ cut := by
      calc
        cut + 1 =
            LevelTree.lev
              (LevelTree.ancestor a (cut+1)
                (Nat.succ_le_iff.mpr hLevA)) := hAncLev.symm
        _ ≤ LevelTree.lev (LevelTree.meet a b) := hLev
        _ = cut := hMeetLevel
    omega
  have hOldA :
      (LevelTree.ancestor a cut (Nat.le_of_lt hLevA)).val =
        (⟨cut,A.partialTypeAt cut v.val⟩ :
          RawPartialTypeNode 1 0 1) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid v a (by exact le_rfl)
      cut (Nat.le_of_lt hLevA)
  have hOldB :
      (LevelTree.ancestor b cut (Nat.le_of_lt hLevB)).val =
        (⟨cut,A.partialTypeAt cut w.val⟩ :
          RawPartialTypeNode 1 0 1) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid w b (by exact le_rfl)
      cut (Nat.le_of_lt hLevB)
  have hPhysicalOld :
      A.partialTypeAt cut v.val = A.partialTypeAt cut w.val := by
    have hRaw :
        (⟨cut,A.partialTypeAt cut v.val⟩ :
          RawPartialTypeNode 1 0 1) =
        (⟨cut,A.partialTypeAt cut w.val⟩ :
          RawPartialTypeNode 1 0 1) := by
      calc
        (⟨cut,A.partialTypeAt cut v.val⟩ :
            RawPartialTypeNode 1 0 1) =
            (LevelTree.ancestor a cut (Nat.le_of_lt hLevA)).val :=
          hOldA.symm
        _ = (LevelTree.ancestor b cut (Nat.le_of_lt hLevB)).val :=
          congrArg Subtype.val hOldAnc
        _ = (⟨cut,A.partialTypeAt cut w.val⟩ :
            RawPartialTypeNode 1 0 1) := hOldB
    exact eq_of_heq (Sigma.mk.inj_iff.mp hRaw).2
  have hPhysicalNext :
      A.partialTypeAt (cut+1) v.val =
        A.partialTypeAt (cut+1) w.val :=
    hNext hPhysicalOld
  have hUpperA :
      (LevelTree.ancestor a (cut+1)
        (Nat.succ_le_iff.mpr hLevA)).val =
        (⟨cut+1,A.partialTypeAt (cut+1) v.val⟩ :
          RawPartialTypeNode 1 0 1) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid v a (by exact le_rfl)
      (cut+1) (Nat.succ_le_iff.mpr hLevA)
  have hUpperB :
      (LevelTree.ancestor b (cut+1)
        (Nat.succ_le_iff.mpr hLevB)).val =
        (⟨cut+1,A.partialTypeAt (cut+1) w.val⟩ :
          RawPartialTypeNode 1 0 1) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid w b (by exact le_rfl)
      (cut+1) (Nat.succ_le_iff.mpr hLevB)
  have hNextAnc :
      LevelTree.ancestor a (cut+1)
        (Nat.succ_le_iff.mpr hLevA) =
      LevelTree.ancestor b (cut+1)
        (Nat.succ_le_iff.mpr hLevB) := by
    apply Subtype.ext
    calc
      (LevelTree.ancestor a (cut+1)
          (Nat.succ_le_iff.mpr hLevA)).val =
          (⟨cut+1,A.partialTypeAt (cut+1) v.val⟩ :
            RawPartialTypeNode 1 0 1) := hUpperA
      _ = (⟨cut+1,A.partialTypeAt (cut+1) w.val⟩ :
            RawPartialTypeNode 1 0 1) := by rw [hPhysicalNext]
      _ = (LevelTree.ancestor b (cut+1)
          (Nat.succ_le_iff.mpr hLevB)).val := hUpperB.symm
  exact hNextAncNe hNextAnc


/-- Complete old-to-next coherence on the WHOLE actual original stage,
absence of a seed at the positive real cut, and genuine root-source
representation exclude every full I1 terminal at that cut. -/
theorem finiteNumericH_even_real_no_full_I1_of_coherent_stage
    (family : List (NormalizedForbidden 1 0 1))
    (K : AgeTestModel 1 0 1)
    (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (I : Set Nat)
    (X : Set (AdmissibleKptNode family))
    (U : Set (Fin (finiteNumericH K k N).size))
    (hSeeds : X ⊆
      ambientPrefixPool family (finiteNumericH K k N) hAvoid U)
    (idx g : Nat)
    (hPositive : 0 < hPosition k idx g)
    (hNoSeedAt : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ X ∧ LevelTree.lev z = hPosition k idx g)
    (hCoherent : ∀ v w : Fin (finiteNumericH K k N).size,
      v ∈ ambientStagePool (finiteNumericH K k N) U I →
      w ∈ ambientStagePool (finiteNumericH K k N) U I →
      hPosition k idx g+1 ≤ (finiteNumericH K k N).freeLevel v.val →
      hPosition k idx g+1 ≤ (finiteNumericH K k N).freeLevel w.val →
      (finiteNumericH K k N).partialTypeAt (hPosition k idx g) v.val =
        (finiteNumericH K k N).partialTypeAt (hPosition k idx g) w.val →
      (finiteNumericH K k N).partialTypeAt (hPosition k idx g+1) v.val =
        (finiteNumericH K k N).partialTypeAt (hPosition k idx g+1) w.val) :
    ¬ ∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) I X ∧
      LevelTree.lev z = hPosition k idx g := by
  classical
  let A : EnumeratedPartialStructure 1 0 1 := finiteNumericH K k N
  let cut : Nat := hPosition k idx g
  rintro ⟨z,hz,hLev⟩
  have hNotSeed : z ∉ X := by
    intro hx
    exact hNoSeedAt ⟨z,hx,hLev⟩
  obtain ⟨v,hv,w,hw,hComp,hMeet⟩ :=
    finiteNumericH_even_real_level_nonseed_is_original_meet
      family K k N hAvoid I X U hSeeds z idx g hLev hz hNotSeed
  have hMeetLevel :
      LevelTree.lev
        (LevelTree.meet
          (A.kptOriginal family hAvoid v)
          (A.kptOriginal family hAvoid w)) = cut := by
    simpa only [A, cut, hMeet] using hLev
  have hGeV : cut ≤ A.freeLevel v.val := by
    have h := LevelTree.level_le_of_le
      (LevelTree.meet_le_left hComp)
    change LevelTree.lev
      (LevelTree.meet
        (A.kptOriginal family hAvoid v)
        (A.kptOriginal family hAvoid w)) ≤ A.freeLevel v.val at h
    omega
  have hGeW : cut ≤ A.freeLevel w.val := by
    have h := LevelTree.level_le_of_le
      (LevelTree.meet_le_right hComp)
    change LevelTree.lev
      (LevelTree.meet
        (A.kptOriginal family hAvoid v)
        (A.kptOriginal family hAvoid w)) ≤ A.freeLevel w.val at h
    omega
  have hPositiveV : 0 < A.freeLevel v.val :=
    lt_of_lt_of_le hPositive hGeV
  have hPositiveW : 0 < A.freeLevel w.val :=
    lt_of_lt_of_le hPositive hGeW
  have hNotEvenV : A.freeLevel v.val ≠ cut :=
    finiteNumericH_positive_freeLevel_ne_realPosition
      K k N v.val idx g v.isLt hPositiveV
  have hNotEvenW : A.freeLevel w.val ≠ cut :=
    finiteNumericH_positive_freeLevel_ne_realPosition
      K k N w.val idx g w.isLt hPositiveW
  have hFreeV : cut+1 ≤ A.freeLevel v.val := by omega
  have hFreeW : cut+1 ≤ A.freeLevel w.val := by omega
  exact
    (actual_coherent_cut_originals_meet_level_ne_cut
      family A hAvoid cut v w hFreeV hFreeW
      (hCoherent v w hv hw hFreeV hFreeW) hComp) hMeetLevel


/-- Exhaustive physical representation of the SAME full source Z and
coherence on every eligible name in its original pool exclude strict full
old-equal/next-different forks. This does not require no-I1. -/
theorem full_kpt_cut_fork_false_of_coherent_full_physical_pool
    (family : List (NormalizedForbidden 1 0 1))
    (A : EnumeratedPartialStructure 1 0 1)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    {M : Nat}
    (original : Fin M → Fin A.size)
    (Z : Set (AdmissibleKptNode family))
    (hPool : ∀ z : AdmissibleKptNode family, z ∈ Z →
      ∃ v : Fin M, z ≤ A.kptOriginal family hAvoid (original v))
    (cut : Nat)
    (hCoherent : ∀ v w : Fin M,
      cut+1 ≤ A.freeLevel (original v).val →
      cut+1 ≤ A.freeLevel (original w).val →
      A.partialTypeAt cut (original v).val =
        A.partialTypeAt cut (original w).val →
      A.partialTypeAt (cut+1) (original v).val =
        A.partialTypeAt (cut+1) (original w).val) :
    ¬ KptFullCutFork family Z cut := by
  classical
  rintro ⟨a,ha,b,hb,hCa,hCb,hOldEq,hUpperNe⟩
  obtain ⟨va,hBelowA⟩ := hPool a ha
  obtain ⟨vb,hBelowB⟩ := hPool b hb
  have hFreeA : cut+1 ≤ A.freeLevel (original va).val := by
    have h := kptBelowOriginal_level_le_free
      family A hAvoid (original va) a hBelowA
    omega
  have hFreeB : cut+1 ≤ A.freeLevel (original vb).val := by
    have h := kptBelowOriginal_level_le_free
      family A hAvoid (original vb) b hBelowB
    omega
  have hAncOldA :
      (LevelTree.ancestor a cut (Nat.le_of_lt hCa)).val =
        (⟨cut,A.partialTypeAt cut (original va).val⟩ :
          RawPartialTypeNode 1 0 1) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid (original va) a hBelowA cut (Nat.le_of_lt hCa)
  have hAncOldB :
      (LevelTree.ancestor b cut (Nat.le_of_lt hCb)).val =
        (⟨cut,A.partialTypeAt cut (original vb).val⟩ :
          RawPartialTypeNode 1 0 1) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid (original vb) b hBelowB cut (Nat.le_of_lt hCb)
  have hOldRawA :
      kptFullOldAtCut a cut =
        some (⟨cut,A.partialTypeAt cut (original va).val⟩ :
          RawPartialTypeNode 1 0 1) := by
    calc
      kptFullOldAtCut a cut =
          some (LevelTree.ancestor a cut (Nat.le_of_lt hCa)).val :=
        (kpt_full_old_upper_types_of_crossing a cut hCa).1
      _ = some (⟨cut,A.partialTypeAt cut (original va).val⟩ :
          RawPartialTypeNode 1 0 1) :=
        congrArg some hAncOldA
  have hOldRawB :
      kptFullOldAtCut b cut =
        some (⟨cut,A.partialTypeAt cut (original vb).val⟩ :
          RawPartialTypeNode 1 0 1) := by
    calc
      kptFullOldAtCut b cut =
          some (LevelTree.ancestor b cut (Nat.le_of_lt hCb)).val :=
        (kpt_full_old_upper_types_of_crossing b cut hCb).1
      _ = some (⟨cut,A.partialTypeAt cut (original vb).val⟩ :
          RawPartialTypeNode 1 0 1) :=
        congrArg some hAncOldB
  have hSomeOld :
      some (⟨cut,A.partialTypeAt cut (original va).val⟩ :
          RawPartialTypeNode 1 0 1) =
        some (⟨cut,A.partialTypeAt cut (original vb).val⟩ :
          RawPartialTypeNode 1 0 1) :=
    hOldRawA.symm.trans (hOldEq.trans hOldRawB)
  have hPhysicalOld :
      A.partialTypeAt cut (original va).val =
        A.partialTypeAt cut (original vb).val := by
    have hRaw :
        (⟨cut,A.partialTypeAt cut (original va).val⟩ :
          RawPartialTypeNode 1 0 1) =
        (⟨cut,A.partialTypeAt cut (original vb).val⟩ :
          RawPartialTypeNode 1 0 1) :=
      Option.some.inj hSomeOld
    exact eq_of_heq (Sigma.mk.inj_iff.mp hRaw).2
  have hPhysicalUpper :
      A.partialTypeAt (cut+1) (original va).val =
        A.partialTypeAt (cut+1) (original vb).val :=
    hCoherent va vb hFreeA hFreeB hPhysicalOld
  have hAncUpA :
      (LevelTree.ancestor a (cut+1)
        (Nat.succ_le_iff.mpr hCa)).val =
        (⟨cut+1,A.partialTypeAt (cut+1) (original va).val⟩ :
          RawPartialTypeNode 1 0 1) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid (original va) a hBelowA (cut+1)
        (Nat.succ_le_iff.mpr hCa)
  have hAncUpB :
      (LevelTree.ancestor b (cut+1)
        (Nat.succ_le_iff.mpr hCb)).val =
        (⟨cut+1,A.partialTypeAt (cut+1) (original vb).val⟩ :
          RawPartialTypeNode 1 0 1) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid (original vb) b hBelowB (cut+1)
        (Nat.succ_le_iff.mpr hCb)
  have hNextA :
      kptFullUpperAtCut a cut =
        some (⟨cut+1,A.partialTypeAt (cut+1) (original va).val⟩ :
          RawPartialTypeNode 1 0 1) := by
    calc
      kptFullUpperAtCut a cut =
          some (LevelTree.ancestor a (cut+1)
            (Nat.succ_le_iff.mpr hCa)).val :=
        (kpt_full_old_upper_types_of_crossing a cut hCa).2
      _ = some (⟨cut+1,A.partialTypeAt (cut+1) (original va).val⟩ :
          RawPartialTypeNode 1 0 1) :=
        congrArg some hAncUpA
  have hNextB :
      kptFullUpperAtCut b cut =
        some (⟨cut+1,A.partialTypeAt (cut+1) (original vb).val⟩ :
          RawPartialTypeNode 1 0 1) := by
    calc
      kptFullUpperAtCut b cut =
          some (LevelTree.ancestor b (cut+1)
            (Nat.succ_le_iff.mpr hCb)).val :=
        (kpt_full_old_upper_types_of_crossing b cut hCb).2
      _ = some (⟨cut+1,A.partialTypeAt (cut+1) (original vb).val⟩ :
          RawPartialTypeNode 1 0 1) :=
        congrArg some hAncUpB
  have hUpperEq :
      kptFullUpperAtCut a cut = kptFullUpperAtCut b cut := by
    calc
      kptFullUpperAtCut a cut =
          some (⟨cut+1,A.partialTypeAt (cut+1) (original va).val⟩ :
            RawPartialTypeNode 1 0 1) := hNextA
      _ = some (⟨cut+1,A.partialTypeAt (cut+1) (original vb).val⟩ :
            RawPartialTypeNode 1 0 1) := by rw [hPhysicalUpper]
      _ = kptFullUpperAtCut b cut := hNextB.symm
  exact hUpperNe hUpperEq


/-- No-I1 is essential here: a self-meet at a cut-level terminal is an I2
test without a strict crossing fork. With no-I1, full physical coherence
excludes every actual I2 meet. -/
theorem full_kpt_no_i2_of_no_i1_and_coherent_full_physical_pool
    (family : List (NormalizedForbidden 1 0 1))
    (A : EnumeratedPartialStructure 1 0 1)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    {M : Nat}
    (original : Fin M → Fin A.size)
    (Z : Set (AdmissibleKptNode family))
    (hPool : ∀ z : AdmissibleKptNode family, z ∈ Z →
      ∃ v : Fin M, z ≤ A.kptOriginal family hAvoid (original v))
    (cut : Nat)
    (hCoherent : ∀ v w : Fin M,
      cut+1 ≤ A.freeLevel (original v).val →
      cut+1 ≤ A.freeLevel (original w).val →
      A.partialTypeAt cut (original v).val =
        A.partialTypeAt cut (original w).val →
      A.partialTypeAt (cut+1) (original v).val =
        A.partialTypeAt (cut+1) (original w).val)
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ Z ∧ LevelTree.lev z = cut) :
    ¬ ∃ a : AdmissibleKptNode family, a ∈ Z ∧
      ∃ b : AdmissibleKptNode family, b ∈ Z ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut := by
  intro hI2
  have hFork : KptFullCutFork family Z cut :=
    (kpt_no_I1_I2_iff_complete_full_fork family Z cut hNoI1).mp hI2
  exact (full_kpt_cut_fork_false_of_coherent_full_physical_pool
    family A hAvoid original Z hPool cut hCoherent) hFork


/-- The finite enumeration of the COMPLETE actual original stage transports
coherence to both structural tests. All closure nodes have names in this same
pool, and original-meet witnesses are covered before no-I1/no-I2 is proved.
The level set I is arbitrary, so the literal pre-cut AlgorithmRun stage can
be substituted without an assumption about its final selected levels. -/
theorem finiteNumericH_even_real_no_full_I1_I2_of_coherent_stage
    (family : List (NormalizedForbidden 1 0 1))
    (K : AgeTestModel 1 0 1) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid (U : Set (Fin N)))
    (I : Set Nat) (idx g : Nat)
    (hPositive : 0 < hPosition k idx g)
    (hNoSeedAt : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ X ∧ LevelTree.lev z = hPosition k idx g)
    (hCoherent : ∀ v w : Fin (hStageOriginals K k N U I).card,
      hPosition k idx g+1 ≤ (finiteNumericH K k N).freeLevel
        (hOriginalName (hStageOriginals K k N U I) v).val →
      hPosition k idx g+1 ≤ (finiteNumericH K k N).freeLevel
        (hOriginalName (hStageOriginals K k N U I) w).val →
      (finiteNumericH K k N).partialTypeAt (hPosition k idx g)
          (hOriginalName (hStageOriginals K k N U I) v).val =
        (finiteNumericH K k N).partialTypeAt (hPosition k idx g)
          (hOriginalName (hStageOriginals K k N U I) w).val →
      (finiteNumericH K k N).partialTypeAt (hPosition k idx g+1)
          (hOriginalName (hStageOriginals K k N U I) v).val =
        (finiteNumericH K k N).partialTypeAt (hPosition k idx g+1)
          (hOriginalName (hStageOriginals K k N U I) w).val) :
    let Z : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family) I X
    (¬ ∃ z : AdmissibleKptNode family,
      z ∈ Z ∧ LevelTree.lev z = hPosition k idx g) ∧
    (¬ ∃ a : AdmissibleKptNode family, a ∈ Z ∧
      ∃ b : AdmissibleKptNode family, b ∈ Z ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = hPosition k idx g) := by
  classical
  let A : EnumeratedPartialStructure 1 0 1 := finiteNumericH K k N
  let cut : Nat := hPosition k idx g
  let Stage : Finset (Fin N) := hStageOriginals K k N U I
  let original : Fin Stage.card → Fin N := hOriginalName Stage
  let Z : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family) I X
  have hCoherentPool : ∀ v w : Fin Stage.card,
      cut+1 ≤ A.freeLevel (original v).val →
      cut+1 ≤ A.freeLevel (original w).val →
      A.partialTypeAt cut (original v).val =
        A.partialTypeAt cut (original w).val →
      A.partialTypeAt (cut+1) (original v).val =
        A.partialTypeAt (cut+1) (original w).val := hCoherent
  have hMember : ∀ v : Fin N,
      v ∈ ambientStagePool A (U : Set (Fin N)) I → v ∈ Stage := by
    intro v hv
    have hv' : v ∈ U ∨ (v.val ∈ I ∧ 0 < A.freeLevel v.val) := by
      rcases hv with hRoot | ⟨hSelected,hFree⟩
      · exact Or.inl (Finset.mem_coe.mp hRoot)
      · exact Or.inr ⟨hSelected,hFree⟩
    simpa only [Stage,hStageOriginals,Finset.mem_filter,
      Finset.mem_univ,true_and,Set.mem_ofPred_eq] using hv'
  have hCoherentAmbient : ∀ v w : Fin A.size,
      v ∈ ambientStagePool A (U : Set (Fin N)) I →
      w ∈ ambientStagePool A (U : Set (Fin N)) I →
      cut+1 ≤ A.freeLevel v.val → cut+1 ≤ A.freeLevel w.val →
      A.partialTypeAt cut v.val = A.partialTypeAt cut w.val →
      A.partialTypeAt (cut+1) v.val = A.partialTypeAt (cut+1) w.val := by
    intro v w hv hw hFreeV hFreeW hOld
    let iv : Fin Stage.card := Stage.equivFin ⟨v,hMember v hv⟩
    let iw : Fin Stage.card := Stage.equivFin ⟨w,hMember w hw⟩
    have hNameV : original iv = v := by
      simp [original,hOriginalName,iv] <;> rfl
    have hNameW : original iw = w := by
      simp [original,hOriginalName,iw] <;> rfl
    have hPair := hCoherentPool iv iw
    rw [hNameV,hNameW] at hPair
    exact hPair hFreeV hFreeW hOld
  have hNoI1 : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ Z ∧ LevelTree.lev z = cut :=
    finiteNumericH_even_real_no_full_I1_of_coherent_stage
      family K k N hAvoid I X (U : Set (Fin N)) hX
      idx g hPositive hNoSeedAt hCoherentAmbient
  have hPool : ∀ z : AdmissibleKptNode family, z ∈ Z →
      ∃ v : Fin Stage.card,
        z ≤ A.kptOriginal family hAvoid (original v) := by
    intro z hz
    obtain ⟨v,hv,hBelow⟩ :=
      finiteNumericH_stage_closure_represented_by_stage_originals
        family K k N hAvoid U X hX I z hz
    let i : Fin Stage.card := Stage.equivFin ⟨v,hv⟩
    have hName : original i = v := by
      simp [original,hOriginalName,i] <;> rfl
    refine ⟨i,?_⟩
    simpa only [hName] using hBelow
  have hNoI2 : ¬ ∃ a : AdmissibleKptNode family, a ∈ Z ∧
      ∃ b : AdmissibleKptNode family, b ∈ Z ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut :=
    full_kpt_no_i2_of_no_i1_and_coherent_full_physical_pool
      family A hAvoid original Z hPool cut hCoherentPool hNoI1
  exact ⟨hNoI1,hNoI2⟩

#print axioms Kk.actual_coherent_cut_originals_meet_level_ne_cut
#print axioms Kk.finiteNumericH_even_real_no_full_I1_of_coherent_stage
#print axioms Kk.full_kpt_cut_fork_false_of_coherent_full_physical_pool
#print axioms Kk.full_kpt_no_i2_of_no_i1_and_coherent_full_physical_pool
#print axioms Kk.finiteNumericH_even_real_no_full_I1_I2_of_coherent_stage

end Kk
