import Kk.BareRootOldTailRetention
import Kk.NumericHStructuralCutClassifier
import Kk.FullPhysicalCrossingRelation
import Mathlib.Tactic

/-!
# Track C: cut-visible Kpt closure survives inherited lower parameter levels

English-first proof and hostile audit:
  docs/track_c_cut_visible_closure_english_audit.md

The old full-closure absorption lemma imposed the potentially VACUOUS
hypothesis that every inherited selected level is above the tested cut.
Here only the old selected TAIL above the cut must be present in the
new pre-cut selected set.

Underlying reason: every successor parameter has level strictly
BELOW its selected generating level, and a meet cannot increase level.
Nodes generated at inherited levels q <= cut cannot appear AT or ABOVE
cut. Thus closure sets can differ below the cut but have IDENTICAL
cut-visible full dependent L+ records, including E and I2 forks.

This is local to two sources on the SAME successor tree, evaluated
at the SAME new-run selected-level set. It does NOT compare the
AlgorithmRun decisions of a bare-root and a full-inherited-root run,
derive a global resolved diary, or prove the common labelled orbit.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

universe u v

/-- Adjoin ALL nodes below a cut to a meet- and J-parameter-closed
set C. The result is parameter-closed over ANY level set I whose
levels above the cut lie in J.

At i <= cut, every generated parameter has level strictly less
than i, hence stays in the added low region. At i > cut, an input
node in the low region is impossible, so we use J-closure of C. -/
theorem envelope_union_low_closed
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    (S : STree T Label)
    (I J : Set Nat) (C : Set T) (cut : Nat)
    (hMeet : SMTree.Envelope.MeetClosed C)
    (hParam : SMTree.Envelope.ParameterClosedOver S C J)
    (hTail : ∀ i : Nat, i ∈ I → cut < i → i ∈ J) :
    SMTree.Envelope.MeetClosed
        (C ∪ {z : T | LevelTree.lev z < cut}) ∧
    SMTree.Envelope.ParameterClosedOver S
        (C ∪ {z : T | LevelTree.lev z < cut}) I := by
  constructor
  · intro a b ha hb hab
    rcases ha with haC | haLow
    · rcases hb with hbC | hbLow
      · exact Or.inl (hMeet haC hbC hab)
      · right
        have hlev :
            LevelTree.lev (LevelTree.meet a b) ≤ LevelTree.lev b :=
          LevelTree.level_le_of_le (LevelTree.meet_le_right hab)
        exact lt_of_le_of_lt hlev hbLow
    · right
      have hlev :
          LevelTree.lev (LevelTree.meet a b) ≤ LevelTree.lev a :=
        LevelTree.level_le_of_le (LevelTree.meet_le_left hab)
      exact lt_of_le_of_lt hlev haLow
  · intro a ha i hi hia p label hs x hx
    have hxlev : LevelTree.lev x < i := by
      have h := S.parameter_level_lt hs hx
      have haLev :
          LevelTree.lev (LevelTree.ancestor a i (Nat.le_of_lt hia)) = i :=
        LevelTree.level_ancestor a i (Nat.le_of_lt hia)
      rw [haLev] at h
      exact h
    by_cases hHigh : cut < i
    · rcases ha with haC | haLow
      · exact Or.inl (hParam haC (hTail i hi hHigh) hia hs hx)
      · have hContra : False := by
          change LevelTree.lev a < cut at haLow
          omega
        exact False.elim hContra
    · right
      exact lt_of_lt_of_le hxlev (Nat.le_of_not_gt hHigh)

/-- The high-level portion of closure_I X is included in closure_J Y
whenever X ⊆ Y and ALL selected I-levels strictly above cut belong
to J. Old selected levels AT or BELOW cut need not be retained.

The high-level region includes level=cut so this preserves real I1
nodes, not only crossing witnesses. -/
theorem envelope_closure_high_mono_of_tail
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    (S : STree T Label)
    (I J : Set Nat) (X Y : Set T) (cut : Nat)
    (hXY : X ⊆ Y)
    (hTail : ∀ i : Nat, i ∈ I → cut < i → i ∈ J) :
    ∀ z : T,
      z ∈ SMTree.Envelope.closure S I X →
      cut ≤ LevelTree.lev z →
      z ∈ SMTree.Envelope.closure S J Y := by
  let C : Set T := SMTree.Envelope.closure S J Y
  let W : Set T := C ∪ {z : T | LevelTree.lev z < cut}
  have hClosed :
      SMTree.Envelope.MeetClosed W ∧
      SMTree.Envelope.ParameterClosedOver S W I :=
    envelope_union_low_closed S I J C cut
      (SMTree.Envelope.closure_meetClosed S J Y)
      (SMTree.Envelope.closure_parameterClosed S J Y)
      hTail
  have hSeed : X ⊆ W := by
    intro z hz
    exact Or.inl
      ((SMTree.Envelope.subset_closure S J Y) (hXY hz))
  have hCover : SMTree.Envelope.closure S I X ⊆ W :=
    SMTree.Envelope.closure_minimal S I X W
      hSeed hClosed.1 hClosed.2
  intro z hz hLev
  rcases hCover hz with hzC | hzLow
  · exact hzC
  · exact False.elim ((Nat.not_lt_of_ge hLev) hzLow)

/-- Nonvacuous HIGH-VISIBLE source absorption. If I and J agree on
the forward use of selected levels ABOVE c, inherited closure_I X
may be preinserted before the new step without changing ANY node
of level >= c in its J-closure.

The unfiltered closure sets need NOT be equal BELOW the cut. -/
theorem envelope_closure_high_absorbs_old_closure
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    (S : STree T Label)
    (I J : Set Nat) (X O : Set T) (cut : Nat)
    (hTail : ∀ i : Nat, i ∈ I → cut < i → i ∈ J) :
    ∀ z : T, cut ≤ LevelTree.lev z →
      (z ∈ SMTree.Envelope.closure S J
        (SMTree.Envelope.closure S I X ∪ O) ↔
       z ∈ SMTree.Envelope.closure S J (X ∪ O)) := by
  intro z hzLev
  let C : Set T := SMTree.Envelope.closure S J (X ∪ O)
  let W : Set T := C ∪ {w : T | LevelTree.lev w < cut}
  have hCWJ :
      SMTree.Envelope.MeetClosed W ∧
      SMTree.Envelope.ParameterClosedOver S W J :=
    envelope_union_low_closed S J J C cut
      (SMTree.Envelope.closure_meetClosed S J (X ∪ O))
      (SMTree.Envelope.closure_parameterClosed S J (X ∪ O))
      (by intro i hi _; exact hi)
  have hCWI :
      SMTree.Envelope.MeetClosed W ∧
      SMTree.Envelope.ParameterClosedOver S W I :=
    envelope_union_low_closed S I J C cut
      (SMTree.Envelope.closure_meetClosed S J (X ∪ O))
      (SMTree.Envelope.closure_parameterClosed S J (X ∪ O))
      hTail
  have hX : X ⊆ W := by
    intro x hx
    exact Or.inl ((SMTree.Envelope.subset_closure S J (X ∪ O))
      (Or.inl hx))
  have hOld : SMTree.Envelope.closure S I X ⊆ W :=
    SMTree.Envelope.closure_minimal S I X W hX hCWI.1 hCWI.2
  have hSeed : SMTree.Envelope.closure S I X ∪ O ⊆ W := by
    intro x hx
    rcases hx with hxOld | hxO
    · exact hOld hxOld
    · exact Or.inl ((SMTree.Envelope.subset_closure S J (X ∪ O))
        (Or.inr hxO))
  have hOldFull :
      SMTree.Envelope.closure S J
          (SMTree.Envelope.closure S I X ∪ O) ⊆ W :=
    SMTree.Envelope.closure_minimal S J
      (SMTree.Envelope.closure S I X ∪ O)
      W hSeed hCWJ.1 hCWJ.2
  have hXSeed :
      X ∪ O ⊆ SMTree.Envelope.closure S I X ∪ O := by
    intro x hx
    rcases hx with hxX | hxO
    · exact Or.inl ((SMTree.Envelope.subset_closure S I X) hxX)
    · exact Or.inr hxO
  have hBareFull :
      SMTree.Envelope.closure S J (X ∪ O) ⊆
      SMTree.Envelope.closure S J
        (SMTree.Envelope.closure S I X ∪ O) :=
    envelope_closure_mono_seeds_and_levels
      S J J (X ∪ O) (SMTree.Envelope.closure S I X ∪ O)
      (by intro i hi; exact hi) hXSeed
  constructor
  · intro hOldZ
    rcases hOldFull hOldZ with hC | hLow
    · exact hC
    · exact False.elim ((Nat.not_lt_of_ge hzLev) hLow)
  · exact hBareFull

/-- The three actual finite Kpt structural/crossing objects visible
at cut c depend ONLY on closure members of level >= c.

No no-I2 assumption: the full crossing relation may contain several
different COMPLETE upper L+ outputs for one old source. -/
theorem kpt_cut_visible_same_structural_and_full_crossing
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z W : Set (AdmissibleKptNode family))
    (cut : Nat)
    (hVisible : ∀ z : AdmissibleKptNode family,
      cut ≤ LevelTree.lev z → (z ∈ Z ↔ z ∈ W)) :
    (KptI1AtCut family Z cut ↔ KptI1AtCut family W cut) ∧
    (KptI2MeetAtCut family Z cut ↔ KptI2MeetAtCut family W cut) ∧
    (FullPhysicalClosureCrossing family Z cut =
      FullPhysicalClosureCrossing family W cut) := by
  constructor
  · constructor
    · rintro ⟨z, hz, hLev⟩
      exact ⟨z, (hVisible z (by omega)).mp hz, hLev⟩
    · rintro ⟨z, hz, hLev⟩
      exact ⟨z, (hVisible z (by omega)).mpr hz, hLev⟩
  constructor
  · constructor
    · rintro ⟨a, ha, b, hb, hComp, hMeet⟩
      have haLev : cut ≤ LevelTree.lev a := by
        have h := LevelTree.level_le_of_le
          (LevelTree.meet_le_left hComp)
        omega
      have hbLev : cut ≤ LevelTree.lev b := by
        have h := LevelTree.level_le_of_le
          (LevelTree.meet_le_right hComp)
        omega
      exact ⟨a, (hVisible a haLev).mp ha,
        b, (hVisible b hbLev).mp hb, hComp, hMeet⟩
    · rintro ⟨a, ha, b, hb, hComp, hMeet⟩
      have haLev : cut ≤ LevelTree.lev a := by
        have h := LevelTree.level_le_of_le
          (LevelTree.meet_le_left hComp)
        omega
      have hbLev : cut ≤ LevelTree.lev b := by
        have h := LevelTree.level_le_of_le
          (LevelTree.meet_le_right hComp)
        omega
      exact ⟨a, (hVisible a haLev).mpr ha,
        b, (hVisible b hbLev).mpr hb, hComp, hMeet⟩
  · ext p
    constructor
    · rintro ⟨z, hz, hCut, hOld, hUpper⟩
      exact ⟨z, (hVisible z (by omega)).mp hz,
        hCut, hOld, hUpper⟩
    · rintro ⟨z, hz, hCut, hOld, hUpper⟩
      exact ⟨z, (hVisible z (by omega)).mpr hz,
        hCut, hOld, hUpper⟩

/-- Track C physical consequence at EVERY real old cut c<oldTop,
even if the old selected run contains levels 0,...,c.

Rold is a genuine physical Kpt AlgorithmRun on X and has an ACTUAL
old top seed; Rnew is a genuine higher-top run on the corrected
inherited-full seed source closure_I X ∪ O. O consists of ACTUAL new
numerical H+ Kpt ORIGINAL nodes, not their ancestor prefix pool.

The earlier nonvacuous cross-height tail retention theorem supplies
all old q>c in Rnew.I(c+1). The generic graded closure theorem then
gives equality on EVERY real node of level >= c, and hence I1,
I2 and the complete chosen-source old/upper L+ crossing relation.

We do NOT claim the bare-seed AlgorithmRun and this full-seed
AlgorithmRun select the same interesting levels, nor that two
different diary OCCURRENCES have a common labelled inverse orbit. -/
theorem finiteNumericH_newRoot_run_cut_visible_absorption
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (Iunused : Unit)
    (X : Set (AdmissibleKptNode family))
    (W : Set (Fin M))
    (oldTop newTop : Nat)
    (hTopLe : oldTop ≤ newTop)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = oldTop)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (Rnew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (Rold.I 0) X ∪
         ((fun w : Fin M =>
           (finiteNumericH L k M).kptOriginal family hAvoid w) '' W))
      newTop)
    (cut : Nat) (hCut : cut < oldTop) :
    let O : Set (AdmissibleKptNode family) :=
      ((fun w : Fin M =>
        (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)
    let Zfull : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (Rnew.I (cut+1))
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (Rold.I 0) X ∪ O)
    let Zbare : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (Rnew.I (cut+1)) (X ∪ O)
    (∀ z, cut ≤ LevelTree.lev z → (z ∈ Zfull ↔ z ∈ Zbare)) ∧
    (KptI1AtCut family Zfull cut ↔ KptI1AtCut family Zbare cut) ∧
    (KptI2MeetAtCut family Zfull cut ↔
      KptI2MeetAtCut family Zbare cut) ∧
    (FullPhysicalClosureCrossing family Zfull cut =
      FullPhysicalClosureCrossing family Zbare cut) := by
  let O : Set (AdmissibleKptNode family) :=
    ((fun w : Fin M =>
      (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)
  let Yfull : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (Rold.I 0) X ∪ O
  let J := Rnew.I (cut+1)
  let Zfull : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family) J Yfull
  let Zbare : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family) J (X ∪ O)
  have hSeed : X ⊆ Yfull := by
    intro z hz
    exact Or.inl
      ((SMTree.Envelope.subset_closure
        (admissibleKptSTree family) (Rold.I 0) X) hz)
  have hTail :
      ∀ q, q ∈ Rold.I 0 → cut < q → q ∈ J :=
    envelope_algorithmRun_retains_old_selected_tail
      (normalizedKptSMTree family)
      X Yfull hSeed oldTop newTop hTopLe hTopSeed
      Rold Rnew cut hCut
  have hVisible :
      ∀ z : AdmissibleKptNode family,
        cut ≤ LevelTree.lev z → (z ∈ Zfull ↔ z ∈ Zbare) :=
    envelope_closure_high_absorbs_old_closure
      (admissibleKptSTree family)
      (Rold.I 0) J X O cut hTail
  have hStruct :=
    kpt_cut_visible_same_structural_and_full_crossing
      family Zfull Zbare cut hVisible
  dsimp only
  exact ⟨hVisible, hStruct.1, hStruct.2.1, hStruct.2.2⟩

end Kk
