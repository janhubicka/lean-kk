import Kk.AlgorithmRunCrossHeightMonotonicity
import Kk.NumericHStructuralCutClassifier
import Kk.FullPhysicalCrossingRelation
import Mathlib.Tactic

/-!
# Track C: cutwise Kpt source stratification for ALL new-root cut levels

English proof and 20 hostile checks committed BEFORE this Lean source:
  docs/track_c_high_cut_stratification_english_audit.md

The repaired next seed Y = closure_I X ∪ NEW ACTUAL Kpt originals
may preinsert lower parameter nodes from old selected levels i≤cut.
But the successor-tree parameter_level_lt theorem proves these
parameters have level <i≤cut; componentwise meet cannot increase
levels. Hence they cannot affect any node of level >=cut in
the NEW pre-cut closure, provided all old selected levels i>cut
belong to the new higher selected-level set J.

This proves a stronger result than full closure absorption:
  membership in the two closures agrees ABOVE THE TESTED CUT,
even if the closures disagree at some lower levels.

Consequently the TRUE cut I1 and I2 predicates and the entire
physical old/upper dependent L+ crossing relation agree EXACTLY.

The independently proved monotonicity of actual AlgorithmRuns
across increased scan heights gives retention of all old selected
levels (under a GENUINE old top seed). Thus the needed higher-level
inclusion is automatic AT EVERY tested new cut, with NO requirement
that cut be below the smallest old selected level.

This DOES NOT assert that a new root fails to generate new true
I1/I2/I3 events; it only eliminates ARTIFICIAL events caused by
preinsertion of the inherited old closure. No bounded full diary
or common labelled inverse-source orbit is claimed.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

universe u v

/-- At a fixed cut p, adding old meet/parameter closure to the seed
set does not change ANY node at or ABOVE cut in the final J-closure,
provided every old parameter-generating level i>p remains in J.

The crucial invariant is C ∪ {z | lev z<p}, where
C=closure_J(X∪O). It is closed under meet, and under both I
and J parameter generation:
  * a parameter of base level i≤p lies STRICTLY below p;
  * for i>p its level belongs to J, so the generator lies in C;
  * a low-level input cannot have a base level i>p.
No false distributivity of closure over union is assumed.

This is the genuine STree meet/parameter closure, not graph
selected-front or arbitrary downward prefix closure. -/
theorem envelope_closure_highCut_absorbs_lower_levels
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    (S : STree T Label)
    (I J : Set Nat)
    (X O : Set T)
    (cut : Nat)
    (hHigh : ∀ i : Nat, i ∈ I → cut < i → i ∈ J) :
    ∀ z : T, cut ≤ LevelTree.lev z →
      (z ∈ SMTree.Envelope.closure S J
          (SMTree.Envelope.closure S I X ∪ O) ↔
       z ∈ SMTree.Envelope.closure S J (X ∪ O)) := by
  let C : Set T := SMTree.Envelope.closure S J (X ∪ O)
  let Low : Set T := {z : T | LevelTree.lev z < cut}
  let D : Set T := C ∪ Low
  have hMeet : SMTree.Envelope.MeetClosed D := by
    intro a b ha hb hab
    change LevelTree.meet a b ∈ C ∪ Low
    change a ∈ C ∪ Low at ha
    change b ∈ C ∪ Low at hb
    rcases ha with haC | haLow
    · rcases hb with hbC | hbLow
      · exact Or.inl
          ((SMTree.Envelope.closure_meetClosed S J (X ∪ O))
            haC hbC hab)
      · right
        have hLev :=
          LevelTree.level_le_of_le (LevelTree.meet_le_right hab)
        change LevelTree.lev b < cut at hbLow
        change LevelTree.lev (LevelTree.meet a b) < cut
        omega
    · right
      have hLev :=
        LevelTree.level_le_of_le (LevelTree.meet_le_left hab)
      change LevelTree.lev a < cut at haLow
      change LevelTree.lev (LevelTree.meet a b) < cut
      omega
  have hParam : ∀ Q : Set Nat,
      (∀ i : Nat, i ∈ Q → cut < i → i ∈ J) →
      SMTree.Envelope.ParameterClosedOver S D Q := by
    intro Q hQ
    intro a ha i hi hia p c hs x hx
    have hParamLev : LevelTree.lev x < i := by
      have hxi := S.parameter_level_lt hs hx
      have hbase :=
        LevelTree.level_ancestor a i (Nat.le_of_lt hia)
      rw [hbase] at hxi
      exact hxi
    change x ∈ C ∪ Low
    by_cases hLeCut : i ≤ cut
    · exact Or.inr (by
        change LevelTree.lev x < cut
        omega)
    · have hCutI : cut < i := by omega
      have hiJ : i ∈ J := hQ i hi hCutI
      change a ∈ C ∪ Low at ha
      rcases ha with haC | haLow
      · exact Or.inl
          ((SMTree.Envelope.closure_parameterClosed S J (X ∪ O))
            haC hiJ hia hs hx)
      · have hLowLev : LevelTree.lev a < cut := haLow
        omega
  have hSeedX : X ⊆ D := by
    intro z hz
    exact Or.inl
      ((SMTree.Envelope.subset_closure S J (X ∪ O))
        (Or.inl hz))
  have hOld : SMTree.Envelope.closure S I X ⊆ D :=
    SMTree.Envelope.closure_minimal S I X D
      hSeedX hMeet (hParam I hHigh)
  have hUnion : SMTree.Envelope.closure S I X ∪ O ⊆ D := by
    intro z hz
    rcases hz with hzOld | hzO
    · exact hOld hzOld
    · exact Or.inl
        ((SMTree.Envelope.subset_closure S J (X ∪ O))
          (Or.inr hzO))
  have hEntire :
      SMTree.Envelope.closure S J
          (SMTree.Envelope.closure S I X ∪ O) ⊆ D :=
    SMTree.Envelope.closure_minimal
      S J (SMTree.Envelope.closure S I X ∪ O)
      D hUnion hMeet (hParam J (fun _ hi _ => hi))
  have hReverse :
      C ⊆ SMTree.Envelope.closure S J
        (SMTree.Envelope.closure S I X ∪ O) := by
    apply SMTree.Envelope.closure_minimal
      S J (X ∪ O)
      (SMTree.Envelope.closure S J
        (SMTree.Envelope.closure S I X ∪ O))
    · intro z hz
      apply SMTree.Envelope.subset_closure
        S J (SMTree.Envelope.closure S I X ∪ O)
      rcases hz with hzX | hzO
      · exact Or.inl
          ((SMTree.Envelope.subset_closure S I X) hzX)
      · exact Or.inr hzO
    · exact SMTree.Envelope.closure_meetClosed
        S J (SMTree.Envelope.closure S I X ∪ O)
    · exact SMTree.Envelope.closure_parameterClosed
        S J (SMTree.Envelope.closure S I X ∪ O)
  intro z hzHigh
  constructor
  · intro hz
    rcases hEntire hz with hzC | hzLow
    · exact hzC
    · have hLow : LevelTree.lev z < cut := hzLow
      omega
  · exact hReverse

/-- Any two TRUE Kpt node sets which agree AT AND ABOVE a cut
have exactly the same genuine I1, I2 and COMPLETE choice-free
physical old/upper dependent L+ crossing relation at that cut.

I2 meet witnesses must lie at/above the cut since meet<=both.
Every physical crossing witness lies strictly ABOVE the cut.
No assigned functional F is postulated at I2 forks. -/
theorem kpt_highCut_membership_equiv_preserves_full_events
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z C : Set (AdmissibleKptNode family))
    (cut : Nat)
    (hSame : ∀ z : AdmissibleKptNode family,
      cut ≤ LevelTree.lev z → (z ∈ Z ↔ z ∈ C)) :
    (KptI1AtCut family Z cut ↔ KptI1AtCut family C cut) ∧
    (KptI2MeetAtCut family Z cut ↔ KptI2MeetAtCut family C cut) ∧
    FullPhysicalClosureCrossing family Z cut =
      FullPhysicalClosureCrossing family C cut := by
  have hI1 : KptI1AtCut family Z cut ↔
      KptI1AtCut family C cut := by
    constructor
    · rintro ⟨z,hz,hLev⟩
      exact ⟨z,(hSame z (by omega)).mp hz,hLev⟩
    · rintro ⟨z,hz,hLev⟩
      exact ⟨z,(hSame z (by omega)).mpr hz,hLev⟩
  have hI2 : KptI2MeetAtCut family Z cut ↔
      KptI2MeetAtCut family C cut := by
    constructor
    · rintro ⟨a,ha,b,hb,hComp,hLev⟩
      have haHigh : cut ≤ LevelTree.lev a := by
        have hm :=
          LevelTree.level_le_of_le (LevelTree.meet_le_left hComp)
        omega
      have hbHigh : cut ≤ LevelTree.lev b := by
        have hm :=
          LevelTree.level_le_of_le (LevelTree.meet_le_right hComp)
        omega
      exact ⟨a,(hSame a haHigh).mp ha,
        b,(hSame b hbHigh).mp hb,hComp,hLev⟩
    · rintro ⟨a,ha,b,hb,hComp,hLev⟩
      have haHigh : cut ≤ LevelTree.lev a := by
        have hm :=
          LevelTree.level_le_of_le (LevelTree.meet_le_left hComp)
        omega
      have hbHigh : cut ≤ LevelTree.lev b := by
        have hm :=
          LevelTree.level_le_of_le (LevelTree.meet_le_right hComp)
        omega
      exact ⟨a,(hSame a haHigh).mpr ha,
        b,(hSame b hbHigh).mpr hb,hComp,hLev⟩
  have hPhysical :
      FullPhysicalClosureCrossing family Z cut =
        FullPhysicalClosureCrossing family C cut := by
    ext pair
    constructor
    · rintro ⟨z,hz,hCross,hOld,hUpper⟩
      exact ⟨z,(hSame z (Nat.le_of_lt hCross)).mp hz,
        hCross,hOld,hUpper⟩
    · rintro ⟨z,hz,hCross,hOld,hUpper⟩
      exact ⟨z,(hSame z (Nat.le_of_lt hCross)).mpr hz,
        hCross,hOld,hUpper⟩
  exact ⟨hI1,hI2,hPhysical⟩

/-- The CORRECTED physical new-root seed set's actual pre-cut
I1/I2 and full old/upper dependent L+ relation agree with the
bare old-original plus new-original source, provided only the
inherited selected levels STRICTLY ABOVE the cut lie in the
new run's higher selected-level set.

Old selected levels AT OR BELOW the cut need not be present:
their possible extra parameter nodes all have lower level,
so cannot affect the cut's real structural sources. -/
theorem finiteNumericH_newRoot_run_highCut_full_events_absorb
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (I : Set Nat)
    (X : Set (AdmissibleKptNode family))
    (W : Set (Fin M))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
      (finiteNumericH_physicalExtendedSeeds
        family L k M hAvoid I X W) top)
    (cut : Nat) (hCut : cut < top)
    (hRetainedHigher : ∀ i : Nat, i ∈ I →
      cut < i → i ∈ R.I (cut+1)) :
    let O : Set (AdmissibleKptNode family) :=
      ((fun w : Fin M =>
        (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)
    let Z : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1))
        (finiteNumericH_physicalExtendedSeeds family
          L k M hAvoid I X W)
    let C : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1)) (X ∪ O)
    (KptI1AtCut family Z cut ↔ KptI1AtCut family C cut) ∧
    (KptI2MeetAtCut family Z cut ↔ KptI2MeetAtCut family C cut) ∧
    FullPhysicalClosureCrossing family Z cut =
      FullPhysicalClosureCrossing family C cut := by
  let O : Set (AdmissibleKptNode family) :=
    ((fun w : Fin M =>
      (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)
  let Z : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (R.I (cut+1))
      (finiteNumericH_physicalExtendedSeeds family
        L k M hAvoid I X W)
  let C : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (R.I (cut+1)) (X ∪ O)
  have hSame : ∀ z : AdmissibleKptNode family,
      cut ≤ LevelTree.lev z → (z ∈ Z ↔ z ∈ C) :=
    envelope_closure_highCut_absorbs_lower_levels
      (admissibleKptSTree family)
      I (R.I (cut+1)) X O cut hRetainedHigher
  exact kpt_highCut_membership_equiv_preserves_full_events
    family Z C cut hSame

/-- For TWO genuine Kpt AlgorithmRuns with increasing scan height
and an actual old top seed, enlargement of corrected original-ONLY
new-root seeds retains ALL old selected levels (verified M3/CH1).

At EVERY new cut p<newTop, any old selected q with p<q
belongs to the new run's higher level tail Rnew.I(p+1).
Thus the strong high-cut parameter stratification eliminates ALL
artificial I1/I2/full physical L+ source changes caused only by
preinserting the inherited old closure, without an assumption
that p is below ALL old interesting levels.

New original interactions may still generate additional genuine
microevents. This is not an exact canonical global diary theorem. -/
theorem finiteNumericH_newRoot_runs_allCuts_full_events_absorb
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (X : Set (AdmissibleKptNode family))
    (W : Set (Fin M))
    (oldTop newTop : Nat)
    (hTopLe : oldTop ≤ newTop)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = oldTop)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (Rnew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
      (finiteNumericH_physicalExtendedSeeds
        family L k M hAvoid (Rold.I 0) X W) newTop) :
    ∀ cut : Nat, cut < newTop →
      let O : Set (AdmissibleKptNode family) :=
        ((fun w : Fin M =>
          (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)
      let Z : Set (AdmissibleKptNode family) :=
        SMTree.Envelope.closure (admissibleKptSTree family)
          (Rnew.I (cut+1))
          (finiteNumericH_physicalExtendedSeeds family
            L k M hAvoid (Rold.I 0) X W)
      let C : Set (AdmissibleKptNode family) :=
        SMTree.Envelope.closure (admissibleKptSTree family)
          (Rnew.I (cut+1)) (X ∪ O)
      (KptI1AtCut family Z cut ↔ KptI1AtCut family C cut) ∧
      (KptI2MeetAtCut family Z cut ↔ KptI2MeetAtCut family C cut) ∧
      FullPhysicalClosureCrossing family Z cut =
        FullPhysicalClosureCrossing family C cut := by
  have hRetained : Rold.I 0 ⊆ Rnew.I 0 :=
    finiteNumericH_newRoot_run_retains_old_levels_larger_top
      family L k M hAvoid X W oldTop newTop
      hTopLe hTopSeed Rold Rnew
  intro cut hCut
  have hHigher : ∀ i : Nat, i ∈ Rold.I 0 →
      cut < i → i ∈ Rnew.I (cut+1) := by
    intro i hi hCutI
    rw [Rnew.I_eq_final_tail_of_run (cut+1) (by omega)]
    exact ⟨hRetained hi, by omega⟩
  exact finiteNumericH_newRoot_run_highCut_full_events_absorb
    family L k M hAvoid (Rold.I 0)
    X W newTop Rnew cut hCut hHigher

#print axioms Kk.envelope_closure_highCut_absorbs_lower_levels
#print axioms Kk.kpt_highCut_membership_equiv_preserves_full_events
#print axioms Kk.finiteNumericH_newRoot_run_highCut_full_events_absorb
#print axioms Kk.finiteNumericH_newRoot_runs_allCuts_full_events_absorb

end Kk
