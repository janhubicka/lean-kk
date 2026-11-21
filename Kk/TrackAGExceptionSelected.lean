import Kk.TrackGDistinctSeedProfileScan
import Mathlib.Tactic

/-!
# Track A/G: two actual successor scans agree off an exceptional cut set

English proof and adversarial audit written FIRST:
  docs/track_a_g_exception_localization_english_audit_20261121.md

This builds on the already merged full terminal and complete L+/E
crossing profile transfer from Track G. It does NOT assert that the
proposed KK-free diary provides matching full profiles outside the
ordinary-L critical generation set. Such an implication remains OPEN.
-/

namespace Kk

universe u v

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

/-- A genuine AlgorithmRun only inserts the CURRENT numerical cut
when descending from its next stage. Membership of any OTHER cut
is unchanged, regardless of whether this stage is interesting. -/
private theorem actualAlgorithmRun_other_cut_mem_iff_next
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    {S : STree T Label}
    (H : SMTree S) (X : Set T) (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun H X top)
    (i : Nat) (hi : i < top) (j : Nat) (hji : j ≠ i) :
    (j ∈ R.I i ↔ j ∈ R.I (i+1)) := by
  classical
  by_cases hint :
      SMTree.Envelope.IsInterestingAt H
        (SMTree.Envelope.closure S (R.I (i+1)) X) i
  · have hStep := (R.interesting_step i hi hint).1
    rw [hStep]
    simp only [Set.mem_insert_iff]
    simp [hji]
  · obtain ⟨_,_,_,hStep,_⟩ :=
      R.noninteresting_step i hi hint
    rw [hStep]

/-- **Actual-run exception localization.**
If two possibly different-seed AlgorithmRuns have identical genuine
interestingness decisions at every cut outside an exceptional SET,
then, at EVERY stage, their selected sets agree at every level
outside that set. The tests are made on their independently
constructed actual pre-cut closures, not one hypothetical common
tail. No finiteness of the exceptional set is needed. -/
theorem actualAlgorithmRuns_selected_agree_off_exception
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    {S : STree T Label}
    (H : SMTree S) (X Y : Set T) (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun H X top)
    (RY : SMTree.Envelope.AlgorithmRun H Y top)
    (Exceptional : Set Nat)
    (hDecision : ∀ i : Nat, i < top → i ∉ Exceptional →
      (SMTree.Envelope.IsInterestingAt H
        (SMTree.Envelope.closure S (RX.I (i+1)) X) i ↔
       SMTree.Envelope.IsInterestingAt H
        (SMTree.Envelope.closure S (RY.I (i+1)) Y) i)) :
    ∀ i : Nat, i ≤ top → ∀ j : Nat, j ∉ Exceptional →
      (j ∈ RX.I i ↔ j ∈ RY.I i) := by
  classical
  have main :
      ∀ d : Nat, ∀ i : Nat, top - i = d →
        i ≤ top → ∀ j : Nat, j ∉ Exceptional →
        (j ∈ RX.I i ↔ j ∈ RY.I i) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro i hdi hi j hj
        by_cases hieq : i = top
        · subst i
          rw [RX.topI, RY.topI]
        · have hilt : i < top := lt_of_le_of_ne hi hieq
          have hNext : (j ∈ RX.I (i+1) ↔
              j ∈ RY.I (i+1)) :=
            ih (top-(i+1)) (by omega) (i+1) rfl
              (by omega) j hj
          by_cases hiExc : i ∈ Exceptional
          · have hji : j ≠ i := by
              intro heq
              subst j
              exact hj hiExc
            have hX := actualAlgorithmRun_other_cut_mem_iff_next
              H X top RX i hilt j hji
            have hY := actualAlgorithmRun_other_cut_mem_iff_next
              H Y top RY i hilt j hji
            exact hX.trans (hNext.trans hY.symm)
          · have hDec := hDecision i hilt hiExc
            by_cases hintX :
                SMTree.Envelope.IsInterestingAt H
                  (SMTree.Envelope.closure S
                    (RX.I (i+1)) X) i
            · have hintY :
                  SMTree.Envelope.IsInterestingAt H
                    (SMTree.Envelope.closure S
                      (RY.I (i+1)) Y) i :=
                hDec.mp hintX
              have hIX := (RX.interesting_step i hilt hintX).1
              have hIY := (RY.interesting_step i hilt hintY).1
              rw [hIX, hIY]
              simp only [Set.mem_insert_iff]
              exact or_congr Iff.rfl hNext
            · have hintY :
                  ¬ SMTree.Envelope.IsInterestingAt H
                    (SMTree.Envelope.closure S
                      (RY.I (i+1)) Y) i := by
                intro h
                exact hintX (hDec.mpr h)
              obtain ⟨_,_,_,hIX,_⟩ :=
                RX.noninteresting_step i hilt hintX
              obtain ⟨_,_,_,hIY,_⟩ :=
                RY.noninteresting_step i hilt hintY
              rw [hIX, hIY]
              exact hNext
  intro i hi j hj
  exact main (top-i) i rfl hi j hj

/-- The symmetric difference of the FINAL selected levels of
two actual successor scans is contained in the exception set.
The set inclusion itself does not require finite exceptions. -/
theorem actualAlgorithmRuns_selected_diff_subset_exception
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    {S : STree T Label}
    (H : SMTree S) (X Y : Set T) (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun H X top)
    (RY : SMTree.Envelope.AlgorithmRun H Y top)
    (Exceptional : Set Nat)
    (hDecision : ∀ i : Nat, i < top → i ∉ Exceptional →
      (SMTree.Envelope.IsInterestingAt H
        (SMTree.Envelope.closure S (RX.I (i+1)) X) i ↔
       SMTree.Envelope.IsInterestingAt H
        (SMTree.Envelope.closure S (RY.I (i+1)) Y) i)) :
    (RX.I 0 \ RY.I 0) ∪ (RY.I 0 \ RX.I 0) ⊆ Exceptional := by
  intro j hjDiff
  by_contra hjOff
  have hEq := actualAlgorithmRuns_selected_agree_off_exception
    H X Y top RX RY Exceptional hDecision 0
    (Nat.zero_le top) j hjOff
  rcases Set.mem_union.mp hjDiff with hLeft | hRight
  · have hPair := Set.mem_diff.mp hLeft
    exact hPair.2 (hEq.mp hPair.1)
  · have hPair := Set.mem_diff.mp hRight
    exact hPair.2 (hEq.mpr hPair.1)

/-- Track G's actual full-profile criterion transfers the
generic exception localization to DIFFERENT genuine Kpt seeds.
Terminal I1 equivalence and FULL old/upper L+/E crossing-pair
equality must hold at each actual stage OUTSIDE Exceptional.
In particular, auxiliary I2 forks and I3 monoid skip
obstructions are not projected away to binary L. -/
theorem kpt_actual_runs_selected_agree_off_full_profiles
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (RY : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y top)
    (Exceptional : Set Nat)
    (hTerminal : ∀ cut : Nat, cut < top → cut ∉ Exceptional →
      (KptI1AtCut family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) X) cut ↔
       KptI1AtCut family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RY.I (cut+1)) Y) cut))
    (hCrossing : ∀ cut : Nat, cut < top → cut ∉ Exceptional →
      FullPhysicalClosureCrossing family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) X) cut =
      FullPhysicalClosureCrossing family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RY.I (cut+1)) Y) cut) :
    ∀ i : Nat, i ≤ top → ∀ j : Nat, j ∉ Exceptional →
      (j ∈ RX.I i ↔ j ∈ RY.I i) := by
  apply actualAlgorithmRuns_selected_agree_off_exception
    (normalizedKptSMTree family) X Y top RX RY Exceptional
  intro cut hCut hOff
  exact kpt_IsInterestingAt_iff_of_terminal_and_full_crossing_eq
    family
    (SMTree.Envelope.closure (admissibleKptSTree family)
      (RX.I (cut+1)) X)
    (SMTree.Envelope.closure (admissibleKptSTree family)
      (RY.I (cut+1)) Y)
    cut (hTerminal cut hCut hOff) (hCrossing cut hCut hOff)


/-- The number of DISTINCT final selected-level disagreements is
bounded by the number of exceptional cut coordinates, for a finite
exception set. No assumption that the selected levels themselves
are all exceptional or finite-by-structure is needed: both
finiteness and the bound follow from their symmetric difference
being contained in a finite set. -/
theorem actualAlgorithmRuns_selected_disagreement_card_le
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    {S : STree T Label}
    (H : SMTree S) (X Y : Set T) (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun H X top)
    (RY : SMTree.Envelope.AlgorithmRun H Y top)
    (Exceptional : Finset Nat)
    (hDecision : ∀ i : Nat, i < top →
      i ∉ (Exceptional : Set Nat) →
      (SMTree.Envelope.IsInterestingAt H
        (SMTree.Envelope.closure S (RX.I (i+1)) X) i ↔
       SMTree.Envelope.IsInterestingAt H
        (SMTree.Envelope.closure S (RY.I (i+1)) Y) i)) :
    ((RX.I 0 \ RY.I 0) ∪ (RY.I 0 \ RX.I 0)).ncard ≤
      Exceptional.card := by
  have hSub := actualAlgorithmRuns_selected_diff_subset_exception
    H X Y top RX RY (Exceptional : Set Nat) hDecision
  have hBound :=
    Set.ncard_le_ncard hSub (Finset.finite_toSet Exceptional)
  simpa only [Set.ncard_coe_finset] using hBound

/-- Full terminal I1 and dependent old/upper L+/E crossing
equality outside a FINITE set of cuts bounds the number of
actual selected-level disagreements for two different-seed
Kpt scans by the size of that set. This is conditional on
matching the actual pre-cut closure profiles, not ordinary-L
graph ages or an unverified diary-derived transfer. -/
theorem kpt_actual_runs_selected_disagreement_card_le_of_full_profiles
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (RY : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y top)
    (Exceptional : Finset Nat)
    (hTerminal : ∀ cut : Nat, cut < top →
      cut ∉ (Exceptional : Set Nat) →
      (KptI1AtCut family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) X) cut ↔
       KptI1AtCut family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RY.I (cut+1)) Y) cut))
    (hCrossing : ∀ cut : Nat, cut < top →
      cut ∉ (Exceptional : Set Nat) →
      FullPhysicalClosureCrossing family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) X) cut =
      FullPhysicalClosureCrossing family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RY.I (cut+1)) Y) cut) :
    ((RX.I 0 \ RY.I 0) ∪ (RY.I 0 \ RX.I 0)).ncard ≤
      Exceptional.card := by
  apply actualAlgorithmRuns_selected_disagreement_card_le
    (normalizedKptSMTree family) X Y top RX RY Exceptional
  intro cut hCut hOff
  exact kpt_IsInterestingAt_iff_of_terminal_and_full_crossing_eq
    family
    (SMTree.Envelope.closure (admissibleKptSTree family)
      (RX.I (cut+1)) X)
    (SMTree.Envelope.closure (admissibleKptSTree family)
      (RY.I (cut+1)) Y)
    cut (hTerminal cut hCut hOff) (hCrossing cut hCut hOff)

#print axioms Kk.actualAlgorithmRuns_selected_disagreement_card_le
#print axioms Kk.kpt_actual_runs_selected_disagreement_card_le_of_full_profiles
#print axioms Kk.actualAlgorithmRuns_selected_agree_off_exception
#print axioms Kk.actualAlgorithmRuns_selected_diff_subset_exception
#print axioms Kk.kpt_actual_runs_selected_agree_off_full_profiles

end Kk
