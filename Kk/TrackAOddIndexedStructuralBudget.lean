import Kk.TrackAOddBadSocleTrichotomy
import Mathlib.Tactic

/-!
# Track A/G: indexed structural bound on genuine odd Kpt factor-Bad cuts

English proof + 18 hostile checks committed first:
  docs/track_a_odd_bad_indexed_structural_budget_english_audit_20261122.md

At an exact old-factor Bad odd numerical-H cut, the verified physical
trichotomy yields a terminal, meet, or missing complete OLD Kpt socle.
Finite candidate node indices give a Q+Q² structural level envelope.
This does not bound Q or missing socles uniformly in the diary size.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

/-- Conservative image of all candidate terminal and pair-meet levels.
Inactive nodes and incompatible-component pairs may be included. -/
noncomputable def kptIndexedStructuralLevels
    {db du dd Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (node : Fin Q → AdmissibleKptNode family) : Finset Nat := by
  classical
  exact ((Finset.univ : Finset (Fin Q)).image
      (fun i => LevelTree.lev (node i))) ∪
    ((Finset.univ : Finset (Fin Q × Fin Q)).image
      (fun pair => LevelTree.lev
        (LevelTree.meet (node pair.1) (node pair.2))))

/-- At most Q candidate terminal levels plus Q² ordered meet levels;
no injectivity or uniform bound on the actual source index is used. -/
theorem kpt_indexed_structural_levels_card_le
    {db du dd Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (node : Fin Q → AdmissibleKptNode family) :
    (kptIndexedStructuralLevels family node).card ≤ Q + Q*Q := by
  classical
  let T : Finset Nat :=
    (Finset.univ : Finset (Fin Q)).image
      (fun i => LevelTree.lev (node i))
  let M : Finset Nat :=
    (Finset.univ : Finset (Fin Q × Fin Q)).image
      (fun pair => LevelTree.lev
        (LevelTree.meet (node pair.1) (node pair.2)))
  have hT : T.card ≤ Q := by
    have h : T.card ≤ (Finset.univ : Finset (Fin Q)).card := by
      dsimp [T]
      exact Finset.card_image_le
    simpa only [Finset.card_univ, Fintype.card_fin] using h
  have hM : M.card ≤ Q*Q := by
    have h : M.card ≤ (Finset.univ : Finset (Fin Q × Fin Q)).card := by
      dsimp [M]
      exact Finset.card_image_le
    simpa only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] using h
  have hUnion := Finset.card_union_le T M
  change (T ∪ M).card ≤ Q + Q*Q
  omega

/-- A genuinely live candidate crossing lacks any OLD source crossing
with the SAME COMPLETE dependent lower ancestor at this cut. -/
def kptMissingOldSocleAt
    {db du dd Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (node : Fin Q → AdmissibleKptNode family)
    (live : Nat → Fin Q → Bool)
    (cut : Nat) : Prop :=
  ∃ i : Fin Q, live cut i = true ∧
    ∃ (hCross : cut < LevelTree.lev (node i)),
      ¬ ∃ w : AdmissibleKptNode family,
        w ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) X ∧
        ∃ (hWCross : cut < LevelTree.lev w),
          LevelTree.ancestor (node i) cut (Nat.le_of_lt hCross) =
            LevelTree.ancestor w cut (Nat.le_of_lt hWCross)

/-- True old-factor Bad odd cuts outside the Q+Q² structural
candidate level envelope require a missing COMPLETE OLD Kpt
lower-ancestor witness. Candidate index exactness is at the
TRUE pre-cut parameter closure of the old run with seed Y. -/
theorem finiteNumericH_odd_bad_off_indexed_structural_has_missing_socle
    (family : List (NormalizedForbidden 1 0 1))
    (K : AgeTestModel 1 0 1) (k N Q : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hSym : ∀ i j : Nat,
      (finiteNumericH K k N).L.binary i j (0 : Fin 1) =
        (finiteNumericH K k N).L.binary j i (0 : Fin 1))
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid (U : Set (Fin N)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (node : Fin Q → AdmissibleKptNode family)
    (live : Nat → Fin Q → Bool)
    (a : Nat)
    (hExactY : ∀ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I ((2*a+1)+1)) Y ↔
      ∃ i : Fin Q, node i = z ∧ live (2*a+1) i = true)
    (hBad : (2*a+1) ∈ kptExactOldFactorBadCuts
      family X top R node live)
    (hOutside : (2*a+1) ∉ kptIndexedStructuralLevels family node) :
    kptMissingOldSocleAt family X top R node live (2*a+1) := by
  classical
  rcases finiteNumericH_odd_exact_bad_has_three_physical_witnesses
      family K k N Q hAvoid hSym U X Y hXY hY
        top R node live a hExactY hBad with hTerm | hMeet | hMissing
  · obtain ⟨z,hz,hLev⟩ := hTerm
    obtain ⟨i,hi,_⟩ := (hExactY z).mp hz
    exfalso
    apply hOutside
    change (2*a+1) ∈
      ((Finset.univ : Finset (Fin Q)).image
        (fun i => LevelTree.lev (node i))) ∪
      ((Finset.univ : Finset (Fin Q × Fin Q)).image
        (fun pair => LevelTree.lev
          (LevelTree.meet (node pair.1) (node pair.2))))
    apply Finset.mem_union.mpr
    left
    exact Finset.mem_image.mpr
      ⟨i, Finset.mem_univ i, by simpa only [hi] using hLev.symm⟩
  · obtain ⟨z,hz,w,hw,_hSame,hLev⟩ := hMeet
    obtain ⟨i,hi,_⟩ := (hExactY z).mp hz
    obtain ⟨j,hj,_⟩ := (hExactY w).mp hw
    exfalso
    apply hOutside
    change (2*a+1) ∈
      ((Finset.univ : Finset (Fin Q)).image
        (fun i => LevelTree.lev (node i))) ∪
      ((Finset.univ : Finset (Fin Q × Fin Q)).image
        (fun pair => LevelTree.lev
          (LevelTree.meet (node pair.1) (node pair.2))))
    apply Finset.mem_union.mpr
    right
    exact Finset.mem_image.mpr
      ⟨(i,j), Finset.mem_univ _, by simpa only [hi,hj] using hLev.symm⟩
  · obtain ⟨z,hz,hCross,hNoOld⟩ := hMissing
    obtain ⟨i,hi,hLive⟩ := (hExactY z).mp hz
    refine ⟨i,hLive,?_⟩
    rw [hi]
    exact ⟨hCross,hNoOld⟩

/-- Finite list of ODD actual factor-Bad cuts in the old run.
The factor-Bad predicate itself enforces cut<top. -/
noncomputable def kptOddExactBadCuts
    {db du dd Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (node : Fin Q → AdmissibleKptNode family)
    (live : Nat → Fin Q → Bool) : Finset Nat := by
  classical
  exact ((Finset.range top).image (fun a => 2*a+1)).filter
    (fun cut => cut ∈ kptExactOldFactorBadCuts
      family X top R node live)

/-- Conservative finite set of ODD cuts where a candidate crossing
has no old complete Kpt lower-ancestor witness. Membership need NOT
imply an actual factor-Bad event at the cut. -/
noncomputable def kptOddMissingOldSocleCuts
    {db du dd Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (node : Fin Q → AdmissibleKptNode family)
    (live : Nat → Fin Q → Bool) : Finset Nat := by
  classical
  exact (Finset.range top).filter
    (fun cut => cut % 2 = 1 ∧
      kptMissingOldSocleAt family X top R node live cut)

/-- ALL exact odd Bad cuts lie in the structural terminal/meet
envelope or in the genuinely missing OLD complete-socle set.
Candidate index is exact at every compared actual pre-cut closure. -/
theorem finiteNumericH_odd_bad_subset_structural_union_missing
    (family : List (NormalizedForbidden 1 0 1))
    (K : AgeTestModel 1 0 1) (k N Q : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hSym : ∀ i j : Nat,
      (finiteNumericH K k N).L.binary i j (0 : Fin 1) =
        (finiteNumericH K k N).L.binary j i (0 : Fin 1))
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid (U : Set (Fin N)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (node : Fin Q → AdmissibleKptNode family)
    (live : Nat → Fin Q → Bool)
    (hExactY : ∀ cut : Nat, cut < top →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) Y ↔
        ∃ i : Fin Q, node i = z ∧ live cut i = true) :
    kptOddExactBadCuts family X top R node live ⊆
      kptIndexedStructuralLevels family node ∪
      kptOddMissingOldSocleCuts family X top R node live := by
  classical
  intro cut hCut
  have hSource :
      cut ∈ ((Finset.range top).image (fun a => 2*a+1)) ∧
      cut ∈ kptExactOldFactorBadCuts family X top R node live :=
    Finset.mem_filter.mp hCut
  obtain ⟨a,_ha,hEq⟩ := Finset.mem_image.mp hSource.1
  have hCutTop : cut < top :=
    ((mem_kptExactOldFactorBadCuts
      family X top R node live cut).mp hSource.2).1
  by_cases hStruct : cut ∈ kptIndexedStructuralLevels family node
  · exact Finset.mem_union.mpr (Or.inl hStruct)
  · have hBadOdd : (2*a+1) ∈
        kptExactOldFactorBadCuts family X top R node live := by
      simpa only [hEq] using hSource.2
    have hOffOdd : (2*a+1) ∉
        kptIndexedStructuralLevels family node := by
      simpa only [hEq] using hStruct
    have hExactOdd :
        ∀ z : AdmissibleKptNode family,
          z ∈ SMTree.Envelope.closure
            (admissibleKptSTree family) (R.I ((2*a+1)+1)) Y ↔
          ∃ i : Fin Q, node i = z ∧ live (2*a+1) i = true := by
      simpa only [hEq] using hExactY cut hCutTop
    have hMissingOdd :=
      finiteNumericH_odd_bad_off_indexed_structural_has_missing_socle
        family K k N Q hAvoid hSym U X Y hXY hY
        top R node live a hExactOdd hBadOdd hOffOdd
    have hMissing :
        kptMissingOldSocleAt family X top R node live cut := by
      simpa only [hEq] using hMissingOdd
    apply Finset.mem_union.mpr
    right
    unfold kptOddMissingOldSocleCuts
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hCutTop, ?_⟩
    refine ⟨?_,hMissing⟩
    omega

/-- Quantitative finite-source result:
bad ODD cuts ≤ Q + Q² + odd missing-complete-old-socle cuts.
No bound on Q or the latter cardinality is assumed. -/
theorem finiteNumericH_odd_bad_card_le_structural_plus_missing
    (family : List (NormalizedForbidden 1 0 1))
    (K : AgeTestModel 1 0 1) (k N Q : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hSym : ∀ i j : Nat,
      (finiteNumericH K k N).L.binary i j (0 : Fin 1) =
        (finiteNumericH K k N).L.binary j i (0 : Fin 1))
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid (U : Set (Fin N)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (node : Fin Q → AdmissibleKptNode family)
    (live : Nat → Fin Q → Bool)
    (hExactY : ∀ cut : Nat, cut < top →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) Y ↔
        ∃ i : Fin Q, node i = z ∧ live cut i = true) :
    (kptOddExactBadCuts family X top R node live).card ≤
      Q + Q*Q +
      (kptOddMissingOldSocleCuts
        family X top R node live).card := by
  classical
  have hSub := finiteNumericH_odd_bad_subset_structural_union_missing
    family K k N Q hAvoid hSym U X Y hXY hY
      top R node live hExactY
  have hSubCard := Finset.card_le_card hSub
  have hUnion := Finset.card_union_le
    (kptIndexedStructuralLevels family node)
    (kptOddMissingOldSocleCuts family X top R node live)
  have hBound := kpt_indexed_structural_levels_card_le family node
  omega

/-- If no odd cut has a missing complete old Kpt socle, exact odd
Bad cuts are confined to at most Q+Q² structural levels. -/
theorem finiteNumericH_odd_bad_card_le_of_no_missing_old_socle
    (family : List (NormalizedForbidden 1 0 1))
    (K : AgeTestModel 1 0 1) (k N Q : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hSym : ∀ i j : Nat,
      (finiteNumericH K k N).L.binary i j (0 : Fin 1) =
        (finiteNumericH K k N).L.binary j i (0 : Fin 1))
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid (U : Set (Fin N)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (node : Fin Q → AdmissibleKptNode family)
    (live : Nat → Fin Q → Bool)
    (hExactY : ∀ cut : Nat, cut < top →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) Y ↔
        ∃ i : Fin Q, node i = z ∧ live cut i = true)
    (hNoMissing : kptOddMissingOldSocleCuts
      family X top R node live = ∅) :
    (kptOddExactBadCuts family X top R node live).card ≤
      Q + Q*Q := by
  have h := finiteNumericH_odd_bad_card_le_structural_plus_missing
    family K k N Q hAvoid hSym U X Y hXY hY
      top R node live hExactY
  simpa [hNoMissing] using h

#print axioms Kk.finiteNumericH_odd_bad_card_le_of_no_missing_old_socle
#print axioms Kk.finiteNumericH_odd_bad_card_le_structural_plus_missing
#print axioms Kk.finiteNumericH_odd_bad_subset_structural_union_missing
#print axioms Kk.kpt_indexed_structural_levels_card_le
#print axioms Kk.finiteNumericH_odd_bad_off_indexed_structural_has_missing_socle

end Kk
