import Kk.FullCrossingPoolIndependence
import Kk.B3LowerRealBaseCoverage
import Kk.B3ActualI3PhysicalCore
import Kk.B3ActualRunFullBadCoreIff
import SuccessorTree.V10.I3AlgorithmRunPool
import Mathlib.Tactic

/-!
# Track D: the ACTUAL pre-cut stage pool replaces the circular final source

English first, adversarially audited before writing this module:
docs/audits/2026-11-18-track-d-stage-local-source-english.md

At a tested cut c, the actual source closure is based on R.I(c+1).
Its original-name pool is the genuine stage set, not the final
R.I 0 set. We prove coverage of that stage source, exact old/upper
full L+/E name transport, pool independence of the full chosen
corrected-B3 test and a genuine lower-real local nonselection theorem.

No global retained-Q diary hypothesis or lower-cut induction is assumed.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Every node of the genuine finite numerical H+ Kpt closure at
ANY selected-level set I has a physical original representative
in the SAME finite stage pool. It includes generated meets and
auxiliary E parameters, with no no-I2 premise. This is the
stage-local Finset-naming form of the true successor closure invariant. -/
theorem finiteNumericH_stage_closure_represented_by_stage_originals
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid (U : Set (Fin N)))
    (I : Set Nat)
    (z : AdmissibleKptNode family)
    (hz : z ∈ SMTree.Envelope.closure
      (admissibleKptSTree family) I X) :
    ∃ v : Fin N,
      v ∈ hStageOriginals K k N U I ∧
      z ≤ (finiteNumericH K k N).kptOriginal family hAvoid v := by
  classical
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  obtain ⟨o,⟨v,hv,rfl⟩,hPrefix⟩ :=
    admissibleKpt_stage_closure_subset_pool
      family A hAvoid (U : Set (Fin N)) I X hX hz
  change Fin N at v
  have hV : v ∈ hStageOriginals K k N U I := by
    have hV' :
        v ∈ U ∨ (v.val ∈ I ∧ 0 < A.freeLevel v.val) := by
      rcases hv with hu | ⟨hLevel,hPositive⟩
      · exact Or.inl (Finset.mem_coe.mp hu)
      · exact Or.inr ⟨hLevel,hPositive⟩
    simpa only [hStageOriginals, Finset.mem_filter,
      Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      using hV'
  exact ⟨v,hV,hPrefix⟩

/-- Full physical OLD and UPPER L+/E names of a single actual
pre-cut crossing source can be reproduced by an original in
the true STAGE pool. The final-pool name v may be different.
No I2 or chosen-target hypothesis is used: both original
prefix records are restrictions of ONE actual source node z. -/
theorem finiteNumericH_stage_name_preserves_one_crossing_full_types
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid (U : Set (Fin N)))
    (I : Set Nat) (cut : Nat) (v : Fin N)
    (hFull : closureSelectedOriginal family
      (finiteNumericH K k N) hAvoid (fun q : Fin N => q)
      (SMTree.Envelope.closure (admissibleKptSTree family) I X)
      cut v) :
    ∃ w : Fin N,
      w ∈ hStageOriginals K k N U I ∧
      closureSelectedOriginal family
        (finiteNumericH K k N) hAvoid (fun q : Fin N => q)
        (SMTree.Envelope.closure (admissibleKptSTree family) I X)
        cut w ∧
      (finiteNumericH K k N).partialTypeAt cut v.val =
        (finiteNumericH K k N).partialTypeAt cut w.val ∧
      (finiteNumericH K k N).partialTypeAt (cut+1) v.val =
        (finiteNumericH K k N).partialTypeAt (cut+1) w.val := by
  classical
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  obtain ⟨z,hz,hCross,hBelowV⟩ := hFull
  obtain ⟨w,hStage,hBelowW⟩ :=
    finiteNumericH_stage_closure_represented_by_stage_originals
      family K k N hAvoid U X hX I z hz
  have hOldV :
      (LevelTree.ancestor z cut (Nat.le_of_lt hCross)).val =
        (⟨cut,A.partialTypeAt cut v.val⟩ :
          RawPartialTypeNode db du dd) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid v z hBelowV cut (Nat.le_of_lt hCross)
  have hOldW :
      (LevelTree.ancestor z cut (Nat.le_of_lt hCross)).val =
        (⟨cut,A.partialTypeAt cut w.val⟩ :
          RawPartialTypeNode db du dd) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid w z hBelowW cut (Nat.le_of_lt hCross)
  have hUpperV :
      (LevelTree.ancestor z (cut+1) (Nat.succ_le_iff.mpr hCross)).val =
        (⟨cut+1,A.partialTypeAt (cut+1) v.val⟩ :
          RawPartialTypeNode db du dd) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid v z hBelowV (cut+1)
        (Nat.succ_le_iff.mpr hCross)
  have hUpperW :
      (LevelTree.ancestor z (cut+1) (Nat.succ_le_iff.mpr hCross)).val =
        (⟨cut+1,A.partialTypeAt (cut+1) w.val⟩ :
          RawPartialTypeNode db du dd) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid w z hBelowW (cut+1)
        (Nat.succ_le_iff.mpr hCross)
  have hOld :
      A.partialTypeAt cut v.val = A.partialTypeAt cut w.val :=
    eq_of_heq (Sigma.mk.inj_iff.mp
      (hOldV.symm.trans hOldW)).2
  have hUpper :
      A.partialTypeAt (cut+1) v.val =
        A.partialTypeAt (cut+1) w.val :=
    eq_of_heq (Sigma.mk.inj_iff.mp
      (hUpperV.symm.trans hUpperW)).2
  exact ⟨w,hStage,⟨z,hz,hCross,hBelowW⟩,hOld,hUpper⟩

/-- The true stage pool based on Run.I(cut+1) and the possibly
LARGER final pool based on Run.I 0 BOTH exhaust the EXACT
pre-cut closure. A later-selected-stage name is never invented
retroactively. No no-I2 hypothesis is necessary for coverage. -/
theorem finiteNumericH_run_stage_and_final_pool_exhaust_same_closure
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid (U : Set (Fin N)))
    (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (cut : Nat) (hCut : cut < top) :
    let Stage : Finset (Fin N) :=
      hStageOriginals K k N U (Run.I (cut+1))
    let Final : Finset (Fin N) :=
      hStageOriginals K k N U (Run.I 0)
    let Z : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure
        (admissibleKptSTree family) (Run.I (cut+1)) X
    (Stage ⊆ Final) ∧
    (∀ z : AdmissibleKptNode family, z ∈ Z →
      ∃ i : Fin Stage.card,
        z ≤ (finiteNumericH K k N).kptOriginal family hAvoid
          (hOriginalName Stage i)) ∧
    (∀ z : AdmissibleKptNode family, z ∈ Z →
      ∃ i : Fin Final.card,
        z ≤ (finiteNumericH K k N).kptOriginal family hAvoid
          (hOriginalName Final i)) := by
  classical
  let Stage : Finset (Fin N) :=
    hStageOriginals K k N U (Run.I (cut+1))
  let Final : Finset (Fin N) :=
    hStageOriginals K k N U (Run.I 0)
  let Z : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure
      (admissibleKptSTree family) (Run.I (cut+1)) X
  have hI : Run.I (cut+1) ⊆ Run.I 0 := by
    intro i hi
    rw [Run.I_eq_final_tail_of_run (cut+1) (by omega)] at hi
    exact hi.1
  have hStageFinal : Stage ⊆ Final := by
    intro v hv
    have hv' :
        v ∈ U ∨
          (v.val ∈ Run.I (cut+1) ∧
           0 < (finiteNumericH K k N).freeLevel v.val) := by
      simpa only [Stage,hStageOriginals,Finset.mem_filter,
        Finset.mem_univ,true_and,Set.mem_ofPred_eq] using hv
    have hvF :
        v ∈ U ∨
          (v.val ∈ Run.I 0 ∧
           0 < (finiteNumericH K k N).freeLevel v.val) := by
      rcases hv' with hRoot | ⟨hCutSelected,hFree⟩
      · exact Or.inl hRoot
      · exact Or.inr ⟨hI hCutSelected,hFree⟩
    simpa only [Final,hStageOriginals,Finset.mem_filter,
      Finset.mem_univ,true_and,Set.mem_ofPred_eq] using hvF
  have hStageExhaust :
      ∀ z : AdmissibleKptNode family, z ∈ Z →
        ∃ i : Fin Stage.card,
          z ≤ (finiteNumericH K k N).kptOriginal family hAvoid
            (hOriginalName Stage i) := by
    intro z hz
    obtain ⟨v,hv,hBelow⟩ :=
      finiteNumericH_stage_closure_represented_by_stage_originals
        family K k N hAvoid U X hX (Run.I (cut+1)) z hz
    let i : Fin Stage.card := Stage.equivFin ⟨v,hv⟩
    have hName : hOriginalName Stage i = v := by
      simp [hOriginalName,i]
    refine ⟨i,?_⟩
    change z ≤ (finiteNumericH K k N).kptOriginal family hAvoid
      (hOriginalName _ i)
    rw [hName]
    exact hBelow
  have hFinalExhaust :
      ∀ z : AdmissibleKptNode family, z ∈ Z →
        ∃ i : Fin Final.card,
          z ≤ (finiteNumericH K k N).kptOriginal family hAvoid
            (hOriginalName Final i) := by
    intro z hz
    obtain ⟨v,hv,hBelow⟩ :=
      finiteNumericH_stage_closure_represented_by_stage_originals
        family K k N hAvoid U X hX (Run.I (cut+1)) z hz
    have hFin : v ∈ Final := hStageFinal hv
    let i : Fin Final.card := Final.equivFin ⟨v,hFin⟩
    have hName : hOriginalName Final i = v := by
      simp [hOriginalName,i]
    refine ⟨i,?_⟩
    change z ≤ (finiteNumericH K k N).kptOriginal family hAvoid
      (hOriginalName _ i)
    rw [hName]
    exact hBelow
  exact ⟨hStageFinal,hStageExhaust,hFinalExhaust⟩

/-- The ACTUAL pre-cut and final original-name lists give the same
complete old/upper L+/E source graph and the same corrected-B3 age
test, even if lower cuts add more final original names.
Unlike stage source coverage, this demands no actual I2 fork. -/
theorem finiteNumericH_run_stage_final_full_source_and_B3_eq
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid (U : Set (Fin N)))
    (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (cut : Nat) (hCut : cut < top)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode family,
      a ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (Run.I (cut+1)) X ∧
      ∃ b : AdmissibleKptNode family,
        b ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (Run.I (cut+1)) X ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :
    let Stage : Finset (Fin N) :=
      hStageOriginals K k N U (Run.I (cut+1))
    let Final : Finset (Fin N) :=
      hStageOriginals K k N U (Run.I 0)
    let Z : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure
        (admissibleKptSTree family) (Run.I (cut+1)) X
    let F : PrescribedBoringData cut db du dd :=
      closureSelectedBoringData family
        (finiteNumericH K k N) hAvoid (hOriginalName Stage) Z cut
    let G : PrescribedBoringData cut db du dd :=
      closureSelectedBoringData family
        (finiteNumericH K k N) hAvoid (hOriginalName Final) Z cut
    (F.source = G.source ∧
      ∀ T, T ∈ F.source → F.target T = G.target T) ∧
      (F.CorrectedB3 family ↔ G.CorrectedB3 family) := by
  classical
  let Stage : Finset (Fin N) :=
    hStageOriginals K k N U (Run.I (cut+1))
  let Final : Finset (Fin N) :=
    hStageOriginals K k N U (Run.I 0)
  let Z : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure
      (admissibleKptSTree family) (Run.I (cut+1)) X
  let F : PrescribedBoringData cut db du dd :=
    closureSelectedBoringData family
      (finiteNumericH K k N) hAvoid (hOriginalName Stage) Z cut
  let G : PrescribedBoringData cut db du dd :=
    closureSelectedBoringData family
      (finiteNumericH K k N) hAvoid (hOriginalName Final) Z cut
  obtain ⟨_hInclusion,hPoolStage,hPoolFinal⟩ :=
    finiteNumericH_run_stage_and_final_pool_exhaust_same_closure
      family K k N hAvoid U X hX top Run cut hCut
  have hCrossing :
      F.source = G.source ∧
        ∀ T, T ∈ F.source → F.target T = G.target T := by
    exact finiteNumericH_full_crossing_independent_of_original_pool
      family K k N hAvoid
      (hOriginalName Stage) (hOriginalName Final)
      Z hPoolStage hPoolFinal cut hNoI2
  have hB3 :
      F.CorrectedB3 family ↔ G.CorrectedB3 family := by
    exact finiteNumericH_correctedB3_independent_of_original_pool
      family K k N hAvoid
      (hOriginalName Stage) (hOriginalName Final)
      Z hPoolStage hPoolFinal cut hNoI2
  exact ⟨hCrossing,hB3⟩

/-- One ACTUAL lower-real AlgorithmRun cut is not selected if the
complete PRE-CUT STAGE source (not the unknown final source) has:
  full no-I1/no-I2, genuine Marked source representation,
  coverage of every positive later higher-generation base neighbour
  among all StageFull names, and actual chosen Marked B3.

The full B3 verdict transfers from the stage to the final pool
by the proven same-Z pool independence, NOT by a circular equality
of the proposed retained diary pool with the full final pool. -/
theorem henson_actualRun_lower_real_unselected_of_stage_covered_marked_B3
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N : Nat)
    (U : Finset (Fin N))
    (hAvoidA : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (X : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (hX : X ⊆ ambientPrefixPool
      (hensonForbiddenFamily ell hell)
      (finiteNumericH (normalizedGraphModel E) k N)
      hAvoidA (U : Set (Fin N)))
    (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell)) X top)
    (hTop : ∃ x ∈ X, LevelTree.lev x = top)
    (idx g : Nat) (hg : g < k)
    (hPos : 0 < hPosition k idx g)
    (hBelow : hPosition k idx g < top)
    (hCut : hPosition k idx g < N)
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode
      (hensonForbiddenFamily ell hell),
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (hPosition k idx g+1)) X ∧
      LevelTree.lev z = hPosition k idx g)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode
      (hensonForbiddenFamily ell hell),
      a ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (hPosition k idx g+1)) X ∧
      ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        b ∈ SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily ell hell))
          (Run.I (hPosition k idx g+1)) X ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = hPosition k idx g) :
    let cut : Nat := hPosition k idx g
    let Stage : Finset (Fin N) :=
      hStageOriginals (normalizedGraphModel E) k N U (Run.I (cut+1))
    let original : Fin Stage.card → Fin N := hOriginalName Stage
    let Z : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)) :=
      SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (cut+1)) X
    let Full : Fin Stage.card → Prop :=
      closureSelectedOriginal (hensonForbiddenFamily ell hell)
        (finiteNumericH (normalizedGraphModel E) k N)
        hAvoidA original Z cut
    ∀ (Marked : Fin Stage.card → Prop),
      (∀ v : Fin Stage.card, Marked v → Full v) →
      (∀ v : Fin Stage.card, Full v →
        ∀ j m : Nat, idx < j → g < m → m ≤ k →
          (original v).val = hPosition k j m →
          E idx j = true → Marked v) →
      (selectedStagePoolPrescribedData
        (finiteNumericH (normalizedGraphModel E) k N)
        cut original Marked).CorrectedB3
          (hensonForbiddenFamily ell hell) →
      cut ∉ Run.I 0 := by
  classical
  intro cut Stage original Z Full Marked hMarkedRepresented
    hBaseCovered hMarkedB3
  let family := hensonForbiddenFamily ell hell
  let K : AgeTestModel 1 0 1 := normalizedGraphModel E
  let A : EnumeratedPartialStructure 1 0 1 := finiteNumericH K k N
  have hStageB3 :
      (selectedStagePoolPrescribedData A cut original Full).CorrectedB3
        family := by
    exact henson_fullB3_of_lower_real_base_covered_marked_source
      ell hell k hK E hLoops hSym hClique
      N idx g Stage.card hg hCut original hAvoidA
      Z Full Marked hMarkedRepresented hNoI2 hBaseCovered hMarkedB3
  have hPoolEq :=
    finiteNumericH_run_stage_final_full_source_and_B3_eq
      family K k N hAvoidA U X hX top Run cut hBelow hNoI2
  let P := actualHensonRunCutOccurrence
    ell hell k hK E hLoops hSym hClique
    N U hAvoidA X top Run cut hCut hNoI2
  have hFinalB3 : P.fullProfile.CorrectedB3 family := by
    exact hPoolEq.2.mp hStageB3
  intro hSelected
  have hPhysical :
      HensonPhysicalCutStarBadCore
        ell hell P.k P.N cut P.M P.E P.original P.Full :=
    henson_actualRun_nonstructural_I3_has_exact_physical_core
      ell hell k hK E hLoops hSym hClique
      N U hAvoidA X hX top Run hTop
      cut hPos hBelow hCut hSelected hNoI1 hNoI2
  have hFailure : ¬ P.fullProfile.CorrectedB3 family :=
    (henson_actualRun_complete_fullB3_failure_iff_physical_bad_core
      ell hell k hK E hLoops hSym hClique
      N U hAvoidA X hX top Run cut hCut hBelow hNoI2).2.2.mpr
        hPhysical
  exact hFailure hFinalB3

#print axioms Kk.finiteNumericH_stage_closure_represented_by_stage_originals
#print axioms Kk.finiteNumericH_stage_name_preserves_one_crossing_full_types
#print axioms Kk.finiteNumericH_run_stage_and_final_pool_exhaust_same_closure
#print axioms Kk.finiteNumericH_run_stage_final_full_source_and_B3_eq
#print axioms Kk.henson_actualRun_lower_real_unselected_of_stage_covered_marked_B3

end Kk
