import Kk.TrackCOddFinalFreeEndSupport
import Kk.TrackDOddStageNoFreeEnd
import Mathlib.Tactic

/-!
# Track C: new candidate I1 terminal reflects to the old source at safe ODD cuts

English-first, adversarially audited mathematical proof:
 docs/track_c_odd_i1_reflection_audit_20261121.md

The physical free-end set F of the genuine FINAL ORIGINAL stage
has size <= M, where M is the finite numerical carrier. At every
odd cut c<oldTop outside F, complete original stage E-free endpoints
are absent. The new bare root's own E-free endpoint is ABOVE oldTop.

Crucially, even without old-prefix matching or old-boringness,
a NEW candidate full Kpt I1 terminal at c implies an OLD full Kpt
I1 terminal at c: either an old initial seed ends there, giving
the old witness, or NO Y seed ends there and the verified Track D
odd full-I1 theorem excludes ALL generated new terminals.

Only I1 is controlled; I2/I3, full old/upper L+/E crossing inclusion,
actual taller new runs, diary-uniform BRD and inverse-source
monoid orbits are NOT asserted.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Generic one-bare-source ODD I1 terminal reflection. No genuine
old-boring assumption: if an OLD seed ends at c it itself witnesses
the old terminal; otherwise no Y seed ends there and the full
stage no-E-free-end theorem eliminates generated I1.

The FULL original-stage free-end condition and the new literal
bare root not ending at c are still separate premises here. -/
theorem finiteNumericH_one_bare_odd_terminal_reflects_of_no_stage_end
    (family : List (NormalizedForbidden 1 0 1))
    (L : AgeTestModel 1 0 1) (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (hSym : ∀ i j : Nat,
      (finiteNumericH L k M).L.binary i j (0 : Fin 1) =
        (finiteNumericH L k M).L.binary j i (0 : Fin 1))
    (W : Finset (Fin M))
    (X Y : Set (AdmissibleKptNode family))
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH L k M) hAvoid (W : Set (Fin M)))
    (newV : Fin M)
    (hBare : Y = X ∪
      ({(finiteNumericH L k M).kptOriginal family hAvoid newV} :
        Set (AdmissibleKptNode family)))
    (oldTop : Nat)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (a : Nat)
    (hNewFreeNe :
      (finiteNumericH L k M).freeLevel newV.val ≠ 2*a+1)
    (hNoStageEnd : ∀ v : Fin M,
      v ∈ ambientStagePool (finiteNumericH L k M)
        (W : Set (Fin M)) (Rold.I ((2*a+1)+1)) →
      (finiteNumericH L k M).freeLevel v.val ≠ 2*a+1) :
    KptI1AtCut family
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (Rold.I ((2*a+1)+1)) Y) (2*a+1) →
    KptI1AtCut family
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (Rold.I ((2*a+1)+1)) X) (2*a+1) := by
  classical
  let c : Nat := 2*a+1
  by_cases hOldSeed : ∃ z : AdmissibleKptNode family,
      z ∈ X ∧ LevelTree.lev z = c
  · obtain ⟨z,hz,hLev⟩ := hOldSeed
    intro _hNewI1
    exact ⟨z,
      (SMTree.Envelope.subset_closure
        (admissibleKptSTree family) (Rold.I (c+1)) X) hz,
      hLev⟩
  · have hNoYSeed :
        ¬ ∃ z : AdmissibleKptNode family,
          z ∈ Y ∧ LevelTree.lev z = c := by
      rintro ⟨z,hYz,hLev⟩
      rw [hBare] at hYz
      rcases hYz with hzOld | hzNew
      · exact hOldSeed ⟨z,hzOld,hLev⟩
      · have hzEq : z =
          (finiteNumericH L k M).kptOriginal family hAvoid newV := by
          simpa only [Set.mem_singleton_iff] using hzNew
        subst z
        exact hNewFreeNe hLev
    have hNoNewI1 : ¬ KptI1AtCut family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (Rold.I (c+1)) Y) c := by
      change ¬ ∃ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (Rold.I (c+1)) Y ∧
        LevelTree.lev z = c
      exact finiteNumericH_odd_no_full_I1_of_no_seed_or_stage_free
        family L k M hAvoid hSym
        (Rold.I (c+1)) Y (W : Set (Fin M))
        hY a hNoYSeed hNoStageEnd
    intro hNewI1
    exact False.elim (hNoNewI1 hNewI1)

/-- In the genuine two-model numerical-H+ base extension, construct
one real old Kpt run Rold, one finite full original pool W and a
finite exceptional source-cut set F with |F|<=M. Every ODD cut
c=2a+1<oldTop OUTSIDE F has one-way FULL I1 terminal reflection
NEW->OLD in the candidate pre-cut source, WITHOUT an old-boring
hypothesis or ANY complete old Kpt prefix match.

The physical chronology derives the new bare root endpoint
newTop>c, and F excludes all other generated original E-free
endpoints. This is not an I2/I3 or whole-run transport theorem. -/
theorem finiteNumericH_constructed_odd_terminal_reflects_outside_freeends
    (family : List (NormalizedForbidden 1 0 1))
    (K L : AgeTestModel 1 0 1)
    (k b N M j : Nat)
    (hNM : N ≤ M) (hBlock : N ≤ hPosition k b 0)
    (hk : 0 < k) (hj : 0 < j)
    (hTarget : hPosition k j k < M)
    (hNTop : N ≤ hPosition k (j-1) k+1)
    (hBin : ∀ i j : Nat, i < b → j < b →
      ∀ r : Fin 1, K.binary i j r = L.binary i j r)
    (hUn : ∀ i : Nat, i < b → ∀ r : Fin 0,
      K.unary i r = L.unary i r)
    (hDiag : ∀ i : Nat, i < b → ∀ r : Fin 1,
      K.diagonal i r = L.diagonal i r)
    (hAvoidK : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hAvoidL : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (hSymL : ∀ i j : Nat,
      (finiteNumericH L k M).L.binary i j (0 : Fin 1) =
        (finiteNumericH L k M).L.binary j i (0 : Fin 1))
    (U : Set (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hSeeds : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoidK U)
    (oldTop : Nat)
    (hOldPhysical : HasPhysicalExhaustiveKptRun family X oldTop) :
    let Y : Set (AdmissibleKptNode family) :=
      finiteNumericH_bareTopRootSeeds
        family L k M j hAvoidL hTarget X
    ∃ Rold : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family) X oldTop,
      ∃ W : Finset (Fin M),
        ∃ F : Finset Nat,
          Y ⊆ ambientPrefixPool family
            (finiteNumericH L k M) hAvoidL (W : Set (Fin M)) ∧
          F.card ≤ M ∧
          ∀ a : Nat,
            2*a+1 < oldTop →
            2*a+1 ∉ F →
            (KptI1AtCut family
              (SMTree.Envelope.closure (admissibleKptSTree family)
                (Rold.I ((2*a+1)+1)) Y) (2*a+1) →
             KptI1AtCut family
              (SMTree.Envelope.closure (admissibleKptSTree family)
                (Rold.I ((2*a+1)+1)) X) (2*a+1)) := by
  classical
  let w : Fin M := ⟨hPosition k j k, hTarget⟩
  let Y : Set (AdmissibleKptNode family) :=
    finiteNumericH_bareTopRootSeeds
      family L k M j hAvoidL hTarget X
  have hPhysicalCopy : HasPhysicalExhaustiveKptRun
      family X oldTop := hOldPhysical
  obtain ⟨_Rtrue,hOldTopSeed,_oldParams,_oldLive,
      _oldFinal,_oldInj,_oldPresent,_oldExact⟩ := hPhysicalCopy
  have hOldTopLe : oldTop ≤ hPosition k (j-1) k+1 :=
    finiteNumericH_old_physical_top_le_new_chronological_top
      family K k N j oldTop hNTop hAvoidK U X hSeeds hOldTopSeed
  have hNewFree :
      (finiteNumericH L k M).freeLevel w.val =
        hPosition k (j-1) k+1 :=
    finiteNumericH_top_freeLevel_exact L k M j hk hj hTarget
  obtain ⟨Rold,W,hY,_hOdd⟩ :=
    finiteNumericH_constructed_bare_odd_quiet_of_stage_free_and_socle
      family K L k b N M j hNM hBlock hk hj hTarget hNTop
      hBin hUn hDiag hAvoidK hAvoidL hSymL
      U X hSeeds oldTop hOldPhysical
  let F : Finset Nat :=
    KptPhysicalFinalStageFreeEnds family L k M W X oldTop Rold
  have hCard : F.card ≤ M :=
    kpt_physical_final_freeend_cuts_card_le_carrier
      family L k M W X oldTop Rold
  have hBare : Y = X ∪
      ({(finiteNumericH L k M).kptOriginal family hAvoidL w} :
        Set (AdmissibleKptNode family)) := by
    change X ∪
      ((fun v : Fin M =>
        (finiteNumericH L k M).kptOriginal family hAvoidL v) ''
        ({w} : Set (Fin M))) = _
    simp only [Set.image_singleton]
  refine ⟨Rold,W,F,hY,hCard,?_⟩
  intro a hCut hNotF
  have hNewFreeNe :
      (finiteNumericH L k M).freeLevel w.val ≠ 2*a+1 := by
    rw [hNewFree]
    omega
  have hNoEnd : ∀ v : Fin M,
      v ∈ ambientStagePool (finiteNumericH L k M)
        (W : Set (Fin M)) (Rold.I ((2*a+1)+1)) →
      (finiteNumericH L k M).freeLevel v.val ≠ 2*a+1 :=
    kpt_physical_no_stage_free_end_outside_final
      family L k M W X oldTop Rold (2*a+1) hCut hNotF
  exact finiteNumericH_one_bare_odd_terminal_reflects_of_no_stage_end
    family L k M hAvoidL hSymL W X Y hY w hBare
    oldTop Rold a hNewFreeNe hNoEnd

end Kk

#check @Kk.finiteNumericH_one_bare_odd_terminal_reflects_of_no_stage_end
#print axioms Kk.finiteNumericH_one_bare_odd_terminal_reflects_of_no_stage_end
#check @Kk.finiteNumericH_constructed_odd_terminal_reflects_outside_freeends
#print axioms Kk.finiteNumericH_constructed_odd_terminal_reflects_outside_freeends
