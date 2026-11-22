import Kk.TrackCOddSelectedLevelExceptionBudget
import Kk.NumericHBaseExtensionCoherence
import Mathlib.Tactic

/-!
# Track C: the bare root requires only inherited physical roots plus ONE new root

English proof and 24-case adversarial audit COMMITTED BEFORE Lean:
 docs/track_c_small_bare_root_odd_exception_budget_english_audit_20261122.md

For a TRUE old finite ORIGINAL root pool U with complete dependent
Kpt prefix coverage, the *bare* new seed Y=X∪{ONE physical original}
is represented in the enlarged physical ambient by just
W=Fin.castLE[U]∪{new root}. No selected old Kpt closure parameters
need to be included as INITIAL root-original names. This gives
|W|<=|U|+1, retaining all old directed auxiliary E and ordinary L.

The complete genuine final-stage E-free-end exception set therefore
has cardinal at most min(M, |U|+|actual old selected levels|+1).
At old-unselected ODD cuts outside that constructed finite set,
the complete candidate is quiet PROVIDED genuine complete OLD Kpt
prefix witnesses exist for active stage originals. This does NOT
construct those witnesses, quiet genuinely exceptional source cuts,
identify the taller target run, or give diary-uniform BRDs.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- In a genuine two-model physical numerical-H+ base extension,
the truly BARE old-plus-one-new-original seed set has an actual
full-dependent Kpt original-prefix cover by a pool containing
at most |U|+1 physical original names.

The chosen W is literally the cast old root-original set with
the ONE actual new target added. This theorem avoids the larger
old selected-stage pool formerly used as the root cover.

The old source X must already have physical full Kpt prefix
coverage by the finite U; its existence is not inferred from an
ordinary-L graph shadow or a proposed abstract diary. -/
theorem finiteNumericH_bare_root_small_original_pool
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K L : AgeTestModel db du dd)
    (k b N M j : Nat)
    (hNM : N ≤ M) (hBlock : N ≤ hPosition k b 0)
    (hTarget : hPosition k j k < M)
    (hBin : ∀ i j : Nat, i < b → j < b →
      ∀ r : Fin db, K.binary i j r = L.binary i j r)
    (hUn : ∀ i : Nat, i < b → ∀ r : Fin du,
      K.unary i r = L.unary i r)
    (hDiag : ∀ i : Nat, i < b → ∀ r : Fin dd,
      K.diagonal i r = L.diagonal i r)
    (hAvoidK : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hAvoidL : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hSeeds : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoidK (U : Set (Fin N))) :
    ∃ W : Finset (Fin M),
      W.card ≤ U.card + 1 ∧
      finiteNumericH_bareTopRootSeeds
        family L k M j hAvoidL hTarget X ⊆
          ambientPrefixPool family (finiteNumericH L k M)
            hAvoidL (W : Set (Fin M)) := by
  classical
  let B : EnumeratedPartialStructure db du dd :=
    finiteNumericH L k M
  let w : Fin M := ⟨hPosition k j k, hTarget⟩
  let U' : Finset (Fin M) := U.image (Fin.castLE hNM)
  let W : Finset (Fin M) := U' ∪ {w}
  have hOldLift :
      X ⊆ ambientPrefixPool family B hAvoidL
        ((Fin.castLE hNM) '' (U : Set (Fin N))) :=
    finiteNumericH_baseExtension_old_seedPool_lifts
      family K L k b N M hNM hBlock
      hBin hUn hDiag hAvoidK hAvoidL
      (U : Set (Fin N)) X hSeeds
  have hRootSub :
      ((Fin.castLE hNM) '' (U : Set (Fin N))) ⊆
        (W : Set (Fin M)) := by
    rintro v ⟨u,hu,rfl⟩
    change Fin.castLE hNM u ∈ W
    change Fin.castLE hNM u ∈ U' ∪ ({w} : Finset (Fin M))
    apply Finset.mem_union.mpr
    left
    exact Finset.mem_image.mpr ⟨u,hu,rfl⟩
  have hw : w ∈ (W : Set (Fin M)) := by
    change w ∈ W
    simp [W]
  have hCardU : U'.card ≤ U.card := Finset.card_image_le
  have hBound : W.card ≤ U.card + 1 := by
    calc
      W.card = (U' ∪ {w}).card := rfl
      _ ≤ U'.card + ({w} : Finset (Fin M)).card :=
        Finset.card_union_le U' ({w} : Finset (Fin M))
      _ = U'.card + 1 := by simp
      _ ≤ U.card + 1 := Nat.add_le_add_right hCardU 1
  refine ⟨W, hBound, ?_⟩
  intro z hz
  change z ∈ X ∪
    ((fun v : Fin M => B.kptOriginal family hAvoidL v) ''
      ({w} : Set (Fin M))) at hz
  rcases hz with hzOld | hzNew
  · obtain ⟨o,⟨v,hv,ho⟩,hBelow⟩ := hOldLift hzOld
    exact ⟨o, ⟨v,hRootSub hv,ho⟩,hBelow⟩
  · rw [Set.image_singleton] at hzNew
    have hzEq : z = B.kptOriginal family hAvoidL w :=
      Set.mem_singleton_iff.mp hzNew
    subst z
    exact ⟨B.kptOriginal family hAvoidL w,
      ⟨w,hw,rfl⟩,le_rfl⟩

/-- A TRUE chronological finite numerical-H+ K/L extension with a
finite OLD root-original set U constructs:
* a genuine old dependent Kpt AlgorithmRun Rold;
* a small, concrete bare root cover W, |W|<=|U|+1;
* one actual FINAL physical auxiliary-E free-end exception set F,
  |F|<=min(M, |U|+|actual selected old levels|+1).

At every old-unselected ODD cut c=2*a+1<oldTop outside this
constructed F, complete candidate no-novelty follows from the
genuine COMPLETE OLD Kpt prefix coverage of active originals.

The old source-coordinate selected-level set is the TRUE Rold.I0.
The bound remains conditional on the old finite U and is NOT
a diary-uniform bound or a global BRD proof. -/
theorem finiteNumericH_constructed_odd_quiet_outside_small_root_budget
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
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hSeeds : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoidK (U : Set (Fin N)))
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
          W.card ≤ U.card + 1 ∧
          F.card ≤ min M
            (U.card +
              (kpt_old_actual_selected_levels
                family X oldTop Rold).card + 1) ∧
          ∀ a : Nat,
            2*a+1 < oldTop →
            2*a+1 ∉ Rold.I (2*a+1) →
            2*a+1 ∉ F →
            KptCandidateOriginalOldPrefixCovered
              family L k M hAvoidL W X Y oldTop Rold (2*a+1) →
            NewRootNoNoveltyAtCut family
              (SMTree.Envelope.closure (admissibleKptSTree family)
                (Rold.I ((2*a+1)+1)) X)
              (SMTree.Envelope.closure (admissibleKptSTree family)
                (Rold.I ((2*a+1)+1)) Y)
              (2*a+1) := by
  classical
  let w : Fin M := ⟨hPosition k j k, hTarget⟩
  let Y : Set (AdmissibleKptNode family) :=
    finiteNumericH_bareTopRootSeeds
      family L k M j hAvoidL hTarget X
  obtain ⟨Rold,hOldTopSeed,_oldParams,_oldLive,
    _oldFinal,_oldInj,_oldPresent,_oldExact⟩ := hOldPhysical
  obtain ⟨W,hWCard,hY⟩ :=
    finiteNumericH_bare_root_small_original_pool
      family K L k b N M j hNM hBlock hTarget
      hBin hUn hDiag hAvoidK hAvoidL U X hSeeds
  have hOldLe : oldTop ≤ hPosition k (j-1) k+1 :=
    finiteNumericH_old_physical_top_le_new_chronological_top
      family K k N j oldTop hNTop hAvoidK
      (U : Set (Fin N)) X hSeeds hOldTopSeed
  have hRootFree : (finiteNumericH L k M).freeLevel w.val =
      hPosition k (j-1) k+1 :=
    finiteNumericH_top_freeLevel_exact L k M j hk hj hTarget
  have hBare :
      Y = X ∪
        ({(finiteNumericH L k M).kptOriginal family hAvoidL w} :
          Set (AdmissibleKptNode family)) := by
    change X ∪
      ((fun v : Fin M =>
        (finiteNumericH L k M).kptOriginal family hAvoidL v) ''
        ({w} : Set (Fin M))) = _
    simp only [Set.image_singleton]
  let F : Finset Nat :=
    KptPhysicalFinalStageFreeEnds family L k M W X oldTop Rold
  have hFCarrier : F.card ≤ M :=
    kpt_physical_final_freeend_cuts_card_le_carrier
      family L k M W X oldTop Rold
  have hFSelected :
      F.card ≤ W.card +
        (kpt_old_actual_selected_levels family X oldTop Rold).card :=
    kpt_physical_final_freeend_cuts_card_le_root_add_selected
      family L k M W X oldTop Rold
  have hFBound :
      F.card ≤ min M
        (U.card +
          (kpt_old_actual_selected_levels family X oldTop Rold).card + 1) := by
    apply Nat.le_min.mpr
    constructor
    · exact hFCarrier
    · omega
  refine ⟨Rold,W,F,hY,hWCard,hFBound,?_⟩
  intro a hCut hUnselected hNotF hPrefix
  let c : Nat := 2*a+1
  have hBoring : ¬ SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family)
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (Rold.I (c+1)) X) c := by
    intro hInteresting
    have hStep := (Rold.interesting_step c hCut hInteresting).1
    apply hUnselected
    rw [hStep]
    exact Set.mem_insert_iff.mpr (Or.inl rfl)
  have hRootNe :
      (finiteNumericH L k M).freeLevel w.val ≠ c := by
    rw [hRootFree]
    omega
  have hNoEnd :
      ∀ v : Fin M,
        v ∈ ambientStagePool (finiteNumericH L k M)
          (W : Set (Fin M)) (Rold.I (c+1)) →
        (finiteNumericH L k M).freeLevel v.val ≠ c :=
    kpt_physical_no_stage_free_end_outside_final
      family L k M W X oldTop Rold c hCut hNotF
  exact finiteNumericH_old_boring_one_bare_odd_noNovelty_general
    family L k M hAvoidL hSymL W X Y hY w hBare
    oldTop Rold a hBoring hRootNe hNoEnd hPrefix

end Kk

#check @Kk.finiteNumericH_bare_root_small_original_pool
#print axioms Kk.finiteNumericH_bare_root_small_original_pool
#check @Kk.finiteNumericH_constructed_odd_quiet_outside_small_root_budget
#print axioms Kk.finiteNumericH_constructed_odd_quiet_outside_small_root_budget
