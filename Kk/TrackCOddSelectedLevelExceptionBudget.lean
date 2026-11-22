import Kk.TrackCOddFinalFreeEndSupport
import Kk.TrackESelectedLevelOriginalBudget
import Mathlib.Tactic

/-!
# Track C: odd physical E-free-end exceptions cost actual roots + selected old levels

English FIRST, adversarially audited:
 docs/track_c_odd_selected_exception_budget_english_audit_20261122.md

For one actual normalized Kpt AlgorithmRun, let F be the image under
physical auxiliary E-freeLevel of the COMPLETE final old stage
of original coordinates W union selected original addresses.
The existing bound |F| <= M overcounts arbitrarily padded physical
carriers. Track E E86 bounds the real final stage by
|W| + |the ACTUAL selected old source levels Rold.I0|.
Consequently |F| <= min(M, |W| + |SelectedOld|).

We use EXACTLY the same genuine chronological old run and stage
pool to recover full conditional no-novelty at safe odd cuts outside
this sharpened finite F. This is NOT a diary-uniform bound until
both W and SelectedOld are controlled by the abstract diary.

Old-prefix witnesses, exceptional E cuts, nonzero real cuts,
taller new AlgorithmRun and common labelled inverse-source orbits
remain outside the claim.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The number of DISTINCT actual odd-source candidate original
E-free endpoints is at most the number of original roots W plus
the number of ACTUALLY selected old source levels.

It is independent of padding M and of numerical boring gaps, except
through the literal physical pool W and true old selected-level set.
No assertion that freeLevel is injective is needed. -/
theorem kpt_physical_final_freeend_cuts_card_le_root_add_selected
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (W : Finset (Fin M))
    (X : Set (AdmissibleKptNode family))
    (oldTop : Nat)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop) :
    (KptPhysicalFinalStageFreeEnds
      family L k M W X oldTop Rold).card ≤
      W.card +
        (kpt_old_actual_selected_levels family X oldTop Rold).card := by
  classical
  change
    ((hStageOriginals L k M W (Rold.I 0)).image
      (fun v : Fin M =>
        (finiteNumericH L k M).freeLevel v.val)).card ≤
        W.card +
          (kpt_old_actual_selected_levels family X oldTop Rold).card
  calc
    ((hStageOriginals L k M W (Rold.I 0)).image
      (fun v : Fin M =>
        (finiteNumericH L k M).freeLevel v.val)).card ≤
        (hStageOriginals L k M W (Rold.I 0)).card :=
      Finset.card_image_le
    _ ≤ W.card +
        (kpt_old_actual_selected_levels family X oldTop Rold).card :=
      finiteNumericH_old_run_final_stage_originals_card_le_root_add_selected
        family L k M W X oldTop Rold

/-- Combine the genuinely distinct two bounds: physical carrier M
and roots-plus-selected-levels. This is stronger than the existing
per-carrier |F|<=M claim and uses the ACTUAL full stage. -/
theorem kpt_physical_final_freeend_cuts_card_le_min_selected_carrier
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (W : Finset (Fin M))
    (X : Set (AdmissibleKptNode family))
    (oldTop : Nat)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop) :
    (KptPhysicalFinalStageFreeEnds
      family L k M W X oldTop Rold).card ≤
      min M
        (W.card +
          (kpt_old_actual_selected_levels family X oldTop Rold).card) :=
  Nat.le_min.mpr
    ⟨kpt_physical_final_freeend_cuts_card_le_carrier
       family L k M W X oldTop Rold,
     kpt_physical_final_freeend_cuts_card_le_root_add_selected
       family L k M W X oldTop Rold⟩

/-- For the TRUE numerical-H+ chronological one-bare-root extension,
construct one genuine old Kpt run Rold, its COMPLETE original pool W,
and a *concrete* E-free-end exception set F whose cardinal is
bounded by MIN(M, root count + actual selected old-level count).

Every old-unselected odd cut outside F is FULL new-root quiet,
assuming only the genuine COMPLETE OLD prefix coverage of all
active original sources. No per-cut endpoint hypothesis remains.

The proof constructs the SAME F from the SAME W and Rold as the
actual full-stage chronology; it does not refine an arbitrary
previous existential F or equate old and taller new runs. -/
theorem finiteNumericH_constructed_odd_quiet_outside_selected_budget
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
          F.card ≤ min M
            (W.card +
              (kpt_old_actual_selected_levels
                family X oldTop Rold).card) ∧
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
  let Y : Set (AdmissibleKptNode family) :=
    finiteNumericH_bareTopRootSeeds
      family L k M j hAvoidL hTarget X
  obtain ⟨Rold,W,hY,hOdd⟩ :=
    finiteNumericH_constructed_bare_odd_quiet_of_stage_free_and_socle
      family K L k b N M j
      hNM hBlock hk hj hTarget hNTop
      hBin hUn hDiag hAvoidK hAvoidL hSymL
      U X hSeeds oldTop hOldPhysical
  let F : Finset Nat :=
    KptPhysicalFinalStageFreeEnds family L k M W X oldTop Rold
  have hCard : F.card ≤
      min M
        (W.card +
          (kpt_old_actual_selected_levels family X oldTop Rold).card) :=
    kpt_physical_final_freeend_cuts_card_le_min_selected_carrier
      family L k M W X oldTop Rold
  refine ⟨Rold,W,F,hY,hCard,?_⟩
  intro a hCut hOldUnselected hNotF hPrefix
  have hNoEnd :
      ∀ v : Fin M,
        v ∈ ambientStagePool (finiteNumericH L k M)
          (W : Set (Fin M)) (Rold.I ((2*a+1)+1)) →
        (finiteNumericH L k M).freeLevel v.val ≠ 2*a+1 :=
    kpt_physical_no_stage_free_end_outside_final
      family L k M W X oldTop Rold (2*a+1) hCut hNotF
  exact hOdd a hCut hOldUnselected hNoEnd hPrefix

end Kk

#check @Kk.kpt_physical_final_freeend_cuts_card_le_root_add_selected
#print axioms Kk.kpt_physical_final_freeend_cuts_card_le_root_add_selected
#check @Kk.kpt_physical_final_freeend_cuts_card_le_min_selected_carrier
#print axioms Kk.kpt_physical_final_freeend_cuts_card_le_min_selected_carrier
#check @Kk.finiteNumericH_constructed_odd_quiet_outside_selected_budget
#print axioms Kk.finiteNumericH_constructed_odd_quiet_outside_selected_budget
