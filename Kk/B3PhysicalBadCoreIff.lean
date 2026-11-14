import Kk.B3ExactCutStarWitness
import Kk.B3CrossAmbientProfile
import Mathlib.Tactic

/-!
# Track D: exact physical cut-star clique certificate for corrected-B3 FAILURE

We prove a genuine converse to the checked necessary finite cut-star
clique extraction. The converse needs the ACTUAL no-(I2) full Kpt
closure and genuine selected-name representation: those hypotheses
guarantee that a physical original's full next-cut L type is among
the CHOSEN prescribed outputs even when source deduplication selects
a different original with the same old full L+ source type.

The final equivalence is at ONE genuine finite Henson cut. It is not
the outstanding graph-age-loss / active macrodiary equivalence.

English proof and 17 hostile checks preceded Lean:
docs/audits/2026-11-14-track-d-physical-b3-core-iff-english.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The complete next ordinary-L type of a genuine represented and
cut-eligible selected original is an ACTUAL CHOSEN upper type of the
selected-stage prescribed function. No-(I2) makes chosen output
independent of representative in every full old L+ source fibre.

This repairs the false shortcut "selected name -> chosen target";
without no-(I2), equal old full L+ types may choose different next
outputs. No E is placed on an arbitrary age-test continuation. -/
theorem selected_named_nextL_permitted_of_no_I2
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (cut : Nat) (original : Fin M → Fin A.size)
    (Z : Set (AdmissibleKptNode family))
    (Selected : Fin M → Prop)
    (hRepresented : ∀ v : Fin M, Selected v →
      closureSelectedOriginal family A hAvoid original Z cut v)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode family,
      a ∈ Z ∧ ∃ b : AdmissibleKptNode family,
        b ∈ Z ∧ SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut)
    (v : Fin M) (hSelected : Selected v)
    (hEligible : cut+1 ≤ A.freeLevel (original v).val) :
    (selectedStagePoolPrescribedData A cut original Selected).PrescribedUpperLType
      (A.partialTypeAt (cut+1) (original v).val).lReduct := by
  classical
  let F : PrescribedBoringData cut db du dd :=
    selectedStagePoolPrescribedData A cut original Selected
  let T : PartialTypeWithE cut db du dd :=
    A.partialTypeAt cut (original v).val
  have hT : T ∈ F.source := by
    change ∃ u : Fin M,
      (Selected u ∧ cut+1 ≤ A.freeLevel (original u).val) ∧
      A.partialTypeAt cut (original u).val = T
    exact ⟨v,⟨hSelected,hEligible⟩,rfl⟩
  obtain ⟨w,hWSelected,_hWEligible,hOld,hTarget⟩ :=
    selectedStagePoolPrescribedData_source_original
      A cut original Selected T hT
  have hOldEq :
      A.partialTypeAt cut (original w).val =
        A.partialTypeAt cut (original v).val := by
    simpa only [T] using hOld.symm
  have hNextEq :
      A.partialTypeAt (cut+1) (original w).val =
        A.partialTypeAt (cut+1) (original v).val :=
    kpt_marked_next_full_type_eq_of_no_meet
      family A hAvoid original Z cut Selected
      hRepresented hNoI2 w v hWSelected hSelected hOldEq
  refine ⟨T,hT,?_⟩
  calc
    (A.partialTypeAt (cut+1) (original v).val).lReduct =
        (A.partialTypeAt (cut+1) (original w).val).lReduct :=
      congrArg
        (fun Q : PartialTypeWithE (cut+1) db du dd => Q.lReduct)
        hNextEq.symm
    _ = (F.target T).lReduct :=
      congrArg
        (fun Q : PartialTypeWithE (cut+1) db du dd => Q.lReduct)
        hTarget.symm

/-- A FINITE, L-only, PHYSICAL obstruction certificate to corrected B3
in a genuine finite numerical Henson structure. At least one truly
cut-eligible selected name is required, so the prescribed source
is not vacuously empty.

EVERY upper vertex of ONE forbidden clique core has a SINGLE actual
selected original that is both eligible and physically cut-adjacent
and whose entire directed next-cut L-prefix type matches it.
Upper--upper edges of the witness are unconstrained by physical H.

This certificate is NOT a selected-front integer graph-age loss and
does not prescribe auxiliary E on the witness. -/
def HensonPhysicalCutStarBadCore
    (ell : Nat) (hell : 2 ≤ ell)
    (k N cut M : Nat)
    (E : Nat → Nat → Bool)
    (original : Fin M → Fin N)
    (Selected : Fin M → Prop) : Prop :=
  let A : EnumeratedPartialStructure 1 0 1 :=
    finiteNumericH (normalizedGraphModel E) k N
  let C : AgeTestModel 1 0 1 :=
    finiteNumericHL (normalizedGraphModel E) k N
  ∃ v0 : Fin M, Selected v0 ∧
    cut+1 ≤ A.freeLevel (original v0).val ∧
    ∃ (V : AgeTestModel 1 0 1) (e : Fin ell → Nat),
      V.BoundedCarrier ∧ SameInitialL V C cut ∧
      (∀ bad, bad ∈ hensonForbiddenFamily ell hell →
        bad.Avoids (V.withoutVertex cut)) ∧
      V.Realizes (cliquePattern ell) e ∧
      (∃ a : Fin ell, e a = cut) ∧
      (∀ x, x ∈ V.carrier → cut < x →
        ∃ a : Fin ell, e a = x) ∧
      (∀ x, x ∈ V.carrier → cut < x →
        ∃ v : Fin M, Selected v ∧
          cut+1 ≤ A.freeLevel (original v).val ∧
          C.binary cut (original v).val (0 : Fin 1) = true ∧
          RelationalPrefixType.ofAgeModel V (cut+1) x =
            RelationalPrefixType.ofAgeModel C (cut+1) (original v).val)

/-- Exact two-sided characterization of full corrected-(B3) FAILURE
by ONE physically named finite L-only forbidden clique core.

The left-to-right direction requires no no-(I2) premise and uses
the verified finite clique-core theorem. In the converse,
genuine full closure representation and no-(I2) ensure that ALL
named physical upper L-types are ACTUAL CHOSEN prescribed outputs.

This is strictly local to one numerical Henson cut: it does not
establish that the selected diary graph age changes precisely at
these obstructions, which additionally requires fixed-source
relative realization and exact full B3-loss fidelity. -/
theorem henson_fullB3_failure_iff_physical_cut_star_bad_core_of_no_I2
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N cut M : Nat) (hCut : cut < N)
    (original : Fin M → Fin N)
    (Z : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (Selected : Fin M → Prop)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (hRepresented : ∀ v : Fin M, Selected v →
      closureSelectedOriginal
        (hensonForbiddenFamily ell hell)
        (finiteNumericH (normalizedGraphModel E) k N)
        hAvoid original Z cut v)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      a ∈ Z ∧ ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        b ∈ Z ∧ SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :
    ¬ (selectedStagePoolPrescribedData
      (finiteNumericH (normalizedGraphModel E) k N)
      cut original Selected).CorrectedB3 (hensonForbiddenFamily ell hell) ↔
    HensonPhysicalCutStarBadCore ell hell k N cut M E original Selected := by
  classical
  let K : AgeTestModel 1 0 1 := normalizedGraphModel E
  let A : EnumeratedPartialStructure 1 0 1 := finiteNumericH K k N
  let C : AgeTestModel 1 0 1 := finiteNumericHL K k N
  let F : PrescribedBoringData cut 1 0 1 :=
    selectedStagePoolPrescribedData A cut original Selected
  constructor
  · intro hFail
    obtain ⟨v0,hSel0,hEligible0,_hEdge0⟩ :=
      henson_failedSelectedB3_has_eligible_cut_neighbour
        ell hell k hK E hLoops hSym hClique
        N cut M hCut original Selected hFail
    obtain ⟨V,e,hFinite,hSocle,hDelete,hCopy,hAt,hFuture,hUpper⟩ :=
      henson_failed_selectedB3_has_exact_full_cut_star_core
        ell hell k hK E hLoops hSym hClique
        N cut M hCut original Selected hFail
    change HensonPhysicalCutStarBadCore ell hell k N cut M E original Selected
    unfold HensonPhysicalCutStarBadCore
    exact ⟨v0,hSel0,hEligible0,V,e,hFinite,hSocle,
      hDelete,hCopy,hAt,hFuture,hUpper⟩
  · intro hBad hGood
    change HensonPhysicalCutStarBadCore ell hell k N cut M E original Selected
      at hBad
    unfold HensonPhysicalCutStarBadCore at hBad
    obtain ⟨v0,hSel0,hEligible0,V,e,hFinite,hSocle,
      hDelete,hCopy,_hAt,_hFuture,hUpper⟩ := hBad
    let T0 : PartialTypeWithE cut 1 0 1 :=
      A.partialTypeAt cut (original v0).val
    have hT0 : T0 ∈ F.source := by
      change ∃ v : Fin M,
        (Selected v ∧ cut+1 ≤ A.freeLevel (original v).val) ∧
        A.partialTypeAt cut (original v).val = T0
      exact ⟨v0,⟨hSel0,hEligible0⟩,rfl⟩
    obtain ⟨w,_hWSelected,_hWEligible,_hOld,hTarget⟩ :=
      selectedStagePoolPrescribedData_source_original
        A cut original Selected T0 hT0
    have hChosenSocle :
        SameInitialL
          (prescribedOrdinarySocle (F.target T0))
          A.L cut := by
      rw [hTarget]
      exact ambient_partialType_prescribedSocle
        A cut (original w).val hCut
    have hRelativeSocle : SameInitialL V
        (prescribedOrdinarySocle (F.target T0)) cut :=
      hSocle.trans (crossAmbient_sameInitialL_reverse hChosenSocle)
    have hUpperChosen : UpperTypesPrescribed V cut
        F.PrescribedUpperLType := by
      intro x hx hAbove
      obtain ⟨v,hSelected,hEligible,_hCutEdge,hType⟩ :=
        hUpper x hx hAbove
      have hPermitted :
          F.PrescribedUpperLType
            (A.partialTypeAt (cut+1) (original v).val).lReduct :=
        selected_named_nextL_permitted_of_no_I2
          (hensonForbiddenFamily ell hell) A hAvoid
          cut original Z Selected hRepresented hNoI2
          v hSelected hEligible
      have hActualReduct :
          (A.partialTypeAt (cut+1) (original v).val).lReduct =
            RelationalPrefixType.ofAgeModel C (cut+1)
              (original v).val :=
        partialTypeAt_lReduct_eq_ofAgeModel
          A (cut+1) (original v).val
      have hWitnessReduct :
          RelationalPrefixType.ofAgeModel V (cut+1) x =
            (A.partialTypeAt (cut+1) (original v).val).lReduct :=
        hType.trans hActualReduct.symm
      rw [hWitnessReduct]
      exact hPermitted
    have hAvoidV := hGood T0 hT0 V hFinite
      hRelativeSocle hUpperChosen
      hDelete
    let bad : NormalizedForbidden 1 0 1 :=
      .nontrivial ell (cliquePattern ell) (by omega)
        (cliquePattern_irreducible ell)
    have hBadMem : bad ∈ hensonForbiddenFamily ell hell := by
      simp [bad, hensonForbiddenFamily]
    have hNoCopy := hAvoidV bad hBadMem
    exact hNoCopy ⟨e,hCopy⟩

#print axioms selected_named_nextL_permitted_of_no_I2
#print axioms henson_fullB3_failure_iff_physical_cut_star_bad_core_of_no_I2

end Kk
