import Kk.B3ExactCutStarWitness
import Kk.B3ActualI3ExtraUpper
import Kk.B3CrossAmbientProfile
import Mathlib.Tactic

/-!
# Track D: missing marked type in the SAME physically labelled full B3 clique

The old missing-upper-original lemma gives some FULL physical type
missing from a B3-good marked source, but not a vertex in the actual
forbidden clique which witnesses the full B3 failure.

The sharpened theorem extracts ONE finite L-only forbidden core V
and ONE clique e containing the tested cut. Every upper V vertex is
a genuine eligible, physically cut-adjacent FULL name with its
COMPLETE next L type. When the marked source is B3-good and contains
one eligible name, SOME UPPER VERTEX OF THAT VERY CLIQUE has a complete
type NOT among the marked chosen prescribed outputs.

No no-(I2) hypothesis is needed for this missing-type conclusion:
we do not infer a chosen output from merely marking a name.
No E is assigned to the finite L-age witness and the upper-upper
edges of V remain freely choosable.

English-first proof and 17 hostile checks:
docs/audits/2026-11-14-track-d-missing-marked-in-same-core-english.md
-/

namespace Kk

open SuccessorTree.V10

/-- In a genuine finite Henson graph, if the FULL selected-stage
corrected B3 test fails but a nonempty, genuinely cut-eligible
MARKED selected-stage source passes corrected B3, then there is
ONE finite forbidden K_ell clique core through the cut with
ONE UPPER CLIQUE VERTEX whose COMPLETE next-cut ordinary L type
is supplied by a real FULL-selected, cut-eligible and physically
cut-adjacent original but is MISSING from the ACTUAL CHOSEN marked
upper-L profile.

The same chosen V/e witnesses all clauses. The missing source
original need not lie in the marked active diary and may be an
auxiliary parameter. This is not the selected graph-age-loss bridge.

No no-(I2) hypothesis is required. -/
theorem henson_failed_fullB3_good_marked_has_missing_type_inside_one_core
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N cut M : Nat) (hCut : cut < N)
    (original : Fin M → Fin N)
    (Full Marked : Fin M → Prop)
    (w : Fin M) (hw : Marked w)
    (hwEligible :
      cut+1 ≤ (finiteNumericH (normalizedGraphModel E) k N).freeLevel
        (original w).val)
    (hFullFailure :
      ¬ (selectedStagePoolPrescribedData
        (finiteNumericH (normalizedGraphModel E) k N)
        cut original Full).CorrectedB3
          (hensonForbiddenFamily ell hell))
    (hMarkedGood :
      (selectedStagePoolPrescribedData
        (finiteNumericH (normalizedGraphModel E) k N)
        cut original Marked).CorrectedB3
          (hensonForbiddenFamily ell hell)) :
    ∃ (V : AgeTestModel 1 0 1) (e : Fin ell → Nat),
      V.BoundedCarrier ∧
      SameInitialL V
        (finiteNumericHL (normalizedGraphModel E) k N) cut ∧
      (∀ bad, bad ∈ hensonForbiddenFamily ell hell →
        bad.Avoids (V.withoutVertex cut)) ∧
      V.Realizes (cliquePattern ell) e ∧
      (∃ a : Fin ell, e a = cut) ∧
      (∀ x, x ∈ V.carrier → cut < x →
        ∃ a : Fin ell, e a = x) ∧
      (∃ a : Fin ell, cut < e a ∧
        ∃ v : Fin M,
          Full v ∧
          cut+1 ≤ (finiteNumericH (normalizedGraphModel E) k N).freeLevel
            (original v).val ∧
          (finiteNumericHL (normalizedGraphModel E) k N).binary
            cut (original v).val (0 : Fin 1) = true ∧
          RelationalPrefixType.ofAgeModel V (cut+1) (e a) =
            RelationalPrefixType.ofAgeModel
              (finiteNumericHL (normalizedGraphModel E) k N)
              (cut+1) (original v).val ∧
          ¬ (selectedStagePoolPrescribedData
            (finiteNumericH (normalizedGraphModel E) k N)
            cut original Marked).PrescribedUpperLType
              ((finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
                (cut+1) (original v).val).lReduct) := by
  classical
  let A := finiteNumericH (normalizedGraphModel E) k N
  let C := finiteNumericHL (normalizedGraphModel E) k N
  let G := selectedStagePoolPrescribedData A cut original Marked
  obtain ⟨V,e,hFinite,hSocle,hDelete,hCopy,hAt,hFuture,hUpper⟩ :=
    henson_failed_selectedB3_has_exact_full_cut_star_core
      ell hell k hK E hLoops hSym hClique
      N cut M hCut original Full hFullFailure
  let T0 : PartialTypeWithE cut 1 0 1 :=
    A.partialTypeAt cut (original w).val
  have hT0 : T0 ∈ G.source := by
    change ∃ v : Fin M,
      (Marked v ∧ cut+1 ≤ A.freeLevel (original v).val) ∧
      A.partialTypeAt cut (original v).val = T0
    exact ⟨w,⟨hw,hwEligible⟩,rfl⟩
  obtain ⟨u,_hUSelected,_hUFree,_hOld,hTarget⟩ :=
    selectedStagePoolPrescribedData_source_original
      A cut original Marked T0 hT0
  have hChosenSocle :
      SameInitialL (prescribedOrdinarySocle (G.target T0))
        A.L cut := by
    rw [hTarget]
    exact ambient_partialType_prescribedSocle
      A cut (original u).val hCut
  have hRelativeSocle :
      SameInitialL V
        (prescribedOrdinarySocle (G.target T0)) cut :=
    hSocle.trans (crossAmbient_sameInitialL_reverse hChosenSocle)
  refine ⟨V,e,hFinite,hSocle,hDelete,hCopy,hAt,hFuture,?_⟩
  by_contra hNoMissing
  have hUpperMarked : UpperTypesPrescribed V cut
      G.PrescribedUpperLType := by
    intro x hx hAbove
    obtain ⟨a,ha⟩ := hFuture x hx hAbove
    obtain ⟨v,hFull,hFree,hEdge,hType⟩ := hUpper x hx hAbove
    have hActualType :
        (A.partialTypeAt (cut+1) (original v).val).lReduct =
          RelationalPrefixType.ofAgeModel C
            (cut+1) (original v).val :=
      partialTypeAt_lReduct_eq_ofAgeModel
        A (cut+1) (original v).val
    have hVType :
        RelationalPrefixType.ofAgeModel V (cut+1) x =
          (A.partialTypeAt (cut+1) (original v).val).lReduct :=
      hType.trans hActualType.symm
    by_contra hNotPermitted
    have hMissingV : ¬ G.PrescribedUpperLType
        ((A.partialTypeAt (cut+1) (original v).val).lReduct) := by
      intro hAllowed
      apply hNotPermitted
      rw [hVType]
      exact hAllowed
    apply hNoMissing
    refine ⟨a,?_,v,hFull,hFree,hEdge,?_,hMissingV⟩
    · rw [ha]
      exact hAbove
    · rw [ha]
      exact hType
  have hAvoidV := hMarkedGood T0 hT0 V
    hFinite hRelativeSocle hUpperMarked hDelete
  let bad : NormalizedForbidden 1 0 1 :=
    .nontrivial ell (cliquePattern ell) (by omega)
      (cliquePattern_irreducible ell)
  have hBadMember : bad ∈ hensonForbiddenFamily ell hell := by
    simp [bad, hensonForbiddenFamily]
  exact (hAvoidV bad hBadMember) ⟨e,hCopy⟩

#print axioms henson_failed_fullB3_good_marked_has_missing_type_inside_one_core

end Kk
