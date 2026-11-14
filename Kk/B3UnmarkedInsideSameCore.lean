import Kk.B3MissingMarkedOneCore
import Kk.B3PhysicalBadCoreIff
import Mathlib.Tactic

/-!
# Track D: one offending forbidden clique contains an actually UNMARKED original

PR #177's preceding same-clique theorem finds an upper clique vertex
with a FULL physical original whose complete next-cut ordinary L-type
is absent from the B3-good marked chosen-output spectrum. A name
need not be unmarked without source-choice coherence!

When genuine Marked originals represent nodes in ONE true physical
Kpt closure Z and no (I2) competing meet occurs there at the cut,
the checked complete L+ fibre-coherence theorem makes EVERY
eligible Marked original's own next L-reduct a genuinely chosen
marked output. Thus a missing output forces its SAME physical
clique label to be UNMARKED. The exact missing type remains.

English proof + 14 hostile checks preceded Lean:
docs/audits/2026-11-14-track-d-same-core-unmarked-of-noI2-english.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A complete next-cut L type of a genuinely selected, cut-eligible
original missing from the ACTUAL chosen Marked prescribed outputs
cannot come from a marked physical original if that marked pool is
genuinely represented in ONE no-(I2) Kpt closure.

Without no-(I2) the conclusion can fail due to deduplication of
equal old L+ sources with different next output types. -/
theorem missing_nextL_type_of_marked_closure_implies_unmarked_noI2
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (cut : Nat) (original : Fin M → Fin A.size)
    (Z : Set (AdmissibleKptNode family))
    (Marked : Fin M → Prop)
    (hRepresented : ∀ v : Fin M, Marked v →
      closureSelectedOriginal family A hAvoid original Z cut v)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode family,
      a ∈ Z ∧ ∃ b : AdmissibleKptNode family,
        b ∈ Z ∧ SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut)
    (v : Fin M)
    (hEligible : cut+1 ≤ A.freeLevel (original v).val)
    (hMissing :
      ¬ (selectedStagePoolPrescribedData A cut original Marked).PrescribedUpperLType
        ((A.partialTypeAt (cut+1) (original v).val).lReduct)) :
    ¬ Marked v := by
  intro hMarked
  exact hMissing
    (selected_named_nextL_permitted_of_no_I2
      family A hAvoid cut original Z Marked
      hRepresented hNoI2 v hMarked hEligible)

/-- For one genuine finite K_ell-free Henson cut, a failed FULL
corrected B3 with a B3-good nonempty marked source yields ONE finite
forbidden L-only K_ell clique through the cut and an UPPER VERTEX
whose SAME genuine physical original is:

* FULL-selected;
* genuinely cut-eligible;
* physically positively adjacent to the cut;
* of the EXACT complete next-cut directed ordinary L type of V;
* NOT in the ACTUAL chosen marked output-type spectrum; and
* NOT MARKED.

Last condition requires full no-(I2) coherence of genuine Marked
closure representations. This is not a selected-diary graph-age
loss theorem and retains auxiliary q2-like original names. -/
theorem henson_failed_fullB3_good_marked_has_unmarked_inside_same_core_of_noI2
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
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (Z : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (hMarkedRepresented : ∀ v : Fin M, Marked v →
      closureSelectedOriginal (hensonForbiddenFamily ell hell)
        (finiteNumericH (normalizedGraphModel E) k N)
        hAvoid original Z cut v)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      a ∈ Z ∧ ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        b ∈ Z ∧ SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut)
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
          Full v ∧ ¬ Marked v ∧
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
  let A := finiteNumericH (normalizedGraphModel E) k N
  obtain ⟨V,e,hFinite,hSocle,hDelete,hCopy,hAt,hFuture,
      a,hUpper,v,hFull,hFree,hEdge,hType,hMissing⟩ :=
    henson_failed_fullB3_good_marked_has_missing_type_inside_one_core
      ell hell k hK E hLoops hSym hClique
      N cut M hCut original Full Marked w hw hwEligible
      hFullFailure hMarkedGood
  have hNotMarked : ¬ Marked v :=
    missing_nextL_type_of_marked_closure_implies_unmarked_noI2
      (hensonForbiddenFamily ell hell)
      A hAvoid cut original Z Marked
      hMarkedRepresented hNoI2 v hFree hMissing
  exact ⟨V,e,hFinite,hSocle,hDelete,hCopy,hAt,hFuture,
    a,hUpper,v,hFull,hNotMarked,hFree,hEdge,hType,hMissing⟩

#print axioms missing_nextL_type_of_marked_closure_implies_unmarked_noI2
#print axioms henson_failed_fullB3_good_marked_has_unmarked_inside_same_core_of_noI2

end Kk
