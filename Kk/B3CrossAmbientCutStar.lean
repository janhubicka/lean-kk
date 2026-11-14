import Kk.B3CrossAmbientProfile
import Kk.B3CutStarNormalForm
import Mathlib.Tactic

/-!
# Track B: full corrected B3 comparison between TWO Henson occurrences

English-first mathematical proof and hostile audit:
  docs/track_b_cross_ambient_cutstar_english_audit.md

The two finite numerical-Henson ambients, original-name universes,
full Kpt closure sets and auxiliary E records can be DIFFERENT.
At a COMMON source-coordinate cut, agreement of the old ordinary-L
socle and of the complete permitted upper-L reduct predicates on
the genuine unanchored cut stars implies agreement of the FULL
corrected B3 test.

The complete physical hypotheses for each occurrence are packaged
in HensonCutOccurrence rather than silently inferred from a
selected-front macrodiary. No claim of an occurrence-independent
diary, synchronized full event trace, or labelled inverse orbit.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- One fully physical FINITE Henson occurrence at one common
SOURCE-coordinate cut. Every field is an actual obligation
for applying the cross-occurrence corrected-B3 theorem.

Different occurrences may have unrelated named-original
carriers, selected sets and parameter-closed source nodes. -/
structure HensonCutOccurrence (ell cut : Nat) (hell : 2 ≤ ell) where
  k : Nat
  hK : ell ≤ k+1
  N : Nat
  M : Nat
  E : Nat → Nat → Bool
  hLoops : ∀ i, E i i = false
  hSym : ∀ x y, E x y = E y x
  hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
    (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true)
  hCut : cut < N
  original : Fin M → Fin N
  hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
    bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L
  Z : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell))
  Full : Fin M → Prop
  hRepresented : ∀ v : Fin M, Full v →
    closureSelectedOriginal (hensonForbiddenFamily ell hell)
      (finiteNumericH (normalizedGraphModel E) k N)
      hAvoid original Z cut v
  hNoI2 : ¬ ∃ a : AdmissibleKptNode (hensonForbiddenFamily ell hell),
    a ∈ Z ∧ ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      b ∈ Z ∧ SMTree.Envelope.SameComponent a b ∧
      LevelTree.lev (LevelTree.meet a b) = cut

namespace HensonCutOccurrence

variable {ell cut : Nat} {hell : 2 ≤ ell}

noncomputable abbrev ambient (P : HensonCutOccurrence ell cut hell) :
    EnumeratedPartialStructure 1 0 1 :=
  finiteNumericH (normalizedGraphModel P.E) P.k P.N

abbrev starNames (P : HensonCutOccurrence ell cut hell) : Fin P.M → Prop :=
  hensonCutStarNames P.E P.k P.N cut P.M P.original P.Full

noncomputable abbrev fullProfile
    (P : HensonCutOccurrence ell cut hell) :
    PrescribedBoringData cut 1 0 1 :=
  selectedStagePoolPrescribedData P.ambient cut P.original P.Full

noncomputable abbrev starProfile
    (P : HensonCutOccurrence ell cut hell) :
    PrescribedBoringData cut 1 0 1 :=
  selectedStagePoolPrescribedData P.ambient cut P.original P.starNames

/-- The checked anchor-free Track D theorem specializes to each
individual physical Henson occurrence, including the empty cut-star.
This is an internal adapter used by the cross-ambient endpoints. -/
private theorem full_B3_iff_star_B3
    (P : HensonCutOccurrence ell cut hell) :
    P.fullProfile.CorrectedB3 (hensonForbiddenFamily ell hell) ↔
    P.starProfile.CorrectedB3 (hensonForbiddenFamily ell hell) := by
  exact henson_fullB3_iff_cut_star_of_no_i2
    ell hell P.k P.hK P.E P.hLoops P.hSym P.hClique
    P.N cut P.M P.hCut P.original P.Z P.Full
    P.hAvoid P.hRepresented P.hNoI2

/-- The finite full corrected-(B3) test is an INTER-AMBIENT
invariant of the exact old ordinary-L socle and the COMPLETE
cut-star upper L-reduct spectrum.

No shared ambient, original-name set, Kpt closure set, auxiliary E,
anchor, labelled inverse source, or nonempty cut-star is assumed.
The common source-coordinate cut remains essential. -/
theorem full_B3_crossAmbient_iff_of_cutStar_profiles
    (P Q : HensonCutOccurrence ell cut hell)
    (hOld : SameInitialL P.ambient.L Q.ambient.L cut)
    (hUpper : ∀ R,
      P.starProfile.PrescribedUpperLType R ↔
      Q.starProfile.PrescribedUpperLType R) :
    P.fullProfile.CorrectedB3 (hensonForbiddenFamily ell hell) ↔
    Q.fullProfile.CorrectedB3 (hensonForbiddenFamily ell hell) := by
  have hCross :
      P.starProfile.CorrectedB3 (hensonForbiddenFamily ell hell) ↔
      Q.starProfile.CorrectedB3 (hensonForbiddenFamily ell hell) :=
    selectedStagePool_crossAmbient_B3_iff_equal_upperL
      (hensonForbiddenFamily ell hell)
      P.ambient Q.ambient cut P.hCut Q.hCut
      P.original Q.original P.starNames Q.starNames
      hOld hUpper
  exact (full_B3_iff_star_B3 P).trans
    (hCross.trans (full_B3_iff_star_B3 Q).symm)

/-- If the FULL corrected-B3 test FAILS in the first occurrence
and PASSES in the second, their cut-star profiles differ in a
specific direction: some genuine, cut-ELIGIBLE, PHYSICALLY
cut-adjacent original of the failing occurrence has a COMPLETE
next-level ordinary-L reduct missing from the good occurrence.

This physical witness is obtained without presupposing which
auxiliary cut-star type is missing. The two ambients may differ.
It is NOT a common labelled source-orbit construction. -/
theorem failing_full_B3_has_unmatched_cutStar_original
    (P Q : HensonCutOccurrence ell cut hell)
    (hOld : SameInitialL P.ambient.L Q.ambient.L cut)
    (hFailed : ¬ P.fullProfile.CorrectedB3 (hensonForbiddenFamily ell hell))
    (hPassed : Q.fullProfile.CorrectedB3 (hensonForbiddenFamily ell hell)) :
    ∃ v : Fin P.M,
      P.Full v ∧
      (finiteNumericHL (normalizedGraphModel P.E) P.k P.N).binary
        cut (P.original v).val (0 : Fin 1) = true ∧
      cut+1 ≤ P.ambient.freeLevel (P.original v).val ∧
      ¬ Q.starProfile.PrescribedUpperLType
        ((P.ambient.partialTypeAt (cut+1) (P.original v).val).lReduct) := by
  classical
  have hStarFailed :
      ¬ P.starProfile.CorrectedB3 (hensonForbiddenFamily ell hell) := by
    intro hGood
    exact hFailed ((full_B3_iff_star_B3 P).2 hGood)
  have hStarPassed :
      Q.starProfile.CorrectedB3 (hensonForbiddenFamily ell hell) :=
    (full_B3_iff_star_B3 Q).1 hPassed
  have hNoUpperInclusion :
      ¬ ∀ R, P.starProfile.PrescribedUpperLType R →
          Q.starProfile.PrescribedUpperLType R := by
    intro hInclusion
    have hTransfer :
        P.starProfile.CorrectedB3 (hensonForbiddenFamily ell hell) :=
      selectedStagePool_crossAmbient_B3_of_upperL
        (hensonForbiddenFamily ell hell)
        P.ambient Q.ambient cut P.hCut Q.hCut
        P.original Q.original P.starNames Q.starNames
        hOld hInclusion hStarPassed
    exact hStarFailed hTransfer
  have hMissingUpper : ∃ R,
      P.starProfile.PrescribedUpperLType R ∧
      ¬ Q.starProfile.PrescribedUpperLType R := by
    by_contra hNo
    apply hNoUpperInclusion
    intro R hR
    by_contra hMissing
    exact hNo ⟨R,hR,hMissing⟩
  obtain ⟨R,hInP,hNotInQ⟩ := hMissingUpper
  obtain ⟨S,hS,hReq⟩ := hInP
  obtain ⟨v,hStar,hFree,_hOld,hNext⟩ :=
    selectedStagePoolPrescribedData_source_original
      P.ambient cut P.original P.starNames S hS
  have hR : R =
      (P.ambient.partialTypeAt (cut+1) (P.original v).val).lReduct := by
    calc
      R = (P.starProfile.target S).lReduct := hReq
      _ = (P.ambient.partialTypeAt (cut+1) (P.original v).val).lReduct :=
        congrArg
          (fun T : PartialTypeWithE (cut+1) 1 0 1 => T.lReduct)
          hNext
  refine ⟨v,hStar.1,hStar.2,hFree,?_⟩
  rw [hR] at hNotInQ
  exact hNotInQ

end HensonCutOccurrence

#print axioms HensonCutOccurrence.full_B3_crossAmbient_iff_of_cutStar_profiles
#print axioms HensonCutOccurrence.failing_full_B3_has_unmatched_cutStar_original

end Kk
