import Kk.B3CutVisibleTransfer
import SuccessorTree.V10.I3ClosureSelectedCrossing
import Mathlib.Tactic

/-!
# Track D: no-(I2) gives complete next-type fibre coherence

When two ambient originals represent closure nodes above a cut and
have equal complete old L+ types, their representing closure nodes
have the SAME ancestor at that cut. If their next complete L+ types
differ, their meet has level exactly the cut, contradicting the
full-closure no-(I2) condition.

We first prove equality of the WHOLE next L+ records, then discharge
the previously explicit fibre-coherence premise in the conditional
marked-to-full corrected-B3 transfer. The sole remaining geometric
transfer premise is marked coverage of all genuinely eligible,
cut-adjacent full names (plus closure representation and nonempty
marked source). This premise is NOT proved for the canonical diary.

English proof and adversarial audit:
docs/audits/2026-11-13-track-d-no-i2-fibre-coherence-english.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- No-(I2) makes the complete next L+ record independent of the
represented marked ORIGINAL chosen for a fixed complete old L+ type.

This is a Kpt closure statement: every marked name has an actual
representing closure node above cut. There is no arbitrary E
expansion of an L-only B3 continuation. -/
theorem kpt_marked_next_full_type_eq_of_no_meet
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (original : Fin M → Fin A.size)
    (Z : Set (AdmissibleKptNode family))
    (cut : Nat)
    (Marked : Fin M → Prop)
    (hMarkedRepresented : ∀ v : Fin M, Marked v →
      closureSelectedOriginal family A hAvoid original Z cut v)
    (hNoMeet : ¬ ∃ a : AdmissibleKptNode family,
      a ∈ Z ∧ ∃ b : AdmissibleKptNode family,
        b ∈ Z ∧ SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut)
    (v w : Fin M) (hv : Marked v) (hw : Marked w)
    (hOld : A.partialTypeAt cut (original v).val =
      A.partialTypeAt cut (original w).val) :
    A.partialTypeAt (cut+1) (original v).val =
      A.partialTypeAt (cut+1) (original w).val := by
  obtain ⟨z,hz,hCutZ,hBelowZ⟩ := hMarkedRepresented v hv
  obtain ⟨z',hz',hCutW,hBelowW⟩ := hMarkedRepresented w hw
  have hOldRawV :
      (LevelTree.ancestor z cut (Nat.le_of_lt hCutZ)).val =
        (⟨cut,A.partialTypeAt cut (original v).val⟩ :
          RawPartialTypeNode db du dd) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid (original v) z hBelowZ cut (Nat.le_of_lt hCutZ)
  have hOldRawW :
      (LevelTree.ancestor z' cut (Nat.le_of_lt hCutW)).val =
        (⟨cut,A.partialTypeAt cut (original w).val⟩ :
          RawPartialTypeNode db du dd) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid (original w) z' hBelowW cut (Nat.le_of_lt hCutW)
  have hSameOld :
      LevelTree.ancestor z cut (Nat.le_of_lt hCutZ) =
        LevelTree.ancestor z' cut (Nat.le_of_lt hCutW) := by
    apply Subtype.ext
    calc
      (LevelTree.ancestor z cut (Nat.le_of_lt hCutZ)).val =
          (⟨cut,A.partialTypeAt cut (original v).val⟩ :
            RawPartialTypeNode db du dd) := hOldRawV
      _ = (⟨cut,A.partialTypeAt cut (original w).val⟩ :
            RawPartialTypeNode db du dd) := by rw [hOld]
      _ = (LevelTree.ancestor z' cut (Nat.le_of_lt hCutW)).val :=
        hOldRawW.symm
  have hSameComp : SMTree.Envelope.SameComponent z z' := by
    refine ⟨LevelTree.ancestor z cut (Nat.le_of_lt hCutZ),
      LevelTree.ancestor_le z cut (Nat.le_of_lt hCutZ),?_⟩
    rw [hSameOld]
    exact LevelTree.ancestor_le z' cut (Nat.le_of_lt hCutW)
  have hNotMeet : LevelTree.lev (LevelTree.meet z z') ≠ cut := by
    intro h
    exact hNoMeet ⟨z,hz,z',hz',hSameComp,h⟩
  have hSameNext :
      LevelTree.ancestor z (cut+1) (Nat.succ_le_iff.mpr hCutZ) =
        LevelTree.ancestor z' (cut+1) (Nat.succ_le_iff.mpr hCutW) :=
    SMTree.Envelope.nextPrefix_eq_of_no_meet
      hCutZ hCutW hSameOld hNotMeet
  have hNextRawV :
      (LevelTree.ancestor z (cut+1) (Nat.succ_le_iff.mpr hCutZ)).val =
        (⟨cut+1,A.partialTypeAt (cut+1) (original v).val⟩ :
          RawPartialTypeNode db du dd) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid (original v) z hBelowZ (cut+1)
        (Nat.succ_le_iff.mpr hCutZ)
  have hNextRawW :
      (LevelTree.ancestor z' (cut+1) (Nat.succ_le_iff.mpr hCutW)).val =
        (⟨cut+1,A.partialTypeAt (cut+1) (original w).val⟩ :
          RawPartialTypeNode db du dd) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid (original w) z' hBelowW (cut+1)
        (Nat.succ_le_iff.mpr hCutW)
  have hPair :
      (⟨cut+1,A.partialTypeAt (cut+1) (original v).val⟩ :
        RawPartialTypeNode db du dd) =
      (⟨cut+1,A.partialTypeAt (cut+1) (original w).val⟩ :
        RawPartialTypeNode db du dd) := by
    calc
      (⟨cut+1,A.partialTypeAt (cut+1) (original v).val⟩ :
          RawPartialTypeNode db du dd) =
          (LevelTree.ancestor z (cut+1)
            (Nat.succ_le_iff.mpr hCutZ)).val :=
        hNextRawV.symm
      _ = (LevelTree.ancestor z' (cut+1)
            (Nat.succ_le_iff.mpr hCutW)).val :=
        congrArg Subtype.val hSameNext
      _ = (⟨cut+1,A.partialTypeAt (cut+1) (original w).val⟩ :
          RawPartialTypeNode db du dd) := hNextRawW
  exact eq_of_heq (Sigma.mk.inj_iff.mp hPair).2

/-- At an actual non-(I2) Henson closure stage, marked membership
among genuine represented closure originals has a unique complete
next L-type on every old-source fibre. Thus full corrected B3
follows from marked corrected B3 and genuine cut-neighbour
coverage, without an independent fibre-coherence assumption.

The coverage of all auxiliary cut-neighbours by the marked diary
branches remains explicitly UNPROVED. -/
theorem henson_fullB3_of_no_i2_marked_closure_cut_neighbours
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N cut M : Nat) (hCut : cut < N)
    (original : Fin M → Fin N)
    (familyAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (Z : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (Full Marked : Fin M → Prop)
    (hMarkedNonempty : ∃ v : Fin M, Marked v)
    (hMarkedRepresented : ∀ v : Fin M, Marked v →
      closureSelectedOriginal
        (hensonForbiddenFamily ell hell)
        (finiteNumericH (normalizedGraphModel E) k N)
        familyAvoid original Z cut v)
    (hNoMeet : ¬ ∃ a : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      a ∈ Z ∧ ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        b ∈ Z ∧ SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut)
    (hAllCutNeighboursMarked : ∀ v : Fin M, Full v →
      cut+1 ≤ (finiteNumericH (normalizedGraphModel E) k N).freeLevel
        (original v).val →
      (finiteNumericHL (normalizedGraphModel E) k N).binary
        cut (original v).val (0 : Fin 1) = true →
      Marked v)
    (hMarkedB3 :
      (selectedStagePoolPrescribedData
        (finiteNumericH (normalizedGraphModel E) k N)
        cut original Marked).CorrectedB3
          (hensonForbiddenFamily ell hell)) :
    (selectedStagePoolPrescribedData
      (finiteNumericH (normalizedGraphModel E) k N)
      cut original Full).CorrectedB3
        (hensonForbiddenFamily ell hell) := by
  classical
  let family := hensonForbiddenFamily ell hell
  let A := finiteNumericH (normalizedGraphModel E) k N
  have hEligibleMarked :
      ∃ v : Fin M, Marked v ∧ cut+1 ≤ A.freeLevel (original v).val := by
    obtain ⟨v,hMarked⟩ := hMarkedNonempty
    obtain ⟨z,_hz,hLev,hBelow⟩ := hMarkedRepresented v hMarked
    have hFree : LevelTree.lev z ≤ A.freeLevel (original v).val :=
      kptBelowOriginal_level_le_free
        family A familyAvoid (original v) z hBelow
    exact ⟨v,hMarked,by omega⟩
  have hCoherent : ∀ v w : Fin M,
      Marked v → Marked w →
      cut+1 ≤ A.freeLevel (original v).val →
      cut+1 ≤ A.freeLevel (original w).val →
      A.partialTypeAt cut (original v).val =
        A.partialTypeAt cut (original w).val →
      (A.partialTypeAt (cut+1) (original v).val).lReduct =
        (A.partialTypeAt (cut+1) (original w).val).lReduct := by
    intro v w hv hw _hVEligible _hWEligible hOld
    have hFullEq :
        A.partialTypeAt (cut+1) (original v).val =
          A.partialTypeAt (cut+1) (original w).val :=
      kpt_marked_next_full_type_eq_of_no_meet
        family A familyAvoid original Z cut Marked
        hMarkedRepresented hNoMeet v w hv hw hOld
    exact congrArg
      (fun T : PartialTypeWithE (cut+1) 1 0 1 => T.lReduct)
      hFullEq
  exact henson_fullB3_of_marked_cut_neighbours_and_fibre_coherence
    ell hell k hK E hLoops hSym hClique
    N cut M hCut original Full Marked
    hEligibleMarked hAllCutNeighboursMarked
    hCoherent hMarkedB3

#print axioms kpt_marked_next_full_type_eq_of_no_meet
#print axioms henson_fullB3_of_no_i2_marked_closure_cut_neighbours

end Kk
