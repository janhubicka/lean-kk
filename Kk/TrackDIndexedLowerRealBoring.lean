import Kk.ActualRunLowerRealNoI3OfBaseCoverage
import Kk.NumericHI2FullFork
import Mathlib.Tactic

/-!
# Track D: genuine lower-real boringness from an exhaustive finite Kpt index

English proof and adversarial hypothesis audit committed BEFORE this source:
docs/audits/2026-11-18-track-d-exhaustive-index-boring-cut-english.md

This combines the true final-source and pre-cut live-index masks with the
FULL I1/I2/fork equivalence and the already checked physical full-B3 criterion.
It does NOT establish the finite certificates from a canonical diary, nor any
global common labelled source or BRD characterization.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Exhaustively enumerating the TRUE final Kpt source, with the exact
actual-run pre-cut membership mask, converts two finite tests into
absence of BOTH full structural obstructions:
  * no live node has level = cut (I1);
  * no two live strictly crossing nodes share the complete old L+/E record
    while differing in the complete upper L+/E record (I2).
The closure is taken at R.I(cut+1), NOT at a selected-front proxy.
No source node/auxiliary parameter/meet may be dropped. -/
theorem finiteNumericH_run_no_I1_I2_of_complete_index_checks
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Set (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hSeeds : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid U)
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (params : Finset (AdmissibleKptNode family))
    (hParams : ∀ z : AdmissibleKptNode family,
      z ∈ params ↔
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I 0) X)
    (presentAt : Nat → Fin params.card → Bool)
    (hPresent : ∀ cut : Nat, ∀ i : Fin params.card,
      presentAt cut i = true ↔
        (params.equivFin.symm i).val ∈
          SMTree.Envelope.closure
            (admissibleKptSTree family) (R.I (cut+1)) X)
    (cut : Nat) (hCut : cut < top)
    (hNoActiveI1 : ∀ i : Fin params.card,
      presentAt cut i = true →
        LevelTree.lev (params.equivFin.symm i).val ≠ cut)
    (hNoActiveFork : ¬ ∃ i j : Fin params.card,
      presentAt cut i = true ∧ presentAt cut j = true ∧
      cut < LevelTree.lev (params.equivFin.symm i).val ∧
      cut < LevelTree.lev (params.equivFin.symm j).val ∧
      kptFullOldAtCut (params.equivFin.symm i).val cut =
        kptFullOldAtCut (params.equivFin.symm j).val cut ∧
      kptFullUpperAtCut (params.equivFin.symm i).val cut ≠
        kptFullUpperAtCut (params.equivFin.symm j).val cut) :
    (¬ ∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X ∧
      LevelTree.lev z = cut) ∧
    (¬ ∃ a : AdmissibleKptNode family,
      a ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X ∧
      ∃ b : AdmissibleKptNode family,
        b ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) X ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) := by
  classical
  let Z : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (R.I (cut+1)) X
  have hLevels : R.I (cut+1) ⊆ R.I 0 := by
    intro q hq
    rw [R.I_eq_final_tail_of_run (cut+1) (by omega)] at hq
    exact hq.1
  have hStage : Z ⊆
      SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I 0) X :=
    envelope_closure_mono_levels
      (admissibleKptSTree family)
      (R.I (cut+1)) (R.I 0) X hLevels
  have hNoI1 : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ Z ∧ LevelTree.lev z = cut := by
    rintro ⟨z,hz,hLevel⟩
    have hFin : z ∈ params := (hParams z).2 (hStage hz)
    let i : Fin params.card := params.equivFin ⟨z,hFin⟩
    have hi : (params.equivFin.symm i).val = z := by simp [i]
    have hLive : presentAt cut i = true := by
      apply (hPresent cut i).2
      simpa only [hi] using hz
    exact (hNoActiveI1 i hLive) (by simpa only [hi] using hLevel)
  have hNoI2 : ¬ ∃ a : AdmissibleKptNode family,
      a ∈ Z ∧ ∃ b : AdmissibleKptNode family,
        b ∈ Z ∧ SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut := by
    intro hMeet
    have hFork :=
      (finiteNumericH_run_no_I1_I2_iff_indexed_full_fork
        family K k N hAvoid U X hSeeds top R
        params hParams presentAt hPresent cut hCut hNoI1).mp hMeet
    exact hNoActiveFork hFork
  exact ⟨hNoI1,hNoI2⟩

/-- A verifiable *single-cut* physical nonselection criterion.
The finite index supplies BOTH actual structural exclusions. The
remaining certificate is explicitly about the genuine physically
represented complete source, including auxiliary originals and meets;
it is not inferred from a selected macrodiary.

The certificate is parametrized by the proved no-I2 property solely
because actualHensonRunCutOccurrence packages that property into P. -/
theorem henson_actualRun_lower_real_unselected_of_indexed_full_checks
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
    (params : Finset (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (hParams : ∀ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      z ∈ params ↔
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily ell hell))
          (Run.I 0) X)
    (presentAt : Nat → Fin params.card → Bool)
    (hPresent : ∀ cut : Nat, ∀ i : Fin params.card,
      presentAt cut i = true ↔
        (params.equivFin.symm i).val ∈
          SMTree.Envelope.closure
            (admissibleKptSTree (hensonForbiddenFamily ell hell))
            (Run.I (cut+1)) X)
    (idx g : Nat) (hg : g < k)
    (hPos : 0 < hPosition k idx g)
    (hBelow : hPosition k idx g < top)
    (hCut : hPosition k idx g < N)
    (hNoActiveI1 : ∀ i : Fin params.card,
      presentAt (hPosition k idx g) i = true →
        LevelTree.lev (params.equivFin.symm i).val ≠ hPosition k idx g)
    (hNoActiveFork : ¬ ∃ i j : Fin params.card,
      presentAt (hPosition k idx g) i = true ∧
      presentAt (hPosition k idx g) j = true ∧
      hPosition k idx g < LevelTree.lev (params.equivFin.symm i).val ∧
      hPosition k idx g < LevelTree.lev (params.equivFin.symm j).val ∧
      kptFullOldAtCut (params.equivFin.symm i).val (hPosition k idx g) =
        kptFullOldAtCut (params.equivFin.symm j).val (hPosition k idx g) ∧
      kptFullUpperAtCut (params.equivFin.symm i).val (hPosition k idx g) ≠
        kptFullUpperAtCut (params.equivFin.symm j).val (hPosition k idx g))
    (hPhysicalCertificate :
      ∀ (hNoI2 : ¬ ∃ a : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        a ∈ SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily ell hell))
          (Run.I (hPosition k idx g+1)) X ∧
        ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
          b ∈ SMTree.Envelope.closure
            (admissibleKptSTree (hensonForbiddenFamily ell hell))
            (Run.I (hPosition k idx g+1)) X ∧
          SMTree.Envelope.SameComponent a b ∧
          LevelTree.lev (LevelTree.meet a b) = hPosition k idx g),
        let P := actualHensonRunCutOccurrence
          ell hell k hK E hLoops hSym hClique
          N U hAvoidA X top Run (hPosition k idx g) hCut hNoI2
        ∃ Marked : Fin P.M → Prop,
          (∀ v : Fin P.M, Marked v →
            closureSelectedOriginal (hensonForbiddenFamily ell hell)
              P.ambient P.hAvoid P.original P.Z (hPosition k idx g) v) ∧
          (∀ v : Fin P.M, P.Full v →
            ∀ j m : Nat, idx < j → g < m → m ≤ k →
              (P.original v).val = hPosition k j m →
              E idx j = true → Marked v) ∧
          (selectedStagePoolPrescribedData P.ambient (hPosition k idx g)
            P.original Marked).CorrectedB3
              (hensonForbiddenFamily ell hell)) :
    hPosition k idx g ∉ Run.I 0 := by
  classical
  obtain ⟨hNoI1,hNoI2⟩ :=
    finiteNumericH_run_no_I1_I2_of_complete_index_checks
      (hensonForbiddenFamily ell hell) (normalizedGraphModel E)
      k N hAvoidA (U : Set (Fin N)) X hX top Run
      params hParams presentAt hPresent (hPosition k idx g)
      hBelow hNoActiveI1 hNoActiveFork
  obtain ⟨Marked,hRepresented,hBaseCovered,hMarkedB3⟩ :=
    hPhysicalCertificate hNoI2
  exact henson_actualRun_lower_real_unselected_of_base_covered_marked_B3
    ell hell k hK E hLoops hSym hClique
    N U hAvoidA X hX top Run hTop idx g hg hPos hBelow hCut
    hNoI1 hNoI2 Marked hRepresented hBaseCovered hMarkedB3

#print axioms Kk.finiteNumericH_run_no_I1_I2_of_complete_index_checks
#print axioms Kk.henson_actualRun_lower_real_unselected_of_indexed_full_checks

end Kk
