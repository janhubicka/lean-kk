import Kk.B3ClosureFibreCoherence
import Kk.NumericHFinalPoolCrossing
import Mathlib.Tactic

/-!
# Track B: exact full corrected-B3 compression to the cut star

English proof and twenty hostile checks were committed BEFORE Lean:
  docs/track_b_cut_star_compression_english_audit.md

For a nonempty TRUE closure-selected original pool at one tested
finite Henson cut with no competing (I2) meet, corrected B3 is
EQUIVALENT to its test restricted to:
  * every genuinely selected original adjacent to that cut in L;
  * one genuinely closure-selected original anchor.

The anchor carries the common old L socle and avoids vacuity.
The omission of all other original names is sound for corrected B3
only, not for I1/I2, E records, labelled source orbits or the
unconditional big Ramsey degree theorem.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Exact corrected-B3 equivalence for a TRUE represented closure
source and its ANCHORED CUT-STAR selection in a finite numerical
Henson model, assuming no (I2) competing meet at the tested cut.

Unlike equality of complete upper type spectra, this is only
equality of the corrected-B3 tests, whose finite forbidden-clique
witnesses all meet the tested coordinate. Both directions use
Track D's verified no-I2 cut-visible transfer theorem, with
full and marked profiles exchanged. -/
theorem henson_closureB3_iff_cutStarB3
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N cut M : Nat) (hCut : cut < N)
    (original : Fin M → Fin N)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (Z : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      a ∈ Z ∧ ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        b ∈ Z ∧ SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut)
    (anchor : Fin M)
    (hAnchor : closureSelectedOriginal (hensonForbiddenFamily ell hell)
      (finiteNumericH (normalizedGraphModel E) k N)
      hAvoid original Z cut anchor) :
    let A : EnumeratedPartialStructure 1 0 1 :=
      finiteNumericH (normalizedGraphModel E) k N
    let Full : Fin M → Prop :=
      closureSelectedOriginal (hensonForbiddenFamily ell hell)
        A hAvoid original Z cut
    let Star : Fin M → Prop :=
      fun v => Full v ∧
        (A.L.binary cut (original v).val (0 : Fin 1) = true ∨
          v = anchor)
    (selectedStagePoolPrescribedData A cut original Full).CorrectedB3
      (hensonForbiddenFamily ell hell) ↔
    (selectedStagePoolPrescribedData A cut original Star).CorrectedB3
      (hensonForbiddenFamily ell hell) := by
  classical
  intro A Full Star
  have hFullNonempty : ∃ v : Fin M, Full v :=
    ⟨anchor,hAnchor⟩
  have hStarNonempty : ∃ v : Fin M, Star v :=
    ⟨anchor,⟨hAnchor,Or.inr rfl⟩⟩
  have hFullRep : ∀ v : Fin M, Full v →
      closureSelectedOriginal (hensonForbiddenFamily ell hell)
        A hAvoid original Z cut v := by
    intro v hv
    exact hv
  have hStarRep : ∀ v : Fin M, Star v →
      closureSelectedOriginal (hensonForbiddenFamily ell hell)
        A hAvoid original Z cut v := by
    intro v hv
    exact hv.1
  constructor
  · intro hFullB3
    exact henson_fullB3_of_no_i2_marked_closure_cut_neighbours
      ell hell k hK E hLoops hSym hClique
      N cut M hCut original hAvoid Z
      Star Full hFullNonempty hFullRep hNoI2
      (by
        intro v hv _hEligible _hEdge
        exact hv.1)
      hFullB3
  · intro hStarB3
    exact henson_fullB3_of_no_i2_marked_closure_cut_neighbours
      ell hell k hK E hLoops hSym hClique
      N cut M hCut original hAvoid Z
      Full Star hStarNonempty hStarRep hNoI2
      (by
        intro v hv _hEligible hEdge
        exact ⟨hv,Or.inl hEdge⟩)
      hStarB3

/-- The same exact cut-star reduction on the pre-cut closure of
ONE genuine AlgorithmRun. No selected-level or no-(I1) hypothesis
is needed, because this is a corrected-B3 test equivalence,
not an assertion that the level can be skipped. -/
theorem henson_algorithmRun_B3_iff_cutStarB3
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N cut M : Nat) (hCut : cut < N)
    (original : Fin M → Fin N)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (X : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell)) X top)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      a ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (cut+1)) X ∧
      ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        b ∈ SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily ell hell))
          (Run.I (cut+1)) X ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut)
    (anchor : Fin M)
    (hAnchor : closureSelectedOriginal (hensonForbiddenFamily ell hell)
      (finiteNumericH (normalizedGraphModel E) k N)
      hAvoid original
      (SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (cut+1)) X) cut anchor) :
    let Z : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)) :=
      SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (cut+1)) X
    let A : EnumeratedPartialStructure 1 0 1 :=
      finiteNumericH (normalizedGraphModel E) k N
    let Full : Fin M → Prop :=
      closureSelectedOriginal (hensonForbiddenFamily ell hell)
        A hAvoid original Z cut
    let Star : Fin M → Prop :=
      fun v => Full v ∧
        (A.L.binary cut (original v).val (0 : Fin 1) = true ∨
          v = anchor)
    (selectedStagePoolPrescribedData A cut original Full).CorrectedB3
      (hensonForbiddenFamily ell hell) ↔
    (selectedStagePoolPrescribedData A cut original Star).CorrectedB3
      (hensonForbiddenFamily ell hell) := by
  intro Z A Full Star
  exact henson_closureB3_iff_cutStarB3
    ell hell k hK E hLoops hSym hClique
    N cut M hCut original hAvoid Z hNoI2 anchor hAnchor

/-- In a REAL finite numerical-H AlgorithmRun, the chosen
full crossing on the final maintained finite original-name pool
has both real two-way crossing/source correctness, AND the entire
corrected B3 test agrees with its anchored cut-star restriction.

Unlike the abstract ambient-pool equality, this uses the actual
run invariant to represent the COMPLETE pre-cut source, not
just a prescribed subset of ambient original names. -/
theorem henson_numericH_run_finalPool_cutStar_B3_equivalence
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N : Nat)
    (U : Finset (Fin N))
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (X : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (hX : X ⊆ ambientPrefixPool (hensonForbiddenFamily ell hell)
      (finiteNumericH (normalizedGraphModel E) k N) hAvoid
      (U : Set (Fin N)))
    (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell)) X top)
    (cut : Nat) (hBelow : cut < top) (hCut : cut < N)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      a ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (cut+1)) X ∧
      ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        b ∈ SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily ell hell))
          (Run.I (cut+1)) X ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :
    let A : EnumeratedPartialStructure 1 0 1 :=
      finiteNumericH (normalizedGraphModel E) k N
    let V : Finset (Fin N) :=
      hStageOriginals (normalizedGraphModel E) k N U (Run.I 0)
    let original : Fin V.card → Fin A.size := hOriginalName V
    let Z : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)) :=
      SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (cut+1)) X
    let F : PrescribedBoringData cut 1 0 1 :=
      closureSelectedBoringData (hensonForbiddenFamily ell hell)
        A hAvoid original Z cut
    let Full : Fin V.card → Prop :=
      closureSelectedOriginal (hensonForbiddenFamily ell hell)
        A hAvoid original Z cut
    ∀ (anchor : Fin V.card) (hAnchor : Full anchor),
      CoversClosureCrossing (hensonForbiddenFamily ell hell) Z cut F ∧
      IsCrossingGraphOf (hensonForbiddenFamily ell hell) Z cut F ∧
      (F.CorrectedB3 (hensonForbiddenFamily ell hell) ↔
        (selectedStagePoolPrescribedData A cut original
          (fun v => Full v ∧
            (A.L.binary cut (original v).val (0 : Fin 1) = true ∨
              v = anchor))).CorrectedB3
                (hensonForbiddenFamily ell hell)) := by
  classical
  intro A V original Z F Full anchor hAnchor
  let K : AgeTestModel 1 0 1 := normalizedGraphModel E
  have hCarrier : ∀ i : Nat, i ∈ K.carrier := by
    intro i
    trivial
  have hAvoidK : ∀ bad,
      bad ∈ hensonForbiddenFamily ell hell → bad.Avoids K :=
    (hensonForbiddenFamily_avoids_iff ell hell E).2
      ⟨hLoops,hSym,hClique⟩
  obtain ⟨hCover,hGraph,_hRealSources⟩ :=
    finiteNumericH_run_final_pool_crossing_and_upper_types
      (hensonForbiddenFamily ell hell)
      K hCarrier hAvoidK k N U X hX
      top cut hBelow Run hNoI2
  have hB3 :
      F.CorrectedB3 (hensonForbiddenFamily ell hell) ↔
        (selectedStagePoolPrescribedData A cut original
          (fun v => Full v ∧
            (A.L.binary cut (original v).val (0 : Fin 1) = true ∨
              v = anchor))).CorrectedB3
                (hensonForbiddenFamily ell hell) := by
    exact henson_closureB3_iff_cutStarB3
      ell hell k hK E hLoops hSym hClique
      N cut V.card hCut original hAvoid Z hNoI2
      anchor hAnchor
  exact ⟨hCover,hGraph,hB3⟩

#print axioms henson_closureB3_iff_cutStarB3
#print axioms henson_algorithmRun_B3_iff_cutStarB3
#print axioms henson_numericH_run_finalPool_cutStar_B3_equivalence

end Kk
