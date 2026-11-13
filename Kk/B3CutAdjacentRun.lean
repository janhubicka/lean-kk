import Kk.B3CutAdjacentI3
import Kk.NumericHFinalPoolCrossing
import Mathlib.Tactic

/-!
# Track B: actual finite numerical-H run has an omitted cut neighbour

English proof and hostile audit were committed FIRST:
  docs/track_b_cut_adjacent_i3_english_audit.md

The same final maintained original-name pool V from the actual
AlgorithmRun represents every pre-cut closure source. Consequently
a nonstructural I3 event invisible to a good marked corrected-B3
profile has an unmarked REAL original adjacent to the tested cut.

The full selected source is not all cut-eligible ambient originals.
We do NOT assert that the canonical macrodiary has this marked
source or that all such omitted cut neighbours can be eliminated.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- On a genuine finite numerical Henson AlgorithmRun, any positive
nonstructural I3 event with a B3-good nonempty represented marked
source must have an UNMARKED, free-cut-eligible, cut-ADJACENT
genuine original among the maintained final-stage names
V = hStageOriginals ... U (Run.I 0).

The closure source is exactly Run.I(cut+1); the common pool is
deduced from the verified actual stage invariant, not assumed. -/
theorem henson_numericH_algorithmRun_I3_requires_unmarked_cut_neighbour
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
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = top)
    (cut : Nat) (hPositive : 0 < cut)
    (hBelow : cut < top) (hCut : cut < N)
    (hSelected : cut ∈ Run.I 0)
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (cut+1)) X ∧ LevelTree.lev z = cut)
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
    ∀ (Marked : Fin V.card → Prop)
      (hMarkedNonempty : ∃ v : Fin V.card, Marked v)
      (hMarkedRepresented : ∀ v : Fin V.card, Marked v →
        closureSelectedOriginal
          (hensonForbiddenFamily ell hell)
          A hAvoid original Z cut v)
      (hMarkedB3 :
        (selectedStagePoolPrescribedData A cut original Marked).CorrectedB3
          (hensonForbiddenFamily ell hell)),
      ∃ v : Fin V.card,
        closureSelectedOriginal
          (hensonForbiddenFamily ell hell)
          A hAvoid original Z cut v ∧
        cut+1 ≤ A.freeLevel (original v).val ∧
        A.L.binary cut (original v).val (0 : Fin 1) = true ∧
        ¬ Marked v := by
  classical
  intro A V original Z Marked hMarkedNonempty hMarkedRepresented hMarkedB3
  let K : AgeTestModel 1 0 1 := normalizedGraphModel E
  have hCarrier : ∀ i : Nat, i ∈ K.carrier := by
    intro i
    trivial
  have hAvoidK : ∀ bad,
      bad ∈ hensonForbiddenFamily ell hell → bad.Avoids K :=
    (hensonForbiddenFamily_avoids_iff ell hell E).2
      ⟨hLoops,hSym,hClique⟩
  have hSurj : ∀ v : Fin N, v ∈ V →
      ∃ j : Fin V.card, original j = v := by
    intro v hv
    let j : Fin V.card := V.equivFin ⟨v,hv⟩
    refine ⟨j,?_⟩
    simp [original, hOriginalName, j] <;> rfl
  have hPool : ∀ z, z ∈ Z →
      ∃ j : Fin V.card,
        z ≤ A.kptOriginal
          (hensonForbiddenFamily ell hell) hAvoid (original j) := by
    intro z hz
    obtain ⟨v,hv,hzv⟩ :=
      numericH_algorithmRun_closure_original_in_final_pool
        (hensonForbiddenFamily ell hell)
        K hCarrier hAvoidK k N U X hX
        top cut hBelow Run z hz
    obtain ⟨j,hj⟩ := hSurj v hv
    refine ⟨j,?_⟩
    simpa only [A,K,hj] using hzv
  exact henson_algorithmRun_I3_requires_unmarked_cut_neighbour
    ell hell k hK E hLoops hSym hClique
    N cut V.card hCut hPositive original hAvoid
    X top Run hTopSeed hBelow hSelected hPool
    hNoI1 hNoI2 Marked
    hMarkedNonempty hMarkedRepresented hMarkedB3

#print axioms henson_numericH_algorithmRun_I3_requires_unmarked_cut_neighbour

end Kk
