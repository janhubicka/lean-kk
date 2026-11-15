import Kk.ActualRunOddStructural
import Kk.NumericHStructuralCutClassifier
import Kk.NumericHExhaustiveRunIndex
import Mathlib.Tactic

/-!
# Track D: true selected odd cuts have genuine FINITE active Kpt I1/I2 records

English proof and 16 hostile source checks committed before Lean:
docs/audits/2026-11-15-track-d-odd-finite-index-english.md

STACKED on the actual-run structural odd-cut PR #239. Do not treat
the stacked theorem as verified before predecessor + new exact-head CI.

One finite index of ACTUAL Kpt nodes enumerates the entire FINAL
closure, while its live mask at cut c identifies the distinct TRUE
PRE-CUT closure at Run.I(c+1). A selected physically ODD cut has
either a live node at that cut, or two live strictly crossing
nodes with equal COMPLETE old dependent L+ records and distinct
COMPLETE next dependent L+ records.

No selected graph-age or macrodiary source substitution occurs.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Finite-index certificate of an I1 endpoint or a truly
two-crossing I2 fork, using complete old and upper L+ Kpt records.

This is exactly the right side of
finiteNumericH_run_structural_I1I2_iff_active_node_or_fork;
the I1 alternative is essential to handle trivial self-meets.
-/
def KptFiniteStructuralCutCertificate
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (params : Finset (AdmissibleKptNode family))
    (presentAt : Nat → Fin params.card → Bool)
    (cut : Nat) : Prop :=
  (∃ i : Fin params.card,
      presentAt cut i = true ∧
      LevelTree.lev (params.equivFin.symm i).val = cut) ∨
    (∃ i j : Fin params.card,
      presentAt cut i = true ∧
      presentAt cut j = true ∧
      cut < LevelTree.lev (params.equivFin.symm i).val ∧
      cut < LevelTree.lev (params.equivFin.symm j).val ∧
      kptFullOldAtCut (params.equivFin.symm i).val cut =
        kptFullOldAtCut (params.equivFin.symm j).val cut ∧
      kptFullUpperAtCut (params.equivFin.symm i).val cut ≠
        kptFullUpperAtCut (params.equivFin.symm j).val cut)

/-- For ANY exact finite index of the real full Kpt closure and
literal live mask of pre-cut closure membership, every selected
physical odd cut has an indexed complete-L+ I1/I2 certificate.

The actual original pool U and Kpt seed set X are genuinely
represented; no source is inferred from the selected graph age.
-/
theorem henson_actualRun_odd_selected_has_indexed_I1_or_I2
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
    (hX : X ⊆ ambientPrefixPool
      (hensonForbiddenFamily ell hell)
      (finiteNumericH (normalizedGraphModel E) k N)
      hAvoid (U : Set (Fin N)))
    (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell)) X top)
    (hTop : ∃ x ∈ X, LevelTree.lev x = top)
    (params : Finset (AdmissibleKptNode
      (hensonForbiddenFamily ell hell)))
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
    (a : Nat) (hBelow : 2*a+1 < top) (hCut : 2*a+1 < N)
    (hSelected : 2*a+1 ∈ Run.I 0) :
    KptFiniteStructuralCutCertificate
      (hensonForbiddenFamily ell hell) params presentAt (2*a+1) := by
  classical
  let family := hensonForbiddenFamily ell hell
  let K : AgeTestModel 1 0 1 := normalizedGraphModel E
  let cut : Nat := 2*a+1
  let Z : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure
      (admissibleKptSTree family) (Run.I (cut+1)) X
  have hStructural :
      KptI1AtCut family Z cut ∨
        KptI2MeetAtCut family Z cut :=
    henson_numericH_odd_selected_requires_structural_I1_or_I2
      ell hell k hK E hLoops hSym hClique
      N U hAvoid X hX top Run hTop
      a hBelow hCut hSelected
  have hExact :
      (KptI1AtCut family Z cut ∨
        KptI2MeetAtCut family Z cut) ↔
        KptFiniteStructuralCutCertificate
          family params presentAt cut := by
    exact finiteNumericH_run_structural_I1I2_iff_active_node_or_fork
      family K k N hAvoid (U : Set (Fin N)) X hX top Run
      params hParams presentAt hPresent cut hBelow
  exact hExact.mp hStructural

/-- There EXISTS one actually constructed finite source index and
complete live-mask family witnessing every selected physically odd
cut as one active level endpoint or two genuinely crossing nodes
with identical complete old and different complete upper L+ types.

The index is the TRUE final complete Kpt node set and may contain
generated auxiliary E parameters and meets.
-/
theorem henson_actualRun_odd_selected_has_constructed_indexed_I1_or_I2
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
    (hX : X ⊆ ambientPrefixPool
      (hensonForbiddenFamily ell hell)
      (finiteNumericH (normalizedGraphModel E) k N)
      hAvoid (U : Set (Fin N)))
    (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell)) X top)
    (hTop : ∃ x ∈ X, LevelTree.lev x = top)
    (a : Nat) (hBelow : 2*a+1 < top) (hCut : 2*a+1 < N)
    (hSelected : 2*a+1 ∈ Run.I 0) :
    ∃ (params : Finset (AdmissibleKptNode
        (hensonForbiddenFamily ell hell)))
      (presentAt : Nat → Fin params.card → Bool),
      (∀ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        z ∈ params ↔
          z ∈ SMTree.Envelope.closure
            (admissibleKptSTree (hensonForbiddenFamily ell hell))
            (Run.I 0) X) ∧
      (∀ cut : Nat, ∀ i : Fin params.card,
        presentAt cut i = true ↔
          (params.equivFin.symm i).val ∈
            SMTree.Envelope.closure
              (admissibleKptSTree (hensonForbiddenFamily ell hell))
              (Run.I (cut+1)) X) ∧
      KptFiniteStructuralCutCertificate
        (hensonForbiddenFamily ell hell) params presentAt (2*a+1) := by
  classical
  let family := hensonForbiddenFamily ell hell
  let K : AgeTestModel 1 0 1 := normalizedGraphModel E
  obtain ⟨params,presentAt,hParams,_hInjective,hPresent,_hExhaustive⟩ :=
    finiteNumericH_actualRun_uniform_exhaustive_source_index
      family K k N hAvoid (U : Set (Fin N)) X hX top Run
  refine ⟨params,presentAt,hParams,hPresent,?_⟩
  exact henson_actualRun_odd_selected_has_indexed_I1_or_I2
    ell hell k hK E hLoops hSym hClique
    N U hAvoid X hX top Run hTop
    params hParams presentAt hPresent
    a hBelow hCut hSelected

#print axioms KptFiniteStructuralCutCertificate
#print axioms henson_actualRun_odd_selected_has_indexed_I1_or_I2
#print axioms henson_actualRun_odd_selected_has_constructed_indexed_I1_or_I2

end Kk
