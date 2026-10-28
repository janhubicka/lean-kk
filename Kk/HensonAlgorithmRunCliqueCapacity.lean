import Kk.HensonAlgorithmRunCliqueWitness
import Kk.I3FixedPatternCapacity
import Kk.HensonAlgorithmRunHigherCapacity
import Mathlib.Tactic

/-!
# Positive-generation actual AlgorithmRun I3 levels: clique-only capacity

The full normalized Henson signature contains four forbidden
patterns. The earlier AlgorithmRun bound counts signatures from
all four, whereas the checked numerical-H rank equation forces
every positive-generation I3 witness to use the clique pattern.

This theorem assembles original-labelled witnesses of that fixed
clique pattern from the actual full parameter-closed AlgorithmRun
and invokes the separately verified fixed-pattern collision count.
The source pool is the SAME finite final-stage set at all cuts;
no stage-dependent arbitrary choice of original-name universe is
allowed.

It proves a clique-only capacity with the size of the entire
finite final-stage original pool. A further refinement to use
only strictly higher-generation originals requires transporting
the chosen clique witness's upper names to that smaller pool.
The diary-to-envelope factorization also remains unverified.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- For a positive generation g<k, actual nonstructural I3
levels of a finite Henson Algorithm 5.4 run are bounded by the
one forbidden-clique signature component, (M+1)^ell, where M
is the exact number of originals in the checked final-stage
representing pool. No extra E test or conditional injection is
introduced. -/
theorem henson_algorithmRun_positive_I3_levels_card_le_clique_capacity
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N : Nat)
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (hAvoidH :
      ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
        bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (hX : X ⊆ ambientPrefixPool (hensonForbiddenFamily ell hell)
       (finiteNumericH (normalizedGraphModel E) k N)
       hAvoidH (U : Set (Fin N)))
    (top : Nat)
    (R : SuccessorTree.SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell)) X top)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = top)
    (g : Nat) (hgPos : 0 < g) (hg : g < k)
    (levels : Finset Nat)
    (hLevels : ∀ cut, cut ∈ levels →
      0 < cut ∧ cut < top ∧ cut < N ∧ cut ∈ R.I 0 ∧
      ∃ idx : Nat, cut = hPosition k idx g)
    (hNoI1 : ∀ cut, cut ∈ levels →
      ¬ ∃ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        z ∈ SuccessorTree.SMTree.Envelope.closure
            (admissibleKptSTree (hensonForbiddenFamily ell hell))
            (R.I (cut+1)) X ∧ LevelTree.lev z = cut)
    (hNoI2 : ∀ cut, cut ∈ levels →
      ¬ ∃ a : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        a ∈ SuccessorTree.SMTree.Envelope.closure
            (admissibleKptSTree (hensonForbiddenFamily ell hell))
            (R.I (cut+1)) X ∧
        ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
          b ∈ SuccessorTree.SMTree.Envelope.closure
              (admissibleKptSTree (hensonForbiddenFamily ell hell))
              (R.I (cut+1)) X ∧
          SuccessorTree.SMTree.Envelope.SameComponent a b ∧
          LevelTree.lev (LevelTree.meet a b) = cut) :
    let V := hStageOriginals (normalizedGraphModel E) k N U (R.I 0)
    levels.card ≤ (V.card+1)^ell := by
  classical
  let family : List (NormalizedForbidden 1 0 1) :=
    hensonForbiddenFamily ell hell
  let K : AgeTestModel 1 0 1 := normalizedGraphModel E
  let A : EnumeratedPartialStructure 1 0 1 := finiteNumericH K k N
  have hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K :=
    (hensonForbiddenFamily_avoids_iff ell hell E).2
      ⟨hLoops,hSym,hClique⟩
  let V : Finset (Fin N) := hStageOriginals K k N U (R.I 0)
  let original : Fin V.card → Fin N :=
    fun j => (V.equivFin.symm j).1
  have hSurj : ∀ v : Fin N, v ∈ V →
      ∃ j : Fin V.card, original j = v := by
    intro v hv
    refine ⟨V.equivFin ⟨v,hv⟩,?_⟩
    simp [original]
  let Z : Nat → Set (AdmissibleKptNode family) :=
    fun cut => SuccessorTree.SMTree.Envelope.closure
      (admissibleKptSTree family) (R.I (cut+1)) X
  have hInitial : ∀ cut, cut ∈ levels →
      ∀ x, x ≤ cut → x ∈ (finiteNumericHL K k N).carrier := by
    intro cut hc x hx
    have hCut : cut < N := (hLevels cut hc).2.2.1
    change x < N
    omega
  have hWitness : ∀ cut, cut ∈ levels →
      ∃ w : I3OriginalSignatureWitness
        (fun _ : Fin 1 => ell)
        (fun _ : Fin 1 => cliquePattern ell)
        (finiteNumericHL K k N) (fun v : Fin V.card => (original v).val) cut,
        w.familyIndex = (0 : Fin 1) := by
    intro cut hc
    obtain ⟨hPos,hBelow,hCut,hSelected,idx,hCutGen⟩ :=
      hLevels cut hc
    have hPool : ∀ z, z ∈ Z cut →
        ∃ v : Fin V.card, z ≤ A.kptOriginal family
          hAvoidH (original v) := by
      intro z hz
      obtain ⟨v,hv,hzv⟩ :=
        numericH_algorithmRun_closure_original_in_final_pool
          family K (by intro i; trivial) hAvoidK k N
          U X hX top cut hBelow R z hz
      obtain ⟨j,hj⟩ := hSurj v hv
      refine ⟨j,?_⟩
      simpa [A, ←hj] using hzv
    have hInteresting :
        SuccessorTree.SMTree.Envelope.IsInterestingAt
          (normalizedKptSMTree family) (Z cut) cut := by
      have hFinal := R.finalLevel_interesting_of_run hTopSeed hSelected
      have hNext := R.I_succ_eq_higher_final_of_run cut hBelow
      simpa only [Z,hNext] using hFinal
    have hFailure :
        ¬ (selectedStagePoolPrescribedData
          A cut original
          (closureSelectedOriginal family A hAvoidH original (Z cut) cut)
        ).CorrectedB3 family :=
      algorithmI3_failsCorrectedB3
        family A hAvoidH original (Z cut) hPool cut hPos
        (hNoI1 cut hc) (hNoI2 cut hc) hInteresting
    have hCliq :
        Nonempty (I3OriginalSignatureWitness
          (fun _ : Fin 1 => ell)
          (fun _ : Fin 1 => cliquePattern ell)
          (finiteNumericHL K k N)
          (fun v : Fin V.card => (original v).val) cut) :=
      henson_positive_generation_B3_has_clique_signature
        ell hell k hK E hLoops hSym hClique
        N cut g idx V.card hgPos hg hCut hCutGen
        original
        (closureSelectedOriginal family A hAvoidH original (Z cut) cut)
        hFailure
    exact ⟨Classical.choice hCliq, Subsingleton.elim _ _⟩
  exact i3Levels_card_le_fixedPattern_capacity
    (fun _ : Fin 1 => ell) (fun _ : Fin 1 => cliquePattern ell)
    (finiteNumericHL K k N)
    (fun v : Fin V.card => (original v).val)
    (0 : Fin 1) levels hInitial hWitness

end Kk
