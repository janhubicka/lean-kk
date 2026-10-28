import Kk.HensonAnyGenerationHigherSignature
import Kk.HensonAlgorithmRunCliqueCapacity
import Kk.HensonAlgorithmRunHigherCapacity
import SuccessorTree.V10.I3HigherSignatureCapacity
import Mathlib.Tactic

/-!
# Sharp clique-only I3 bound at all lower generations

Combines two distinct verified numerical-H refinements without
discarding either:
* at any generation every genuine Henson Algorithm 5.4 I3
  corrected-B3 witness is an actual K_ell forbidden clique;
* its upper names can all be drawn from a strictly
  higher-generation subpool of the SAME finite set of originals.

The new witness theorem constructs BOTH properties for ONE finite
L-only clique witness. Then the checked relabelling of selected
originals and the fixed-pattern signature-collision theorem yield
the sharp (H_g+1)^ell bound, rather than the larger (M+1)^ell or
the sum of all four forbidden-family signatures.

This is a quantitative bounded-envelope theorem. It does not show
the diary-to-envelope labelled factorisation or the lower bound.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- At any numerical-H generation g, the true nonstructural
Algorithm 5.4 I3 levels of one Henson finite envelope use at most
(H_g+1)^ell clique signatures, where H_g is EXACTLY the number
of names in the maintained final-stage pool whose generation
is strictly higher than g.

All complete parameter-closed source and B3 hypotheses are
derived from the genuine AlgorithmRun and one fixed pool. -/
theorem henson_algorithmRun_all_I3_levels_card_le_higher_clique_capacity
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
    (g : Nat) (hg : g < k)
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
    let original : Fin V.card → Fin N :=
      fun j => (V.equivFin.symm j).1
    let higher := higherGenerationStageNames original k g
    levels.card ≤ (higher.card+1)^ell := by
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
  let higherNames : Finset (Fin V.card) :=
    higherGenerationStageNames original k g
  let isHigher : Fin V.card → Prop :=
    fun v => ∃ idx m : Nat, g < m ∧ m ≤ k ∧
      (original v).val = hPosition k idx m
  let higher : Fin higherNames.card → Fin V.card :=
    fun j => (higherNames.equivFin.symm j).1
  have hCover : ∀ v : Fin V.card, isHigher v →
      ∃ j : Fin higherNames.card, higher j = v := by
    intro v hv
    have hMember : v ∈ higherNames := by
      simpa only [higherNames, higherGenerationStageNames,
        Finset.mem_filter, Finset.mem_univ, true_and] using hv
    refine ⟨higherNames.equivFin ⟨v,hMember⟩,?_⟩
    simp [higher]
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
        (finiteNumericHL K k N)
        (fun v : Fin higherNames.card => (original (higher v)).val) cut,
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
    obtain ⟨w,hWUpper⟩ :=
      henson_any_generation_B3_has_clique_higher_signature
        ell hell k hK E hLoops hSym hClique
        N cut g idx V.card hg hCut hCutGen
        original
        (closureSelectedOriginal family A hAvoidH original (Z cut) cut)
        hFailure
    have hWUpper' : ∀ a : Fin ell, cut < w.e a →
        ∃ v : Fin V.card, isHigher v ∧
          RelationalPrefixType.ofAgeModel w.W (cut+1) (w.e a) =
            RelationalPrefixType.ofAgeModel (finiteNumericHL K k N)
              (cut+1) (original v).val := hWUpper
    let w' :=
      w.relabelHigherOriginals isHigher higher hCover hWUpper'
    exact ⟨w', Subsingleton.elim _ _⟩
  exact i3Levels_card_le_fixedPattern_capacity
    (fun _ : Fin 1 => ell) (fun _ : Fin 1 => cliquePattern ell)
    (finiteNumericHL K k N)
    (fun v : Fin higherNames.card => (original (higher v)).val)
    (0 : Fin 1) levels hInitial hWitness

end Kk
