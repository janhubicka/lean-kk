import Kk.HensonI3CliqueWitness
import Kk.HensonAlgorithmRunGenerationCutoff
import Mathlib.Tactic

/-!
# Positive-generation Algorithm 5.4 I3 events have genuine K_ell witnesses

The generic AlgorithmRun theorem identifies a positive nonstructural
I3-interesting level with failure of corrected B3 on the complete
parameter-closed closure, using ONE actual finite final-stage original
pool and the stage-dependent selected subset.

The normalized K_ell forbidden family includes extra loop and
asymmetry patterns, but the exact numerical H I3 rank argument
forces a forbidden pattern of size at least g+2 at generation g.
At positive generation g>0, only the symmetric K_ell pattern
has enough vertices.

This is an actual Algorithm 5.4 consequence, NOT an assertion
that the clique witness is supported entirely by the active
diary branches. Its upper continuation types may still name
auxiliary originals of higher generation.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Every genuine selected nonstructural positive-generation I3
event in a finite Henson numerical H AlgorithmRun has a finite
L-only corrected B3 witness violating the actual symmetric
K_ell clique pattern; neither loops nor asymmetric pairs can
be the responsible forbidden pattern.

The selected closure pool and failed B3 test are constructed
inside the proof from the run and no independent B3 witness is
supplied by the caller. -/
theorem henson_algorithmRun_positive_I3_has_clique_witness
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
    (cut idx g : Nat)
    (hBelowTop : cut < top)
    (hCut : cut < N) (hPos : 0 < cut)
    (hGenPos : 0 < g) (hGen : g < k)
    (hCutGen : cut = hPosition k idx g)
    (hSelected : cut ∈ R.I 0)
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      z ∈ SuccessorTree.SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily ell hell))
          (R.I (cut+1)) X ∧ LevelTree.lev z = cut)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      a ∈ SuccessorTree.SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily ell hell))
          (R.I (cut+1)) X ∧
      ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        b ∈ SuccessorTree.SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily ell hell))
          (R.I (cut+1)) X ∧
        SuccessorTree.SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :
    ∃ W : AgeTestModel 1 0 1,
      W.BoundedCarrier ∧
      SameInitialL W
        (finiteNumericHL (normalizedGraphModel E) k N) cut ∧
      (∀ bad, bad ∈ hensonForbiddenFamily ell hell →
        bad.Avoids (W.withoutVertex cut)) ∧
      ¬ (NormalizedForbidden.nontrivial ell
        (cliquePattern ell) (by omega)
        (cliquePattern_irreducible ell)).Avoids W := by
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
  let Z : Set (AdmissibleKptNode family) :=
    SuccessorTree.SMTree.Envelope.closure
      (admissibleKptSTree family) (R.I (cut+1)) X
  have hPool : ∀ z, z ∈ Z →
      ∃ v : Fin V.card, z ≤ A.kptOriginal family
        hAvoidH (original v) := by
    intro z hz
    obtain ⟨v,hv,hzv⟩ :=
      numericH_algorithmRun_closure_original_in_final_pool
        family K (by intro i; trivial) hAvoidK k N
        U X hX top cut hBelowTop R z hz
    obtain ⟨j,hj⟩ := hSurj v hv
    refine ⟨j,?_⟩
    simpa [A, ←hj] using hzv
  have hInteresting :
      SuccessorTree.SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family) Z cut := by
    have hFinal := R.finalLevel_interesting_of_run hTopSeed hSelected
    have hNext := R.I_succ_eq_higher_final_of_run cut hBelowTop
    simpa only [Z,hNext] using hFinal
  have hFailure :=
    algorithmI3_failsCorrectedB3
      family A hAvoidH original Z hPool cut hPos
      hNoI1 hNoI2 hInteresting
  obtain ⟨W,hFinite,hSocle,hDelete,_hUpper,hBad⟩ :=
    henson_positive_generation_B3_has_clique_witness
      ell hell k hK E hLoops hSym hClique
      N cut g idx V.card hGenPos hGen hCut hCutGen
      original
      (closureSelectedOriginal family A hAvoidH original Z cut)
      hFailure
  exact ⟨W,hFinite,hSocle,hDelete,hBad⟩

end Kk
