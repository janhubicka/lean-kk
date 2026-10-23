import Kk.HensonAlgorithmTopI3
import SuccessorTree.V10.I3AlgorithmRunPool
import Mathlib.Tactic

/-!
# Top-generation I3 cannot be selected by the actual Henson AlgorithmRun

The pinned successor library has proved that the genuine
Algorithm 5.4 closure at EVERY intermediate cut is represented
by the SAME finite pool of numerical H originals:
  V = U union {i in R.I 0 : freeLevel(i) > 0}.
No independently assumed closure pool is needed.

The Henson-specific top-generation theorem checks the actual
parameter-closed I3 predicate using this represented closure.
Composing these results removes the pool-representation hypothesis
from the statement for the ACTUAL AlgorithmRun: a selected
top-generation level can only be interesting through (I1) or (I2),
never through (I3).

This is a genuine numerical-H theorem conditional only on the
initial seed lying in the H prefix pool, the selected run, and
the displayed absence of (I1)/(I2). It does not establish the
special resolved-copy diary comparison at lower generations.
-/

namespace Kk

open SuccessorTree.V10

/-- For the genuine Henson Algorithm 5.4 run on a finite numerical
H ambient structure, a positive top-generation cut with neither
an (I1) node nor an (I2) meet cannot belong to the run's
selected interesting level set R.I 0.

The finite original-name representation of the COMPLETE stage
closure follows from the checked generic run invariant; it is
a conclusion inside the proof rather than a new hypothesis. -/
theorem henson_algorithmRun_top_generation_no_I3
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
    (cut idx : Nat)
    (hBelowTop : cut < top)
    (hCut : cut < N) (hPos : 0 < cut)
    (hTopGen : cut = hPosition k idx k)
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
    cut ∉ R.I 0 := by
  intro hSelected
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
  have hNotInteresting :=
    henson_algorithm_top_generation_no_I3
      ell hell k hK E hLoops hSym hClique
      N cut V.card idx hCut hPos hTopGen hAvoidH
      original Z hPool hNoI1 hNoI2
  exact hNotInteresting hInteresting

end Kk
