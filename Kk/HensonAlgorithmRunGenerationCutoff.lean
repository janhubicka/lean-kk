import Kk.HensonI3PatternSize
import Kk.HensonAlgorithmRunLowerI3

/-!
# Actual numerical-H AlgorithmRun I3 events lie below clique-size margin

A failed selected-original corrected B3 test in the normalized Henson
signature can have lower generation only g<=ell-2, since its actual
forbidden pattern has at most ell vertices and a nonempty upper part.

The already checked Algorithm 5.4 run-to-selected-B3 bridge builds
the full closure and finite original-name pool. This theorem combines
it with the forbidden-pattern-size argument to obtain a bound on
the ACTUAL selected nonstructural I3 levels, rather than just an
abstract selected-original B3 prescription.

It does not identify all lower-generation I3 events with the
published macro-diary covers; that remains the full auxiliary
witness projection problem.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- An actual positive nonstructural I3 level at numerical-H generation
g<k requires g+2 <= ell, for any k with ell<=k+1.
In particular, when the manuscript takes k=ell, no I3 level can
occur at generations ell-1 or ell (assuming no I1/I2). -/
theorem henson_algorithmRun_lower_I3_generation_below_clique_margin
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
    (hGen : g < k)
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
    g+2 ≤ ell := by
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
  exact henson_failedSelectedB3_generation_below_clique_margin
    ell hell k hK E hLoops hSym hClique
    N cut g idx V.card hGen hCut hCutGen original
    (closureSelectedOriginal family A hAvoidH original Z cut) hFailure

end Kk
