import Kk.HensonAlgorithmRunTop
import SuccessorTree.V10.I3ChosenOriginalGeneration
import Mathlib.Tactic

/-!
# Lower-generation I3 events in the actual Henson Algorithm 5.4 run

A failed corrected B3 test in a genuine selected numerical H
original pool has a chosen upper original of strictly HIGHER
generation. This module first specializes that theorem for
arbitrary k with ell <= k+1 and for a tested generation g<k.
It then proves the conclusion for the actual intermediate
parameter-closed AlgorithmRun closure, using the established
single finite final-stage original pool.

No hand-supplied representation of the entire closure or
extra B3 failure hypothesis remains in the AlgorithmRun theorem.
The selected original may still be an auxiliary gadget original
rather than a selected diary branch. Establishing that the
macro-diary remembers the resulting B3 events is the separate
K_k-specific construction task.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Corrected B3 failure in the actual Henson selected pool, at
generation g<k, requires a CHOSEN selected original of generation
m>g; the pattern-size bound is ell<=k+1. -/
theorem henson_failedSelectedB3_higher_original_anyK
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N cut g idx M : Nat)
    (hGen : g < k)
    (hCut : cut < N)
    (hGeneration : cut = hPosition k idx g)
    (original : Fin M → Fin N)
    (Selected : Fin M → Prop)
    (hFailure :
      ¬ (selectedStagePoolPrescribedData
        (finiteNumericH (normalizedGraphModel E) k N)
        cut original Selected).CorrectedB3
          (hensonForbiddenFamily ell hell)) :
    ∃ v : Fin M, Selected v ∧
      ∃ j m : Nat, g < m ∧ m ≤ k ∧
        (original v).val = hPosition k j m := by
  have hAvoid :
      ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
        bad.Avoids (normalizedGraphModel E) :=
    (hensonForbiddenFamily_avoids_iff ell hell E).2
      ⟨hLoops,hSym,hClique⟩
  have hPatternBound : ∀ bad,
      bad ∈ hensonForbiddenFamily ell hell →
      bad.patternCard ≤ k+1 := by
    intro bad hb
    exact (hensonForbiddenFamily_patternCard_le ell hell bad hb).trans hK
  obtain ⟨W,hFinite,hSocle,hDelete,t,P,e,r,hr,hrt,
      hIrred,hCopy,hLow,hHigh,i,hGenLast,hUpper⟩ :=
    finiteNumericH_failedSelectedStageB3_originals_higher
      (hensonForbiddenFamily ell hell)
      (normalizedGraphModel E)
      (by intro n; trivial)
      hAvoid k N cut hCut original Selected
      hPatternBound hFailure
  let b : Fin t := ⟨r, hrt⟩
  obtain ⟨v,j,m,hSelected,hFree,hOriginal,hHigher,hm,hType⟩ :=
    hUpper b (by simp [b])
  have hRBound : r-1 ≤ k := by omega
  obtain ⟨_hIndex,hGenEq⟩ :=
    hPosition_injective_bounded k idx g i (r-1)
      (Nat.le_of_lt hGen) hRBound
      (hGeneration.symm.trans hGenLast)
  refine ⟨v,hSelected,j,m,?_,hm,hOriginal⟩
  omega

/-- A genuine positive I3-interesting level in a finite Henson
AlgorithmRun (neither I1 nor I2 at the full intermediate
parameter-closed stage) must have a selected ORIGINAL in the
actual fixed final-stage pool at strictly HIGHER generation.

Unlike the premise needed by generic Observation 6.52, a
finite representing pool and selected-stage crossing are
constructed here from the actual run itself. -/
theorem henson_algorithmRun_lower_I3_requires_higher_selected_original
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
    let V := hStageOriginals (normalizedGraphModel E) k N U (R.I 0)
    let original : Fin V.card → Fin N :=
      fun j => (V.equivFin.symm j).1
    let Z : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)) :=
      SuccessorTree.SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (R.I (cut+1)) X
    ∃ v : Fin V.card,
      closureSelectedOriginal (hensonForbiddenFamily ell hell)
        (finiteNumericH (normalizedGraphModel E) k N)
        hAvoidH original Z cut v ∧
      ∃ j m : Nat, g < m ∧ m ≤ k ∧
        (original v).val = hPosition k j m := by
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
  exact henson_failedSelectedB3_higher_original_anyK
    ell hell k hK E hLoops hSym hClique
    N cut g idx V.card hGen hCut hCutGen original
    (closureSelectedOriginal family A hAvoidH original Z cut) hFailure

end Kk
