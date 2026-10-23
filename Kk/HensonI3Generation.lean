import Kk.HensonEncoding
import SuccessorTree.V10.I3ActualStageGeneration
import Mathlib.Tactic

/-!
# Generation of a corrected B3 failure for an actual Henson original pool

The numerical successor library proves Lemma 6.53 for every normalized
irreducible forbidden family. This module specializes the proof to the
ACTUAL four-pattern normalized K_ell-free graph language, with the
generation k = ell - 1 from the original numerical H construction.

A failed corrected B3 age test of a genuine numerical H original pool
then occurs only at a generation g STRICTLY BELOW k. In particular
the top generation k never witnesses such a failure, provided the
prescribed original pool has the requisite real E-free cuts.

The theorem retains the ambient-pool assumption and its free-cut
hypotheses. It is NOT a claim that every parameter-closed B3 witness
of the resolved diary has already been shown to lie in that pool:
the actual selected-stage-to-original representation is the remaining
application bridge.
-/

namespace Kk

open SuccessorTree.V10

/-- Every normalized forbidden graph pattern has cardinality at most
ell; the three extra symmetry/loop patterns have sizes 1,2,2. -/
theorem hensonForbiddenFamily_patternCard_le
    (ell : Nat) (hell : 2 ≤ ell) :
    ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.patternCard ≤ ell := by
  intro bad hMem
  simp [hensonForbiddenFamily] at hMem
  rcases hMem with rfl | rfl | rfl | rfl
  all_goals simp [NormalizedForbidden.patternCard] <;> omega

/-- Any actual corrected B3 failure from an ambient pool of genuine
numerical H originals in a K_ell-free graph has generation g<ell-1.

Unlike an arbitrary age-shadow argument, this invokes the complete
finite L-only forbidden-copy witness and the verified exact
original-generation relocation theorem of lean-successors. -/
theorem henson_failedAmbientB3_lower_generation
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N cut M : Nat)
    (hCut : cut < N)
    (original : Fin M → Nat)
    (hFree : ∀ v : Fin M,
      cut+1 ≤ (finiteNumericH (normalizedGraphModel E)
        (ell-1) N).freeLevel (original v))
    (hFailure :
      ¬ (ambientPoolPrescribedData
        (finiteNumericH (normalizedGraphModel E) (ell-1) N)
        cut original).CorrectedB3
          (hensonForbiddenFamily ell hell)) :
    ∃ (i g : Nat), g < ell-1 ∧
      cut = hPosition (ell-1) i g := by
  have hAvoid :
      ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
        bad.Avoids (normalizedGraphModel E) :=
    (hensonForbiddenFamily_avoids_iff ell hell E).2
      ⟨hLoops,hSym,hClique⟩
  have hPatternBound : ∀ bad,
      bad ∈ hensonForbiddenFamily ell hell →
      bad.patternCard ≤ (ell-1)+1 := by
    intro bad hb
    have h := hensonForbiddenFamily_patternCard_le ell hell bad hb
    omega
  obtain ⟨W, hBounded, hSocle, hDelete, t, P, e, r, hr,
      hrt, hIrred, hCopy, hLower, hUpper,
      i, hGeneration, hUpperGen⟩ :=
    finiteNumericH_failedPoolB3_generation
      (hensonForbiddenFamily ell hell)
      (normalizedGraphModel E)
      (by intro i; trivial)
      hAvoid (ell-1) N cut hCut original hFree
      hPatternBound hFailure
  let b : Fin t := ⟨r, hrt⟩
  obtain ⟨j, m, hHigher, hM, hLater, hType⟩ :=
    hUpperGen b (by simp [b])
  exact ⟨i, r-1, by omega, hGeneration⟩

/-- A top-generation cut is never a failed corrected B3 stage for
a genuine numerical H ambient-original pool, under the same
explicit full-graph and original-free-cut hypotheses. -/
theorem henson_top_generation_ambientB3
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N cut M i : Nat)
    (hCut : cut < N)
    (hTop : cut = hPosition (ell-1) i (ell-1))
    (original : Fin M → Nat)
    (hFree : ∀ v : Fin M,
      cut+1 ≤ (finiteNumericH (normalizedGraphModel E)
        (ell-1) N).freeLevel (original v)) :
    (ambientPoolPrescribedData
      (finiteNumericH (normalizedGraphModel E) (ell-1) N)
      cut original).CorrectedB3
        (hensonForbiddenFamily ell hell) := by
  by_contra hFailure
  obtain ⟨j,g,hg,hGen⟩ :=
    henson_failedAmbientB3_lower_generation ell hell
      E hLoops hSym hClique N cut M hCut original hFree hFailure
  have hLevels :=
    hTop.symm.trans hGen
  obtain ⟨_,hEq⟩ :=
    hPosition_injective_bounded (ell-1) i (ell-1) j g
      le_rfl (Nat.le_of_lt hg) hLevels
  omega

end Kk
