import Kk.HensonI3Generation
import SuccessorTree.V10.I3ChosenOriginalGeneration
import Mathlib.Tactic

/-!
# Actual selected-pool corrected B3 failures in the Henson numerical H model

The ambient-original theorem is not the final I3 statement:
Algorithm 5.4 uses a stage-dependent selected subset of its
fixed original-name pool.

The pinned successor formalization already supplies a full
finite L-only forbidden-copy witness at a failed corrected B3
stage, and proves that each CHOSEN upper original name has
generation strictly above the tested level's generation.

Here we specialize this fact to the genuine four-pattern
normalized K_ell-free graph language (k = ell-1).
A failed selected-pool B3 test requires a selected name of
strictly higher generation. Consequently B3 cannot fail
if no selected pool name lies at higher generation.

Neither theorem asserts that every selected original is a
chosen active diary branch: auxiliary parameter originals may
also appear in the selected pool. Classifying them is the
remaining geometric bridge for the resolved-copy proof.
-/

namespace Kk

open SuccessorTree.V10

/-- A failed corrected finite-L age test of a true selected original
pool in numerical H necessarily uses a chosen selected original
of a strictly higher H generation.

The target is existential and does not hide a hypothetical
"auxiliary witness projects to selected F" assumption. -/
theorem henson_failedSelectedB3_has_higher_original
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N cut g iGen M : Nat)
    (hg : g < ell-1)
    (hCut : cut < N)
    (hGeneration : cut = hPosition (ell-1) iGen g)
    (original : Fin M → Fin N)
    (Selected : Fin M → Prop)
    (hFailure :
      ¬ (selectedStagePoolPrescribedData
        (finiteNumericH (normalizedGraphModel E) (ell-1) N)
        cut original Selected).CorrectedB3
          (hensonForbiddenFamily ell hell)) :
    ∃ v : Fin M, Selected v ∧
      ∃ j m : Nat, g < m ∧ m ≤ ell-1 ∧
        (original v).val = hPosition (ell-1) j m := by
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
  obtain ⟨W,hWfinite,hWsocle,hWdelete,t,P,e,r,hr,hrt,
      hIrred,hCopy,hLow,hHigh,i,hGenLast,hUpper⟩ :=
    finiteNumericH_failedSelectedStageB3_originals_higher
      (hensonForbiddenFamily ell hell)
      (normalizedGraphModel E)
      (by intro i; trivial)
      hAvoid (ell-1) N cut hCut original Selected
      hPatternBound hFailure
  let b : Fin t := ⟨r, hrt⟩
  obtain ⟨v,j,m,hSelected,hFree,hOriginal,hHigher,hm,hType⟩ :=
    hUpper b (by simp [b])
  have hRBound : r-1 ≤ ell-1 := by omega
  have hGenEq : g = r-1 := by
    obtain ⟨_hIndex,hSameGen⟩ :=
      hPosition_injective_bounded (ell-1)
        iGen g i (r-1) (Nat.le_of_lt hg) hRBound
        (hGeneration.symm.trans hGenLast)
    exact hSameGen
  refine ⟨v,hSelected,j,m,?_,hm,hOriginal⟩
  omega

/-- If the actual selected pool contains no name of higher generation,
corrected B3 cannot fail at this cut. This is a genuine specialized
I3 theorem about the selected pool, not an assertion of full
macro-diary age projection. -/
theorem henson_selectedB3_of_no_higher_original
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N cut g iGen M : Nat)
    (hg : g < ell-1)
    (hCut : cut < N)
    (hGeneration : cut = hPosition (ell-1) iGen g)
    (original : Fin M → Fin N)
    (Selected : Fin M → Prop)
    (hNoHigher : ∀ v : Fin M, Selected v →
      ∀ j m : Nat, (original v).val = hPosition (ell-1) j m →
        m ≤ g) :
    (selectedStagePoolPrescribedData
      (finiteNumericH (normalizedGraphModel E) (ell-1) N)
      cut original Selected).CorrectedB3
        (hensonForbiddenFamily ell hell) := by
  by_contra hFailure
  obtain ⟨v,hSelected,j,m,hHigher,hm,hOriginal⟩ :=
    henson_failedSelectedB3_has_higher_original
      ell hell E hLoops hSym hClique
      N cut g iGen M hg hCut hGeneration
      original Selected hFailure
  have hLow := hNoHigher v hSelected j m hOriginal
  omega

end Kk
