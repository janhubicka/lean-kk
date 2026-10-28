import Kk.HensonSelectedI3
import SuccessorTree.V10.I3ChosenOriginalGeneration
import Mathlib.Tactic

/-!
# No top-generation selected-stage corrected B3 failure in Henson H

The manuscript uses numerical H generation k = ell (maximum
forbidden size), rather than the minimal sufficient ell-1.
This theorem works at ANY k with ell <= k+1.

The pinned successor library proves a stronger selected-original
I3 witness theorem than is needed here. A corrected B3 failure
in an actual selected-stage pool must have the tested cut at
generation r-1 and a chosen upper original at generation m>r-1
with m<=k. Thus it CANNOT occur at generation k.

The proof uses the actual numerical H model, the exact four
normalized K_ell-free forbidden patterns, and the original
stage's selected pool. It is not an assertion that the user's
resolved macro-diary construction has already been identified
with this selected-stage prescription.
-/

namespace Kk

open SuccessorTree.V10

/-- Under the ordinary irreflexive symmetric K_ell-free graph
hypotheses, a selected pool of genuine numerical H originals
cannot fail corrected B3 at a cut of TOP generation k.

Unlike an ambient-pool statement, no free-cut hypothesis on
unselected ambient originals appears: only the genuine
selected-stage prescribed function is tested. -/
theorem henson_selected_top_generation_B3
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hBoundGeneration : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N cut M i : Nat)
    (hCut : cut < N)
    (hTop : cut = hPosition k i k)
    (original : Fin M → Fin N)
    (Selected : Fin M → Prop) :
    (selectedStagePoolPrescribedData
      (finiteNumericH (normalizedGraphModel E) k N)
      cut original Selected).CorrectedB3
        (hensonForbiddenFamily ell hell) := by
  have hAvoid :
      ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
        bad.Avoids (normalizedGraphModel E) :=
    (hensonForbiddenFamily_avoids_iff ell hell E).2
      ⟨hLoops,hSym,hClique⟩
  have hPatternBound : ∀ bad,
      bad ∈ hensonForbiddenFamily ell hell →
      bad.patternCard ≤ k+1 := by
    intro bad hb
    exact (hensonForbiddenFamily_patternCard_le ell hell bad hb).trans
      hBoundGeneration
  by_contra hFailure
  obtain ⟨W,hFinite,hSocle,hDelete,t,P,e,r,hr,hrt,
      hIrred,hCopy,hLow,hHigh,j,hGen,hUpper⟩ :=
    finiteNumericH_failedSelectedStageB3_originals_higher
      (hensonForbiddenFamily ell hell)
      (normalizedGraphModel E)
      (by intro n; trivial)
      hAvoid k N cut hCut original Selected
      hPatternBound hFailure
  let upper : Fin t := ⟨r, hrt⟩
  obtain ⟨v,jOriginal,m,hSelected,hFree,hOriginal,hHigher,hm,hType⟩ :=
    hUpper upper (by simp [upper])
  have hRBound : r-1 ≤ k := by omega
  obtain ⟨_hIndex,hGenEq⟩ :=
    hPosition_injective_bounded k i k j (r-1)
      le_rfl hRBound (hTop.symm.trans hGen)
  omega

end Kk
