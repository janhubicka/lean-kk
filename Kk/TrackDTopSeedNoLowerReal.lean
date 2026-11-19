import SuccessorTree.V10.HTopGenerationSeeds
import Mathlib.Tactic

/-!
# Track D: no initial top-generation Kpt seed at any positive lower-real cut

English-first proof and adversarial audit:
docs/audits/2026-11-19-track-d-top-seeds-no-positive-lower-english.md

Unlike the older noIntermediateReal theorem, the generation-zero
case r=0 is covered as long as the tested real cut is positive.
The seed family is the ACTUAL complete root original and its
chosen top-generation ancestors, not a shadow-selected diary.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The true Kpt top-generation seed family has no seed terminal
at ANY strictly positive lower-real numerical-H coordinate
hPosition(k,p,r),  r<k. This includes r=0.
No AlgorithmRun selected-level hypothesis is needed. -/
theorem numericHTopGenerationSeeds_noPositiveLowerReal
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (c : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ i : Nat, i ∈ blocks →
      hPosition k i k ≤ (finiteNumericH K k N).freeLevel c.val)
    (p r : Nat) (hr : r < k)
    (hPositive : 0 < hPosition k p r) :
    ∀ z : AdmissibleKptNode family,
      z ∈ numericHTopGenerationSeeds
        family K k N hAvoid c blocks hWithin →
      LevelTree.lev z ≠ hPosition k p r := by
  intro z hz hLevel
  obtain hRoot | ⟨i,hPrefix⟩ :=
    numericHTopGenerationSeeds_cases
      family K k N hAvoid c blocks hWithin z hz
  · rw [hRoot] at hLevel
    change (finiteNumericH K k N).freeLevel c.val =
      hPosition k p r at hLevel
    by_cases hFreeZero :
        (finiteNumericH K k N).freeLevel c.val = 0
    · omega
    · have hRootPositive :
          0 < (finiteNumericH K k N).freeLevel c.val := by omega
      exact (finiteNumericH_positive_freeLevel_ne_realPosition
        K k N c.val p r c.isLt hRootPositive) hLevel
  · rw [hPrefix] at hLevel
    have hLev :
        LevelTree.lev
          (LevelTree.ancestor
            ((finiteNumericH K k N).kptOriginal family hAvoid c)
            (hPosition k i.val k) (hWithin i.val i.property)) =
          hPosition k i.val k := LevelTree.level_ancestor _ _ _
    rw [hLev] at hLevel
    exact (numericHTopLevel_ne_lowerGeneration k i.val p r hr) hLevel

#print axioms Kk.numericHTopGenerationSeeds_noPositiveLowerReal

end Kk
