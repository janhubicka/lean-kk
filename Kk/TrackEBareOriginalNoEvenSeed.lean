import Kk.NumericHFullClosureSource
import Mathlib.Tactic

/-!
# Track E E75: bare numerical-H+ original Kpt seeds avoid positive even-real cuts

English proof and 18 adversarial checks were committed before Lean:
docs/track_e_bare_original_even_seed_exclusion_english_audit_20261119.md

The actual positive E free-level of any numerical-H+ physical original
cannot equal a genuine even-real hPosition. Hence an initial seed
family made ONLY of complete actual original Kpt types has NO seed
ending at any positive even-real cut, including after adjoining one
new complete bare original.

This does NOT apply to all-ancestor initial prefix pools; adding a
prefix itself as a seed can force spurious I1. Neither generated
parameter/meet terminals nor zero-column/full-socle geometry is
excluded by this theorem. E73's remaining conditions stay explicit.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- An ACTUAL complete Kpt ORIGINAL of finite numerical-H+ cannot
end at any positive even-real H+ cut, by genuine free E-level
oddness. No AlgorithmRun, ordinary-L symmetry or source closure
representation assumptions. -/
theorem finiteNumericH_bare_original_no_positive_real_level
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (v : Fin N) (idx g : Nat)
    (hPositive : 0 < hPosition k idx g) :
    LevelTree.lev
      ((finiteNumericH K k N).kptOriginal family hAvoid v) ≠
      hPosition k idx g := by
  intro hLev
  have hFree :
      (finiteNumericH K k N).freeLevel v.val =
        hPosition k idx g := by
    exact hLev
  have hPosFree :
      0 < (finiteNumericH K k N).freeLevel v.val := by
    omega
  exact (finiteNumericH_positive_freeLevel_ne_realPosition
    K k N v.val idx g v.isLt hPosFree) hFree

/-- A set of LITERAL complete physical numerical-H+ original
Kpt nodes has no initial seed at any positive even-real cut.
The ordinary original PREFIX POOL is NOT enough: the seed must
be equal to an original, not merely below one. -/
theorem finiteNumericH_bare_original_set_no_positive_real_seed
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (Y : Set (AdmissibleKptNode family))
    (hBare : ∀ y, y ∈ Y →
      ∃ v : Fin N,
        y = (finiteNumericH K k N).kptOriginal family hAvoid v)
    (idx g : Nat) (hPositive : 0 < hPosition k idx g) :
    ¬ ∃ y : AdmissibleKptNode family,
      y ∈ Y ∧ LevelTree.lev y = hPosition k idx g := by
  rintro ⟨y,hy,hLev⟩
  obtain ⟨v,hEq⟩ := hBare y hy
  rw [hEq] at hLev
  exact (finiteNumericH_bare_original_no_positive_real_level
    family K k N hAvoid v idx g hPositive) hLev

/-- If old seeds X are all literal actual ORIGINAL Kpt types,
adding one real NEW complete bare original keeps the initial
source free of positive even-real seed levels. This precisely
avoids the spurious I1 phenomenon caused by pre-inserting
all lower original ancestors as initial seeds. -/
theorem finiteNumericH_bare_one_root_growth_no_positive_real_seed
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (X : Set (AdmissibleKptNode family))
    (hBareOld : ∀ x, x ∈ X →
      ∃ v : Fin N,
        x = (finiteNumericH K k N).kptOriginal family hAvoid v)
    (newV : Fin N) (idx g : Nat)
    (hPositive : 0 < hPosition k idx g) :
    ¬ ∃ y : AdmissibleKptNode family,
      y ∈ (X ∪
        ({(finiteNumericH K k N).kptOriginal family hAvoid newV} :
          Set (AdmissibleKptNode family))) ∧
      LevelTree.lev y = hPosition k idx g := by
  apply finiteNumericH_bare_original_set_no_positive_real_seed
    family K k N hAvoid _ _ idx g hPositive
  intro y hy
  rcases hy with hx | hNew
  · exact hBareOld y hx
  · have hEq :
        y = (finiteNumericH K k N).kptOriginal family hAvoid newV := by
      simpa only [Set.mem_singleton_iff] using hNew
    exact ⟨newV,hEq⟩

end Kk
