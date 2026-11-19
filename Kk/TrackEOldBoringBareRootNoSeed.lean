import Kk.TrackEBareOriginalNoEvenSeed
import Kk.TrackGBoringOnlyNoNoveltyRunTransfer
import Mathlib.Tactic

/-!
# Track E E76: one bare original never creates a positive even-real INITIAL I1
# seed at an OLD-BORING physical Kpt source cut

English-first mathematical proof and 20 hostile checks:
docs/track_e_old_boring_bare_new_root_no_seed_english_audit_20261119.md

The actual old initial seed set X is allowed to contain legitimate
dependent Kpt seeds. An old genuinely boring cut cannot equal
the height of ANY x∈X because initial seeds belong to true closure
and such a terminal would trigger genuine I1.

Add only ONE literal new complete original O_v, not all its lower
prefixes: E75's physical positive free-level parity excludes O_v
from ending at any positive even-real H+ coordinate. Thus the
new initial seed set X∪{O_v} automatically has no terminal
seed at an OLD-BORING positive even-real cut.

This does NOT rule out newly GENERATED meet/parameter terminals;
Track D's even-real whole-source no-I1 theorem is separate.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A genuinely BORING cut in one actual OLD Kpt AlgorithmRun
cannot coincide with the level of any OLD initial seed node,
including arbitrary legitimate dependent Kpt seeds. Closure
contains all initial seeds, so such a terminal would trigger I1.

Only the genuine old full source is used, never a selected-graph
age shadow or a numerical-H+ original representation assumption. -/
theorem kpt_old_actual_boring_no_initial_seed_at_cut
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top cut : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (hBoring : ¬ SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family)
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1)) X) cut) :
    ¬ ∃ x : AdmissibleKptNode family,
      x ∈ X ∧ LevelTree.lev x = cut := by
  rintro ⟨x,hX,hLevel⟩
  have hLive :
      x ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X :=
    (SMTree.Envelope.subset_closure
      (admissibleKptSTree family) (R.I (cut+1)) X) hX
  apply hBoring
  unfold SMTree.Envelope.IsInterestingAt
  exact Or.inl ⟨x,hLive,hLevel⟩

/-- For a genuinely OLD-BORING cut, adjoining ONE true bare
numerical-H+ original cannot introduce an INITIAL seed at any
positive even-real H+ address. The old seed set X may already
contain legitimate dependent parameters; we do not require
X to consist only of original nodes.

The new seed family is LITERALLY X∪{O_v}, not closure_I(X)∪...
or an all-ancestor source. -/
theorem finiteNumericH_oldBoring_bare_root_no_positive_real_seed
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (newV : Fin N) (idx g : Nat)
    (hPositive : 0 < hPosition k idx g)
    (hBoring : ¬ SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family)
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (hPosition k idx g+1)) X)
      (hPosition k idx g)) :
    ¬ ∃ y : AdmissibleKptNode family,
      y ∈ (X ∪
        ({(finiteNumericH K k N).kptOriginal family hAvoid newV} :
          Set (AdmissibleKptNode family))) ∧
      LevelTree.lev y = hPosition k idx g := by
  rintro ⟨y,hy,hLevel⟩
  rcases hy with hOld | hNew
  · exact (kpt_old_actual_boring_no_initial_seed_at_cut
      family X top (hPosition k idx g) R hBoring)
      ⟨y,hOld,hLevel⟩
  · have hyEq :
        y = (finiteNumericH K k N).kptOriginal family hAvoid newV := by
      simpa only [Set.mem_singleton_iff] using hNew
    rw [hyEq] at hLevel
    exact (finiteNumericH_bare_original_no_positive_real_level
      family K k N hAvoid newV idx g hPositive) hLevel

/-- The cut-membership formulation convenient for old-run stability:
if c<top is NOT selected by the OLD genuine AlgorithmRun, the
run's own interesting-step axiom shows it is truly boring, and
the same automatic positive even-real bare-root seed exclusion
follows. No auxiliary source or generated I1 elimination follows. -/
theorem finiteNumericH_oldUnselected_bare_root_no_positive_real_seed
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (newV : Fin N) (idx g : Nat)
    (hPositive : 0 < hPosition k idx g)
    (hCut : hPosition k idx g < top)
    (hNotSelected : hPosition k idx g ∉ R.I (hPosition k idx g)) :
    ¬ ∃ y : AdmissibleKptNode family,
      y ∈ (X ∪
        ({(finiteNumericH K k N).kptOriginal family hAvoid newV} :
          Set (AdmissibleKptNode family))) ∧
      LevelTree.lev y = hPosition k idx g := by
  have hBoring : ¬ SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family)
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (hPosition k idx g+1)) X)
      (hPosition k idx g) := by
    intro hInteresting
    exact hNotSelected
      (R.interesting_step (hPosition k idx g) hCut hInteresting)
  exact finiteNumericH_oldBoring_bare_root_no_positive_real_seed
    family K k N hAvoid X top R newV idx g
    hPositive hBoring

end Kk
