import Kk.B3FailedCutGeneration
import Kk.B3ActualI3PhysicalCore
import Kk.NumericHStructuralCutClassifier
import Mathlib.Tactic

/-!
# Track D: selected finite numerical-H AlgorithmRun cuts are structural or lower-real

English-first mathematical proof and 19 hostile checks:
docs/audits/2026-11-15-track-d-run-real-lower-trichotomy-english.md

STACKED on draft PR #227: do not merge into main or manuscript markers
until the predecessor and exact-head dedicated gate have succeeded.

The true pre-cut source is closure(Run.I(cut+1),X), while the ACTUAL
maintained name pool is based on Run.I 0. Full physical B3
failure is certified for this exact source before invoking the
new numerical H forbidden clique relocation theorem.

Selected cut -> actual I1 or actual I2 or a real lower-generation cut.
This is NOT a complete boringness proof: structural I1/I2 events
must still be shown to lie in the proposed retained-level set.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- True selected positive nonstructural (I3) cuts of ONE actual
finite Henson numerical-H AlgorithmRun have REAL non-top physical
coordinates, with no prior generation assumption.

The theorem needs absence of both literal full pre-cut I1 and
literal full pre-cut competing I2; they are not graph-age surrogates.
-/
theorem henson_actualRun_nonstructural_selected_has_lower_real_cut
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N : Nat)
    (U : Finset (Fin N))
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (X : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (hX : X ⊆ ambientPrefixPool
      (hensonForbiddenFamily ell hell)
      (finiteNumericH (normalizedGraphModel E) k N)
      hAvoid (U : Set (Fin N)))
    (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell)) X top)
    (hTop : ∃ x ∈ X, LevelTree.lev x = top)
    (cut : Nat) (hPos : 0 < cut)
    (hBelow : cut < top) (hCut : cut < N)
    (hSelected : cut ∈ Run.I 0)
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (cut+1)) X ∧
      LevelTree.lev z = cut)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      a ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (cut+1)) X ∧
      ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        b ∈ SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily ell hell))
          (Run.I (cut+1)) X ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :
    ∃ g idx : Nat, g < k ∧ cut = hPosition k idx g := by
  classical
  let P := actualHensonRunCutOccurrence
    ell hell k hK E hLoops hSym hClique
    N U hAvoid X top Run cut hCut hNoI2
  have hCore :
      HensonPhysicalCutStarBadCore
        ell hell P.k P.N cut P.M P.E P.original P.Full :=
    henson_actualRun_nonstructural_I3_has_exact_physical_core
      ell hell k hK E hLoops hSym hClique
      N U hAvoid X hX top Run hTop
      cut hPos hBelow hCut hSelected hNoI1 hNoI2
  have hExact :=
    henson_actualRun_complete_fullB3_failure_iff_physical_bad_core
      ell hell k hK E hLoops hSym hClique
      N U hAvoid X hX top Run cut hCut hBelow hNoI2
  have hFailed :
      ¬ P.fullProfile.CorrectedB3
        (hensonForbiddenFamily ell hell) :=
    hExact.2.2.mpr hCore
  have hSelectedFailed :
      ¬ (selectedStagePoolPrescribedData
        (finiteNumericH (normalizedGraphModel E) k N)
        cut P.original P.Full).CorrectedB3
          (hensonForbiddenFamily ell hell) := hFailed
  exact henson_failed_selectedB3_forces_lower_real_generation
    ell hell k hK E hLoops hSym hClique
    N cut P.M hCut P.original P.Full hSelectedFailed

/-- A genuinely selected positive finite AlgorithmRun cut is
classified by the FULL pre-cut Kpt source:
either an I1 node at cut, or a competing I2 meet at cut, or
a physically REAL numerical-H generation strictly below k.

This is a precise source-level trichotomy, NOT a selected age test,
and not a claim that the chosen retained set automatically includes
all structural cuts. -/
theorem henson_actualRun_selected_structural_or_lower_real_cut
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N : Nat)
    (U : Finset (Fin N))
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (X : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (hX : X ⊆ ambientPrefixPool
      (hensonForbiddenFamily ell hell)
      (finiteNumericH (normalizedGraphModel E) k N)
      hAvoid (U : Set (Fin N)))
    (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell)) X top)
    (hTop : ∃ x ∈ X, LevelTree.lev x = top)
    (cut : Nat) (hPos : 0 < cut)
    (hBelow : cut < top) (hCut : cut < N)
    (hSelected : cut ∈ Run.I 0) :
    let Z := SMTree.Envelope.closure
      (admissibleKptSTree (hensonForbiddenFamily ell hell))
      (Run.I (cut+1)) X
    KptI1AtCut (hensonForbiddenFamily ell hell) Z cut ∨
      KptI2MeetAtCut (hensonForbiddenFamily ell hell) Z cut ∨
      ∃ g idx : Nat, g < k ∧ cut = hPosition k idx g := by
  classical
  intro Z
  by_cases hI1 :
      KptI1AtCut (hensonForbiddenFamily ell hell) Z cut
  · exact Or.inl hI1
  by_cases hI2 :
      KptI2MeetAtCut (hensonForbiddenFamily ell hell) Z cut
  · exact Or.inr (Or.inl hI2)
  have hNoI1 :
      ¬ ∃ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily ell hell))
          (Run.I (cut+1)) X ∧ LevelTree.lev z = cut := hI1
  have hNoI2 :
      ¬ ∃ a : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        a ∈ SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily ell hell))
          (Run.I (cut+1)) X ∧
        ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
          b ∈ SMTree.Envelope.closure
            (admissibleKptSTree (hensonForbiddenFamily ell hell))
            (Run.I (cut+1)) X ∧
          SMTree.Envelope.SameComponent a b ∧
          LevelTree.lev (LevelTree.meet a b) = cut := hI2
  have hReal :=
    henson_actualRun_nonstructural_selected_has_lower_real_cut
      ell hell k hK E hLoops hSym hClique
      N U hAvoid X hX top Run hTop
      cut hPos hBelow hCut hSelected hNoI1 hNoI2
  exact Or.inr (Or.inr hReal)

/-- If the TESTED numerical cut is not a real generation below top,
selection by AlgorithmRun can ONLY be structural I1 or I2 in the
complete pre-cut closure. This covers fake odd and top-generation
physical coordinates without treating them as automatically skippable.
-/
theorem henson_actualRun_selected_non_lower_real_requires_structural
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N : Nat)
    (U : Finset (Fin N))
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (X : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (hX : X ⊆ ambientPrefixPool
      (hensonForbiddenFamily ell hell)
      (finiteNumericH (normalizedGraphModel E) k N)
      hAvoid (U : Set (Fin N)))
    (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell)) X top)
    (hTop : ∃ x ∈ X, LevelTree.lev x = top)
    (cut : Nat) (hPos : 0 < cut)
    (hBelow : cut < top) (hCut : cut < N)
    (hNotLower : ∀ g idx : Nat,
      g < k → cut ≠ hPosition k idx g)
    (hSelected : cut ∈ Run.I 0) :
    let Z := SMTree.Envelope.closure
      (admissibleKptSTree (hensonForbiddenFamily ell hell))
      (Run.I (cut+1)) X
    KptI1AtCut (hensonForbiddenFamily ell hell) Z cut ∨
      KptI2MeetAtCut (hensonForbiddenFamily ell hell) Z cut := by
  classical
  intro Z
  have hTri :=
    henson_actualRun_selected_structural_or_lower_real_cut
      ell hell k hK E hLoops hSym hClique
      N U hAvoid X hX top Run hTop
      cut hPos hBelow hCut hSelected
  change KptI1AtCut (hensonForbiddenFamily ell hell) Z cut ∨
    KptI2MeetAtCut (hensonForbiddenFamily ell hell) Z cut ∨
    ∃ g idx : Nat, g < k ∧ cut = hPosition k idx g at hTri
  rcases hTri with hI1 | hI2 | hReal
  · exact Or.inl hI1
  · exact Or.inr hI2
  · obtain ⟨g,idx,hg,hReal⟩ := hReal
    exact False.elim ((hNotLower g idx hg) hReal)

#print axioms henson_actualRun_nonstructural_selected_has_lower_real_cut
#print axioms henson_actualRun_selected_structural_or_lower_real_cut
#print axioms henson_actualRun_selected_non_lower_real_requires_structural

end Kk
