import Kk.HFirstGadgetFreeCut
import SuccessorTree.V10.KptStageClosureNormalForm
import Mathlib.Tactic

/-!
# When a selected later level forces its genuine Kpt parameter into closure

The exact numerical-H free cut alone does not place an auxiliary
original in Algorithm 5.4's selected source. The selected level set I
and the *actual* successor parameter list do.

This module proves the missing generic forward implication: if a
genuine original a is one of the closure seeds, i lies below its free
cut, i is in I, and the Kpt original at numerical address i has
positive free cut, then that original is forced into the complete
meet-and-parameter closure. The proof obtains the real successor
parameter list from the admissible Kpt S-tree's S3 representation,
not from a guessed E incidence.

The second theorem specializes the statement to the numerical H
first-gadget coordinates (cut 10, future original 22, active top
seed 38). The only remaining premise is that level 22 is in I
and the top original at address 38 is among the closure seeds.
These premises are not inferred from the abstract macro-diary.

This isolates exactly what must be proved or ruled out for the
circulation manuscript's "first auxiliary clique level is boring"
claim. The results do NOT prove failure of the actual AlgorithmRun
at cut 10, because the selection of level 22 remains conditional.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- An actual selected Kpt successor step along a seed original
forces its complete positive-free-level parameter original into
the full Algorithm 5.4 closure. No fictitious parameter node or
uncertified source representation is assumed. -/
theorem kpt_closure_contains_positive_parameter_of_seed
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (I : Set Nat)
    (X : Set (AdmissibleKptNode family))
    (v : Fin A.size)
    (hSeed : A.kptOriginal family hAvoid v ∈ X)
    (i : Nat)
    (hiI : i ∈ I)
    (hiCut : i < A.freeLevel v.val)
    (hiPositive : 0 < A.freeLevel i) :
    ∃ hiSize : i < A.size,
      A.kptOriginal family hAvoid (⟨i, hiSize⟩ : Fin A.size) ∈
        SMTree.Envelope.closure (admissibleKptSTree family) I X := by
  classical
  let a : AdmissibleKptNode family := A.kptOriginal family hAvoid v
  have hia : i < LevelTree.lev a := by
    change i < A.freeLevel v.val
    exact hiCut
  let a0 := LevelTree.ancestor a i (Nat.le_of_lt hia)
  let a1 := LevelTree.ancestor a (i+1) (Nat.succ_le_iff.mpr hia)
  have h0a : a0 ≤ a := LevelTree.ancestor_le a i (Nat.le_of_lt hia)
  have h1a : a1 ≤ a := LevelTree.ancestor_le a (i+1) (Nat.succ_le_iff.mpr hia)
  have h0level : LevelTree.lev a0 = i :=
    LevelTree.level_ancestor a i (Nat.le_of_lt hia)
  have h1level : LevelTree.lev a1 = i+1 :=
    LevelTree.level_ancestor a (i+1) (Nat.succ_le_iff.mpr hia)
  have h01 : a0 ≤ a1 := by
    rcases LevelTree.comparable_below h0a h1a with h | h
    · exact h
    · have hlev := LevelTree.level_le_of_le h
      rw [h0level, h1level] at hlev
      omega
  have hcov : a0 ⋖ a1 := by
    apply LevelTree.covBy_of_le_level_succ h01
    rw [h0level, h1level]
  obtain ⟨p,c,hStep⟩ := (admissibleKptSTree family).s3 hcov
  obtain ⟨hiSize,hParam⟩ :=
    admissibleKpt_crossing_parameter
      family A hAvoid v a le_rfl i hia p c hStep
  have hMemRaw : A.rawTypeAtFree i ∈ p.map Subtype.val := by
    rw [hParam]
    simp [Nat.ne_of_gt hiPositive]
  obtain ⟨x,hx,hRaw⟩ := List.mem_map.mp hMemRaw
  have hOrig : x = A.kptOriginal family hAvoid
      (⟨i,hiSize⟩ : Fin A.size) := Subtype.ext hRaw
  have haClosure :
      a ∈ SMTree.Envelope.closure (admissibleKptSTree family) I X :=
    (SMTree.Envelope.subset_closure
      (admissibleKptSTree family) I X) hSeed
  have hClosed :=
    SMTree.Envelope.closure_parameterClosed
      (admissibleKptSTree family) I X
  have hxClosure :
      x ∈ SMTree.Envelope.closure (admissibleKptSTree family) I X :=
    hClosed haClosure hiI hia hStep hx
  refine ⟨hiSize, ?_⟩
  rw [← hOrig]
  exact hxClosure

/-- The actual finite-H free cuts put the generation-one original
at address 22 in the parameter closure of the top original at 38,
PROVIDED level 22 is selected by Algorithm 5.4. The base L-graph
may be any forbidden-free graph: this parameter fact uses the
literal E relation and the Kpt successor representation.

In particular the E eligibility gate cannot keep this parameter
out of the earlier cut 10 once the successor at 22 is selected.
The remaining unresolved question is whether 22 belongs to the
selected set I in the special resolved diary. -/
theorem numericH_first_gadget_second_original_in_closure
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K 4 40).L)
    (I : Set Nat)
    (X : Set (AdmissibleKptNode family))
    (hSeed : (finiteNumericH K 4 40).kptOriginal family hAvoid
      (⟨38, by decide⟩ : Fin (finiteNumericH K 4 40).size) ∈ X)
    (hSelected22 : 22 ∈ I) :
    (finiteNumericH K 4 40).kptOriginal family hAvoid
      (⟨22, by decide⟩ : Fin (finiteNumericH K 4 40).size) ∈
        SMTree.Envelope.closure (admissibleKptSTree family) I X := by
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K 4 40
  have hFree22 : 0 < A.freeLevel 22 := by
    have hFree :=
      finiteNumericH_next_generation_one_freeLevel K 4 40 1
        (by decide) (by decide)
    change A.freeLevel 22 = 11 at hFree
    omega
  have hE : A.E 22 38 = true := by
    change finiteNumericHE 4 40 22 38 = true
    apply (finiteNumericHE_true_iff 4 40 22 38).2
    refine ⟨by decide, ?_⟩
    have hGenerated : generatedE 4 3 4 22 :=
      generatedE_of_allowedPair 4 2 3 1 4
        (by decide) (by decide) (Or.inl (by decide))
    have hRaw :=
      (exactHEBool_at_real_iff 4 3 4 22 (by decide)).2 hGenerated
    simpa [hPosition] using hRaw
  have hCut38 : 22 < A.freeLevel 38 :=
    (A.E_iff_freeLevel 22 38).1 hE
  obtain ⟨hiSize,hIn⟩ :=
    kpt_closure_contains_positive_parameter_of_seed
      family A hAvoid I X (⟨38, by decide⟩ : Fin A.size)
      hSeed 22 hSelected22 hCut38 hFree22
  exact hIn

end Kk
