import Kk.IndexedPhysicalCrossing
import Mathlib.Tactic

/-!
# Track E adversarial regression: complete crossing spectra miss terminal nodes

Even the collection of ALL complete per-cut old/upper L+ crossing
relations does NOT determine the underlying complete Kpt node set.
Adding an ancestor x below a node y already present contributes
no new full crossings, since y realizes all the old+upper ancestors
of x wherever x crosses. Nevertheless the added terminal prefix
is a new actual node and may change the (I1) presence event.

The proof uses literal admissible Kpt nodes and genuine LevelTree
ancestors, not an abstract shadow graph.

English proof committed first:
  docs/track_e_indexed_physical_crossing_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Adding an ancestor of an already present node is invisible to
EVERY full old/upper L+ crossing relation. This preserves all E atoms
because it compares exact raw ancestors, not L-reduct projections. -/
theorem full_physical_crossing_ignores_redundant_terminal_ancestor
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family))
    (x y : AdmissibleKptNode family)
    (hxy : x ≤ y)
    (hy : y ∈ Z)
    (cut : Nat) :
    FullPhysicalClosureCrossing family (Set.insert x Z) cut =
      FullPhysicalClosureCrossing family Z cut := by
  ext p
  constructor
  · rintro ⟨z,hz,hCut,hOld,hUpper⟩
    rcases (Set.mem_insert_iff.mp hz) with hzx | hzZ
    · subst z
      have hyCut : cut < LevelTree.lev y := by
        have hLevels := LevelTree.level_le_of_le hxy
        omega
      have hOldEq :
          LevelTree.ancestor x cut (Nat.le_of_lt hCut) =
            LevelTree.ancestor y cut (Nat.le_of_lt hyCut) :=
        LevelTree.eq_ancestor_of_le
          ((LevelTree.ancestor_le x cut (Nat.le_of_lt hCut)).trans hxy)
          (LevelTree.level_ancestor x cut (Nat.le_of_lt hCut))
          (Nat.le_of_lt hyCut)
      have hUpperEq :
          LevelTree.ancestor x (cut+1) (Nat.succ_le_iff.mpr hCut) =
            LevelTree.ancestor y (cut+1) (Nat.succ_le_iff.mpr hyCut) :=
        LevelTree.eq_ancestor_of_le
          ((LevelTree.ancestor_le x (cut+1)
            (Nat.succ_le_iff.mpr hCut)).trans hxy)
          (LevelTree.level_ancestor x (cut+1)
            (Nat.succ_le_iff.mpr hCut))
          (Nat.succ_le_iff.mpr hyCut)
      refine ⟨y,hy,hyCut,?_,?_⟩
      · exact hOld.trans (congrArg Subtype.val hOldEq)
      · exact hUpper.trans (congrArg Subtype.val hUpperEq)
    · exact ⟨z,hzZ,hCut,hOld,hUpper⟩
  · rintro ⟨z,hz,hCut,hOld,hUpper⟩
    exact ⟨z,Set.mem_insert_of_mem hz,hCut,hOld,hUpper⟩

/-- The terminal-prefix regression is a literal inequality of
actual Kpt node SETS, despite full crossing equality at EVERY cut.
It only assumes a proper comparable pair; no false assertion that
both sets are actual distinct AlgorithmRun closures is made. -/
theorem distinct_kpt_node_sets_same_all_full_crossings
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (x y : AdmissibleKptNode family)
    (hxy : x ≤ y) (hne : x ≠ y) :
    Set.insert x ({y} : Set (AdmissibleKptNode family)) ≠
        ({y} : Set (AdmissibleKptNode family)) ∧
      ∀ cut,
        FullPhysicalClosureCrossing family
          (Set.insert x ({y} : Set (AdmissibleKptNode family))) cut =
        FullPhysicalClosureCrossing family
          ({y} : Set (AdmissibleKptNode family)) cut := by
  constructor
  · intro hEq
    have hx : x ∈ ({y} : Set (AdmissibleKptNode family)) := by
      rw [← hEq]
      simp
    have hxyEq : x = y := by simpa using hx
    exact hne hxyEq
  · intro cut
    exact full_physical_crossing_ignores_redundant_terminal_ancestor
      family {y} x y hxy (by simp) cut

end Kk
