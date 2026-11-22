import Kk.TrackEFiniteSeedRootOriginalCompression
import Mathlib.Tactic

/-!
# Track E E90: actual small root-original pool for one BARE new Kpt root

English-first proof and 20 hostile checks:
docs/track_e_bare_root_small_original_pool_english_audit_20261122.md

Given a finite OLD INITIAL Kpt seed family X0 (which may contain
legitimate dependent Kpt nodes), choose at most X0.card physical
originals that literally represent those OLD seeds by E89, then
EXPLICITLY retain the one actual new BARE original coordinate newV.

This constructs a common original-root pool U' contained in the
previous pool U, with newV in U' and U'.card ≤ X0.card+1,
representing the genuine new INITIAL seed family
   Y = (X0 : Set KptNode) ∪ {O_new}.
No all-ancestor pre-insertion, guessed source Plan, or
old-seed-is-original assumption is used.

For a genuine OLD AlgorithmRun R on X0, verified E86 then
bounds the number of maximal complete OLD Kpt-prefix tests in
the CHOSEN reduced stage presentation U':
   Need(U').card ≤ X0.card+1+|R.I0|.

This is an EXISTENTIAL representation bound, NOT a claim that the
old arbitrary padded Need(U) is small; old root-role requirements,
maximal witness existence, diary-uniform old selected level count,
unsafe physical cut quietness and labelled source orbit remain OPEN.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Finite OLD Kpt seed nodes have a true physical root-original
pool of size ≤ the OLD seed count while retaining one SPECIFIED
bare new original address newV.

The OLD seed nodes need not themselves be literal originals;
each is only required to be a genuine COMPLETE Kpt prefix of
some actual physical original already in the old pool U.

Adding newV explicitly avoids any unproved injectivity or
canonical choice of the original Kpt type representation. -/
theorem finite_kpt_old_seeds_plus_forced_bare_root_small_pool
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (OldSeeds : Finset (AdmissibleKptNode family))
    (U : Finset (Fin A.size))
    (hSeeds : ∀ x : AdmissibleKptNode family, x ∈ OldSeeds →
      ∃ v : Fin A.size,
        v ∈ U ∧ x ≤ A.kptOriginal family hAvoid v)
    (newV : Fin A.size) (hNewInU : newV ∈ U) :
    ∃ U' : Finset (Fin A.size),
      U' ⊆ U ∧ newV ∈ U' ∧ U'.card ≤ OldSeeds.card+1 ∧
      (∀ x : AdmissibleKptNode family, x ∈ OldSeeds →
        ∃ v : Fin A.size,
          v ∈ U' ∧ x ≤ A.kptOriginal family hAvoid v) := by
  classical
  obtain ⟨U0,hU0Sub,hU0Card,hU0Rep⟩ :=
    finite_kpt_seed_original_root_pool_compression
      family A hAvoid OldSeeds U hSeeds
  let U' : Finset (Fin A.size) := insert newV U0
  have hSub : U' ⊆ U := by
    intro v hv
    rcases Finset.mem_insert.mp hv with hEq | hOld
    · subst v
      exact hNewInU
    · exact hU0Sub hOld
  have hCardInsert : U'.card ≤ U0.card+1 := by
    by_cases hOld : newV ∈ U0
    · simp [U',hOld]
    · simp [U',hOld]
  have hCard : U'.card ≤ OldSeeds.card+1 :=
    hCardInsert.trans (Nat.add_le_add_right hU0Card 1)
  refine ⟨U',hSub,Finset.mem_insert_self _ _,hCard,?_⟩
  intro x hx
  obtain ⟨v,hv,hBelow⟩ := hU0Rep x hx
  exact ⟨v,Finset.mem_insert_of_mem hv,hBelow⟩

/-- Actual finite numerical-H+ one-BARE-root extension with an
EXISTENTIALLY chosen common physical root-original presentation
of size at most (OLD finite seed count)+1.

This is a source-exact bookkeeping reduction for the same genuine
seed sets X and Y and the same old AlgorithmRun selected tails;
the candidate parameter-closed Kpt source itself is unchanged.

One maximal OLD Kpt-prefix TEST per genuinely needed original
therefore has a budget bounded by old seed count+1+number of
ACTUALLY selected OLD levels -- independently of physical N
and arbitrary boring gaps. This is NOT an existence theorem for
the witnesses, and does not prove the abstract diary bounds. -/
theorem finiteNumericH_bare_one_root_small_pool_selected_budget
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (OldSeeds : Finset (AdmissibleKptNode family))
    (U : Finset (Fin N))
    (hOldRepresented :
      (OldSeeds : Set (AdmissibleKptNode family)) ⊆
        ambientPrefixPool family (finiteNumericH K k N)
          hAvoid (U : Set (Fin N)))
    (newV : Fin N) (hNewInU : newV ∈ U)
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
      (OldSeeds : Set (AdmissibleKptNode family)) top)
    (Allowed : Set Nat) :
    ∃ U' : Finset (Fin N),
      U' ⊆ U ∧ newV ∈ U' ∧ U'.card ≤ OldSeeds.card+1 ∧
      ((OldSeeds : Set (AdmissibleKptNode family)) ∪
        ({(finiteNumericH K k N).kptOriginal family hAvoid newV} :
          Set (AdmissibleKptNode family))) ⊆
        ambientPrefixPool family (finiteNumericH K k N)
          hAvoid (U' : Set (Fin N)) ∧
      (kpt_originals_needing_max_old_socle_test
        family K k N hAvoid U'
        (OldSeeds : Set (AdmissibleKptNode family))
        ((OldSeeds : Set (AdmissibleKptNode family)) ∪
          ({(finiteNumericH K k N).kptOriginal family hAvoid newV} :
            Set (AdmissibleKptNode family)))
        top R Allowed).card ≤
      OldSeeds.card+1 +
        (kpt_old_actual_selected_levels
          family (OldSeeds : Set (AdmissibleKptNode family))
          top R).card := by
  classical
  obtain ⟨U0,hU0Sub,hU0Card,hOldRep0,_hOldBudget⟩ :=
    finiteNumericH_candidate_finite_seed_original_budget
      family K k N hAvoid OldSeeds U hOldRepresented
      (OldSeeds : Set (AdmissibleKptNode family))
      top R Allowed
  let U' : Finset (Fin N) := insert newV U0
  have hSub : U' ⊆ U := by
    intro v hv
    rcases Finset.mem_insert.mp hv with hEq | hOld
    · subst v
      exact hNewInU
    · exact hU0Sub hOld
  have hCardInsert : U'.card ≤ U0.card+1 := by
    by_cases hOld : newV ∈ U0
    · simp [U',hOld]
    · simp [U',hOld]
  have hCard : U'.card ≤ OldSeeds.card+1 :=
    hCardInsert.trans (Nat.add_le_add_right hU0Card 1)
  have hNewRepresented :
      ((OldSeeds : Set (AdmissibleKptNode family)) ∪
        ({(finiteNumericH K k N).kptOriginal family hAvoid newV} :
          Set (AdmissibleKptNode family))) ⊆
      ambientPrefixPool family (finiteNumericH K k N)
        hAvoid (U' : Set (Fin N)) := by
    intro z hz
    rcases hz with hOld | hNew
    · obtain ⟨o,⟨v,hv,rfl⟩,hBelow⟩ := hOldRep0 hOld
      have hv' : v ∈ U' :=
        Finset.mem_insert_of_mem (Finset.mem_coe.mp hv)
      exact ⟨(finiteNumericH K k N).kptOriginal family hAvoid v,
        ⟨v,Finset.mem_coe.mpr hv',rfl⟩,hBelow⟩
    · have hEq :
          z = (finiteNumericH K k N).kptOriginal family hAvoid newV := by
        simpa only [Set.mem_singleton_iff] using hNew
      subst z
      exact ⟨(finiteNumericH K k N).kptOriginal family hAvoid newV,
        ⟨newV,Finset.mem_coe.mpr (Finset.mem_insert_self _ _),rfl⟩,
        le_rfl⟩
  have hNeedBound :=
    kpt_originals_needing_max_old_socle_test_card_le_root_add_selected
      family K k N hAvoid U'
      (OldSeeds : Set (AdmissibleKptNode family))
      ((OldSeeds : Set (AdmissibleKptNode family)) ∪
        ({(finiteNumericH K k N).kptOriginal family hAvoid newV} :
          Set (AdmissibleKptNode family)))
      top R Allowed
  refine ⟨U',hSub,Finset.mem_insert_self _ _,hCard,hNewRepresented,?_⟩
  exact hNeedBound.trans
    (Nat.add_le_add_right hCard
      (kpt_old_actual_selected_levels
        family (OldSeeds : Set (AdmissibleKptNode family))
        top R).card)

end Kk
