import Kk.TrackESelectedLevelOriginalBudget
import Mathlib.Tactic

/-!
# Track E E89: compress a finite initial Kpt seed family's TRUE
# physical original root pool before counting maximal OLD prefix tests

English proof and 22 hostile adversarial checks were committed first:
docs/track_e_finite_seed_minimal_root_original_pool_english_audit_20261122.md

If every node of a FINITE actual Kpt seed family Y is literally
below some true original O_v with v in a finite physical root
pool U, choose ONE true original representative per seed.
The image U' of those choices is a valid original-root pool:
   U' ⊆ U, U'.card ≤ Y.card,
and every seed remains a literal Kpt prefix of a true original
named by U'. No graph-age projection or new AlgorithmRun is used.

For a finite numerical-H+ source and one genuine OLD Kpt AlgorithmRun
R, E86 then bounds the number of maximal old Kpt prefix-test
originals, for the CHOSEN reduced presentation U', by
   Need(U').card ≤ Y.card + |R.I 0|.

This is an EXISTENTIAL bookkeeping reduction, not a bound on the
Need set for the original possibly padded U; in the one-bare-root
theorem one must ALSO retain the stipulated new physical name
newV ∈ U', or add it explicitly. No uniform finite diary count,
prefix witness existence or common labelled source orbit follows.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A FINITE family of actual Kpt seeds, each a literal prefix of
some physical original in U, has a true physical original
representing pool U' of cardinal at most the number of seeds.

No Kpt closure, selected numerical levels, target AlgorithmRun,
or guessed graph-age code enters the theorem. A seed may share
an original with another seed, so the bound need not be sharp.
The chosen U' is a SUBSET of the original input pool U. -/
theorem finite_kpt_seed_original_root_pool_compression
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (Y : Finset (AdmissibleKptNode family))
    (U : Finset (Fin A.size))
    (hSeeds : ∀ y : AdmissibleKptNode family, y ∈ Y →
      ∃ v : Fin A.size,
        v ∈ U ∧ y ≤ A.kptOriginal family hAvoid v) :
    ∃ U' : Finset (Fin A.size),
      U' ⊆ U ∧ U'.card ≤ Y.card ∧
      (∀ y : AdmissibleKptNode family, y ∈ Y →
        ∃ v : Fin A.size,
          v ∈ U' ∧ y ≤ A.kptOriginal family hAvoid v) := by
  classical
  let Ytype := {y : AdmissibleKptNode family // y ∈ Y}
  have hChoice : ∀ yy : Ytype,
      ∃ v : Fin A.size,
        v ∈ U ∧ yy.val ≤ A.kptOriginal family hAvoid v := by
    intro yy
    exact hSeeds yy.val yy.property
  let chosen : Ytype → Fin A.size :=
    fun yy => Classical.choose (hChoice yy)
  have hChosen (yy : Ytype) :
      chosen yy ∈ U ∧
      yy.val ≤ A.kptOriginal family hAvoid (chosen yy) :=
    Classical.choose_spec (hChoice yy)
  let U' : Finset (Fin A.size) := Y.attach.image chosen
  have hSubset : U' ⊆ U := by
    intro v hv
    obtain ⟨yy,_hyy,rfl⟩ := Finset.mem_image.mp hv
    exact (hChosen yy).1
  have hCard : U'.card ≤ Y.card := by
    calc
      U'.card ≤ Y.attach.card := Finset.card_image_le
      _ = Y.card := Finset.card_attach
  refine ⟨U',hSubset,hCard,?_⟩
  intro y hy
  let yy : Ytype := ⟨y,hy⟩
  have hIn : chosen yy ∈ U' := by
    apply Finset.mem_image.mpr
    exact ⟨yy,Finset.mem_attach yy,rfl⟩
  exact ⟨chosen yy,hIn,(hChosen yy).2⟩

/-- For one TRUE finite numerical-H+ model and one genuine OLD Kpt
AlgorithmRun R on seeds X, any FINITE represented candidate new
seed family Y has SOME reduced physical original-pool U'⊆U,
with |U'|≤Y.card, that still literally represents every seed.

Applying the independently verified E86 budget to this REDUCED
presentation gives:
   Need(U').card ≤ Y.card + number of selected OLD Kpt levels.

The old/new FULL source closures remain based on the same seed
sets X,Y and the same OLD R.I(c+1); only the accounting root
pool changes. No bound on Need(U) for arbitrary padded U follows,
and no specific newV is guaranteed to remain in U' without
an additional choice condition. -/
theorem finiteNumericH_candidate_finite_seed_original_budget
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (Y : Finset (AdmissibleKptNode family))
    (U : Finset (Fin N))
    (hY : (Y : Set (AdmissibleKptNode family)) ⊆
      ambientPrefixPool family (finiteNumericH K k N)
        hAvoid (U : Set (Fin N)))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (Allowed : Set Nat) :
    ∃ U' : Finset (Fin N),
      U' ⊆ U ∧ U'.card ≤ Y.card ∧
      (Y : Set (AdmissibleKptNode family)) ⊆
        ambientPrefixPool family (finiteNumericH K k N)
          hAvoid (U' : Set (Fin N)) ∧
      (kpt_originals_needing_max_old_socle_test
        family K k N hAvoid U' X
        (Y : Set (AdmissibleKptNode family))
        top R Allowed).card ≤
      Y.card + (kpt_old_actual_selected_levels
        family X top R).card := by
  classical
  have hSeeds : ∀ y : AdmissibleKptNode family, y ∈ Y →
      ∃ v : Fin N,
        v ∈ U ∧
        y ≤ (finiteNumericH K k N).kptOriginal family hAvoid v := by
    intro y hy
    obtain ⟨o,⟨v,hv,rfl⟩,hBelow⟩ := hY hy
    exact ⟨v, Finset.mem_coe.mp hv, hBelow⟩
  -- Keep the concrete physical Fin N representation explicit here.
  -- Abstract Fin A.size instantiation is mathematically equivalent,
  -- but can trigger a semireducible membership-instance mismatch
  -- after specializing A := finiteNumericH K k N.
  let Ytype := {y : AdmissibleKptNode family // y ∈ Y}
  have hChoice : ∀ yy : Ytype,
      ∃ v : Fin N,
        v ∈ U ∧
        yy.val ≤ (finiteNumericH K k N).kptOriginal
          family hAvoid v := by
    intro yy
    exact hSeeds yy.val yy.property
  let chosen : Ytype → Fin N :=
    fun yy => Classical.choose (hChoice yy)
  have hChosen (yy : Ytype) :
      chosen yy ∈ U ∧
      yy.val ≤ (finiteNumericH K k N).kptOriginal
        family hAvoid (chosen yy) :=
    Classical.choose_spec (hChoice yy)
  let U' : Finset (Fin N) := Y.attach.image chosen
  have hSub : U' ⊆ U := by
    intro v hv
    obtain ⟨yy,_hyy,rfl⟩ := Finset.mem_image.mp hv
    exact (hChosen yy).1
  have hCard : U'.card ≤ Y.card := by
    calc
      U'.card ≤ Y.attach.card := Finset.card_image_le
      _ = Y.card := Finset.card_attach
  have hY' : (Y : Set (AdmissibleKptNode family)) ⊆
      ambientPrefixPool family (finiteNumericH K k N)
        hAvoid (U' : Set (Fin N)) := by
    intro y hy
    let yy : Ytype := ⟨y,hy⟩
    have hIn : chosen yy ∈ U' := by
      apply Finset.mem_image.mpr
      exact ⟨yy,Finset.mem_attach yy,rfl⟩
    exact ⟨(finiteNumericH K k N).kptOriginal
        family hAvoid (chosen yy),
      ⟨chosen yy,Finset.mem_coe.mpr hIn,rfl⟩,
      (hChosen yy).2⟩
  have hNeedBound :=
    kpt_originals_needing_max_old_socle_test_card_le_root_add_selected
      family K k N hAvoid U' X
      (Y : Set (AdmissibleKptNode family)) top R Allowed
  refine ⟨U',hSub,hCard,hY',?_⟩
  exact hNeedBound.trans
    (Nat.add_le_add_right hCard
      (kpt_old_actual_selected_levels family X top R).card)

end Kk
