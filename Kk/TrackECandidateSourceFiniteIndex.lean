import Kk.NumericHExhaustiveRunIndex
import Kk.TrackECoherentFinalIndexRetention
import Mathlib.Tactic

/-!
# Track E E70: exhaustive candidate Kpt source names without assuming new run

English mathematical proof and 19 hostile checks were committed FIRST:
docs/track_e_candidate_index_no_new_run_english_audit_20261118.md

Given ONE genuine old AlgorithmRun R on X and a larger actual finite
numerical-H+ original-prefix Kpt seed family Y, both full final
sources closure_(R.I 0)(X) and closure_(R.I 0)(Y) are finite.
Finite name enumeration of the CANDIDATE new source on Y at the
OLD run's levels R.I(c+1) provides exact full source live masks.

A single literal physical old-final -> new-final node injection
preserves full dependent L+/E records and all old-live cut flags.
No already-constructed target AlgorithmRun on Y is assumed.
This supplies E69's candidate full-source indexing assumptions,
not its remaining genuine physical terminal/crossing tests.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Finiteness of the actual CANDIDATE final Kpt meet/parameter
closure on Y, computed at the level set R.I(0) of an OLD actual
run on X. No AlgorithmRun on Y is assumed here.
The bound is finite numerical-H+ ambient N, not diary-uniform. -/
theorem finiteNumericH_oldRun_candidate_finalClosure_finite
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Set (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid U)
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top) :
    (SMTree.Envelope.closure (admissibleKptSTree family)
      (R.I 0) Y).Finite := by
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  have hSeedBound :
      Y ⊆ SMTree.Envelope.levelLe
        (T := AdmissibleKptNode family) N := by
    intro z hz
    obtain ⟨o,⟨v,_hv,rfl⟩,hBelow⟩ := hY hz
    have hLevel :
        LevelTree.lev z ≤ A.freeLevel v.val := by
      exact LevelTree.level_le_of_le hBelow
    have hFree : A.freeLevel v.val ≤ v.val :=
      A.freeLevel_le v.val
    have hvN : v.val < N := v.isLt
    change LevelTree.lev z ≤ N
    omega
  exact SMTree.Envelope.closure_finite_of_bounded
    (S := admissibleKptSTree family) (R.I 0) Y N hSeedBound

/-- One finite list of true candidate new Kpt nodes enumerates
ALL old-run-tail closures closure_(R.I(c+1))(Y), with exact
per-cut physical source membership; no target new run occurs.
This includes generated meets, dependent parameters and E atoms. -/
theorem finiteNumericH_oldRun_candidate_uniform_exhaustive_source_index
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Set (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid U)
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top) :
    ∃ params : Finset (AdmissibleKptNode family),
      ∃ live : Nat → Fin params.card → Bool,
      (∀ z : AdmissibleKptNode family,
        z ∈ params ↔
          z ∈ SMTree.Envelope.closure
            (admissibleKptSTree family) (R.I 0) Y) ∧
      Function.Injective
        (fun j : Fin params.card => (params.equivFin.symm j).val) ∧
      (∀ cut : Nat, ∀ j : Fin params.card,
        live cut j = true ↔
          (params.equivFin.symm j).val ∈
            SMTree.Envelope.closure (admissibleKptSTree family)
              (R.I (cut+1)) Y) ∧
      (∀ cut : Nat, cut < top →
        ∀ z : AdmissibleKptNode family,
          z ∈ SMTree.Envelope.closure
            (admissibleKptSTree family) (R.I (cut+1)) Y ↔
          ∃ j : Fin params.card,
            (params.equivFin.symm j).val = z ∧
            live cut j = true) := by
  classical
  let Z : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family) (R.I 0) Y
  have hFinite : Z.Finite :=
    finiteNumericH_oldRun_candidate_finalClosure_finite
      family K k N hAvoid U X Y hY top R
  let params : Finset (AdmissibleKptNode family) := hFinite.toFinset
  have hExact : ∀ z : AdmissibleKptNode family,
      z ∈ params ↔ z ∈ Z := by
    intro z
    simp [params]
  let live : Nat → Fin params.card → Bool :=
    fun cut j => decide ((params.equivFin.symm j).val ∈
      SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1)) Y)
  have hPresent : ∀ cut : Nat, ∀ j : Fin params.card,
      live cut j = true ↔
        (params.equivFin.symm j).val ∈
          SMTree.Envelope.closure (admissibleKptSTree family)
            (R.I (cut+1)) Y := by
    intro cut j
    simp [live]
  refine ⟨params,live,?_,?_,hPresent,?_⟩
  · exact hExact
  · intro i j hEq
    have hPairs :
        params.equivFin.symm i = params.equivFin.symm j :=
      Subtype.ext hEq
    exact params.equivFin.symm.injective hPairs
  · intro cut hCut z
    let Zcut : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1)) Y
    have hLevels : R.I (cut+1) ⊆ R.I 0 := by
      intro m hm
      rw [R.I_eq_final_tail_of_run (cut+1) (by omega)] at hm
      exact hm.1
    have hSub : Zcut ⊆ Z :=
      envelope_closure_mono_levels
        (admissibleKptSTree family)
        (R.I (cut+1)) (R.I 0) Y hLevels
    constructor
    · intro hz
      have hzFinal : z ∈ Z := hSub hz
      have hzParams : z ∈ params := (hExact z).2 hzFinal
      let j : Fin params.card := params.equivFin ⟨z,hzParams⟩
      have hName : (params.equivFin.symm j).val = z := by
        simp [j]
      refine ⟨j,hName,?_⟩
      exact (hPresent cut j).2 (by simpa only [hName] using hz)
    · rintro ⟨j,hName,hLive⟩
      have hz : (params.equivFin.symm j).val ∈ Zcut :=
        (hPresent cut j).1 hLive
      rw [hName] at hz
      exact hz

/-- TWO finite source indices are constructed using the SAME OLD
AlgorithmRun. One single injective phi maps old final Kpt names to
identical new final Kpt nodes and preserves old pre-cut liveness,
complete old and upper L+/E records and exhaustive candidate new
physical pre-cut closure membership.

The candidate new index depends on finite numerical-H+ N; no Y-run,
uniform diary carrier or reverse source no-novelty is constructed. -/
theorem finiteNumericH_oldRun_candidate_coherent_source_index
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Set (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid U)
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid U)
    (hXY : X ⊆ Y)
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top) :
    ∃ oldParams newParams : Finset (AdmissibleKptNode family),
      ∃ oldLive : Nat → Fin oldParams.card → Bool,
      ∃ newLive : Nat → Fin newParams.card → Bool,
      ∃ φ : Fin oldParams.card → Fin newParams.card,
      Function.Injective φ ∧
      (∀ i : Fin oldParams.card,
        (newParams.equivFin.symm (φ i)).val =
          (oldParams.equivFin.symm i).val) ∧
      (∀ cut : Nat, cut < top →
        ∀ z : AdmissibleKptNode family,
          z ∈ SMTree.Envelope.closure
            (admissibleKptSTree family) (R.I (cut+1)) X ↔
          ∃ i : Fin oldParams.card,
            (oldParams.equivFin.symm i).val = z ∧
            oldLive cut i = true) ∧
      (∀ cut : Nat, cut < top →
        ∀ z : AdmissibleKptNode family,
          z ∈ SMTree.Envelope.closure
            (admissibleKptSTree family) (R.I (cut+1)) Y ↔
          ∃ j : Fin newParams.card,
            (newParams.equivFin.symm j).val = z ∧
            newLive cut j = true) ∧
      (∀ cut : Nat, cut < top →
        ∀ i : Fin oldParams.card,
          oldLive cut i = true → newLive cut (φ i) = true) ∧
      (∀ cut : Nat, cut < top →
        ∀ i : Fin oldParams.card,
          kptFullOldAtCut
            ((newParams.equivFin.symm (φ i)).val) cut =
          kptFullOldAtCut
            ((oldParams.equivFin.symm i).val) cut ∧
          kptFullUpperAtCut
            ((newParams.equivFin.symm (φ i)).val) cut =
          kptFullUpperAtCut
            ((oldParams.equivFin.symm i).val) cut) := by
  classical
  obtain ⟨oldParams,oldLive,hOldParams,hOldInj,hOldPresent,hOldExact⟩ :=
    finiteNumericH_actualRun_uniform_exhaustive_source_index
      family K k N hAvoid U X hX top R
  obtain ⟨newParams,newLive,hNewParams,hNewInj,hNewPresent,hNewExact⟩ :=
    finiteNumericH_oldRun_candidate_uniform_exhaustive_source_index
      family K k N hAvoid U X Y hY top R
  let oldNode : Fin oldParams.card → AdmissibleKptNode family :=
    fun i => (oldParams.equivFin.symm i).val
  let newNode : Fin newParams.card → AdmissibleKptNode family :=
    fun j => (newParams.equivFin.symm j).val
  have hFinalIncl :
      SMTree.Envelope.closure (admissibleKptSTree family)
          (R.I 0) X ⊆
      SMTree.Envelope.closure (admissibleKptSTree family)
          (R.I 0) Y :=
    envelope_closure_mono_seeds_and_levels
      (admissibleKptSTree family)
      (R.I 0) (R.I 0) X Y
      (by intro q hq; exact hq) hXY
  have hOldInNew (i : Fin oldParams.card) :
      oldNode i ∈ newParams := by
    have hMem : oldNode i ∈ oldParams :=
      (oldParams.equivFin.symm i).property
    have hOldFinal :
        oldNode i ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I 0) X :=
      (hOldParams (oldNode i)).mp hMem
    exact (hNewParams (oldNode i)).mpr (hFinalIncl hOldFinal)
  let φ : Fin oldParams.card → Fin newParams.card :=
    fun i => newParams.equivFin ⟨oldNode i,hOldInNew i⟩
  have hNames (i : Fin oldParams.card) :
      newNode (φ i) = oldNode i := by
    simp [newNode,φ]
  have hφInj : Function.Injective φ := by
    intro i j hij
    apply hOldInj
    calc
      oldNode i = newNode (φ i) := (hNames i).symm
      _ = newNode (φ j) := congrArg newNode hij
      _ = oldNode j := hNames j
  refine ⟨oldParams,newParams,oldLive,newLive,φ,
    hφInj,hNames,?_,?_,?_,?_⟩
  · intro cut hCut z
    exact hOldExact cut hCut z
  · intro cut hCut z
    exact hNewExact cut hCut z
  · intro cut hCut i hLive
    have hOldMember :
        oldNode i ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) X :=
      (hOldPresent cut i).mp hLive
    have hNewMember :
        oldNode i ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) Y :=
      (envelope_closure_mono_seeds_and_levels
        (admissibleKptSTree family)
        (R.I (cut+1)) (R.I (cut+1)) X Y
        (by intro q hq; exact hq) hXY) hOldMember
    apply (hNewPresent cut (φ i)).2
    change newNode (φ i) ∈ SMTree.Envelope.closure
      (admissibleKptSTree family) (R.I (cut+1)) Y
    rw [hNames i]
    exact hNewMember
  · intro cut _hCut i
    change kptFullOldAtCut (newNode (φ i)) cut =
        kptFullOldAtCut (oldNode i) cut ∧
      kptFullUpperAtCut (newNode (φ i)) cut =
        kptFullUpperAtCut (oldNode i) cut
    simp [hNames i]

end Kk
