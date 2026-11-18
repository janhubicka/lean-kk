import Kk.NumericHExhaustiveRunIndex
import Kk.TrackGEmptyCanonicalBadCutsRunTransfer
import Mathlib.Tactic

/-!
# Track G: construct a complete finite Kpt target source index WITHOUT
# first assuming an AlgorithmRun on the target seeds.

English proof and fifteen adversarial checks were committed FIRST:
docs/track_g_construct_target_finite_index_without_run_english_audit_20261118.md

An arbitrary family I of selected levels whose pre-cut tails are
contained in I(0), combined with genuine physically represented
seeds Y in ONE finite numerical-H+ original prefix, has ONE finite
exhaustive source-node index for every closure(S,I(cut+1),Y).
This reuses the checked physical level bound and generic
closure_finite_of_bounded, independently of an actual Y-run.

For one actual old X-run and nested X⊆Y represented in that same
finite H+ prefix, construct both full finite indices without
assuming any Y-run; empty canonical physical old-boring Bad
support then implies existence of a genuine Y-run with literally
the same selected I and TOTAL monoid map F functions by G371.

No bound independent of the physical finite carrier size, no
executable diary-uniform classifier, no common labelled orbit
and no exact Kk-free BRD theorem is claimed.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

/-- A genuinely finite numerical-H+ represented Kpt seed pool Y
has a single exhaustive finite source index for ANY given family
I of level sets whose pre-cut tails lie in I 0.

The source I need not arise from an AlgorithmRun on Y.
All actual meet/parameter Kpt nodes are included, not
just selected original graph vertices. -/
theorem finiteNumericH_any_I_tails_uniform_Kpt_source_index
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Set (Fin N))
    (Y : Set (AdmissibleKptNode family))
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid U)
    (I : Nat → Set Nat) (top : Nat)
    (hTail : ∀ cut : Nat, cut < top → I (cut+1) ⊆ I 0) :
    ∃ params : Finset (AdmissibleKptNode family),
      ∃ live : Nat → Fin params.card → Bool,
        (∀ z : AdmissibleKptNode family,
          z ∈ params ↔
            z ∈ SMTree.Envelope.closure
              (admissibleKptSTree family) (I 0) Y) ∧
        (∀ cut : Nat, cut < top →
          ∀ z : AdmissibleKptNode family,
            z ∈ SMTree.Envelope.closure
              (admissibleKptSTree family) (I (cut+1)) Y ↔
            ∃ j : Fin params.card,
              (params.equivFin.symm j).val = z ∧
              live cut j = true) := by
  classical
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  have hSeedBound :
      Y ⊆ SMTree.Envelope.levelLe
        (T := AdmissibleKptNode family) N := by
    intro z hz
    obtain ⟨o,⟨v,_hv,rfl⟩,hBelow⟩ := hY hz
    have hLevel :
        LevelTree.lev z ≤ A.freeLevel v.val := by
      have h := LevelTree.level_le_of_le hBelow
      exact h
    have hFree : A.freeLevel v.val ≤ v.val :=
      A.freeLevel_le v.val
    have hvN : v.val < N := v.isLt
    change LevelTree.lev z ≤ N
    omega
  let Z : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family) (I 0) Y
  have hFinite : Z.Finite :=
    SMTree.Envelope.closure_finite_of_bounded
      (S := admissibleKptSTree family) (I 0) Y N hSeedBound
  let params : Finset (AdmissibleKptNode family) := hFinite.toFinset
  have hExact : ∀ z : AdmissibleKptNode family,
      z ∈ params ↔ z ∈ Z := by
    intro z
    simp [params]
  let live : Nat → Fin params.card → Bool :=
    fun cut j => decide ((params.equivFin.symm j).val ∈
      SMTree.Envelope.closure (admissibleKptSTree family)
        (I (cut+1)) Y)
  have hLive : ∀ cut : Nat, ∀ j : Fin params.card,
      live cut j = true ↔
        (params.equivFin.symm j).val ∈
          SMTree.Envelope.closure (admissibleKptSTree family)
            (I (cut+1)) Y := by
    intro cut j
    simp [live]
  refine ⟨params, live, hExact, ?_⟩
  intro cut hCut z
  let Zcut : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family) (I (cut+1)) Y
  have hSub : Zcut ⊆ Z :=
    envelope_closure_mono_levels
      (admissibleKptSTree family)
      (I (cut+1)) (I 0) Y (hTail cut hCut)
  constructor
  · intro hz
    have hzFinal : z ∈ Z := hSub hz
    have hzParams : z ∈ params := (hExact z).2 hzFinal
    let j : Fin params.card := params.equivFin ⟨z,hzParams⟩
    have hName : (params.equivFin.symm j).val = z := by
      simp [j]
    refine ⟨j,hName,?_⟩
    exact (hLive cut j).2 (by simpa only [hName] using hz)
  · rintro ⟨j,hName,hActive⟩
    have hz : (params.equivFin.symm j).val ∈ Zcut :=
      (hLive cut j).1 hActive
    rw [hName] at hz
    exact hz

/-- A real finite numerical-H+ old AlgorithmRun on X and a bounded
physically represented extension X⊆Y are enough to CONSTRUCT
independent complete exact source indices for BOTH RX.I-tail
families, without assuming any Y-run.

If the E54 minimal canonical physical Bad Finset of those indexed
sources is EMPTY, G371 constructs a true Y-run with the SAME
selected I and total MMap-valued F functions as RX.

This is conditional on EMPTY Bad. The finite index sizes may
depend on the numerical-H+ carrier N, not just the diary. -/
theorem finiteNumericH_construct_full_indices_and_transport_if_zero_Bad
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Set (Fin N))
    (X Y : Set (AdmissibleKptNode family)) (hXY : X ⊆ Y)
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid U)
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top) :
    ∃ oldParams : Finset (AdmissibleKptNode family),
      ∃ oldLive : Nat → Fin oldParams.card → Bool,
        ∃ newParams : Finset (AdmissibleKptNode family),
          ∃ newLive : Nat → Fin newParams.card → Bool,
            (∀ cut : Nat, cut < top →
              ∀ z : AdmissibleKptNode family,
                z ∈ SMTree.Envelope.closure
                  (admissibleKptSTree family) (RX.I (cut+1)) X ↔
                ∃ i : Fin oldParams.card,
                  (oldParams.equivFin.symm i).val = z ∧
                  oldLive cut i = true) ∧
            (∀ cut : Nat, cut < top →
              ∀ z : AdmissibleKptNode family,
                z ∈ SMTree.Envelope.closure
                  (admissibleKptSTree family) (RX.I (cut+1)) Y ↔
                ∃ j : Fin newParams.card,
                  (newParams.equivFin.symm j).val = z ∧
                  newLive cut j = true) ∧
            (kptCanonicalOffPlanBadCuts family RX.I top
              (fun i : Fin oldParams.card =>
                (oldParams.equivFin.symm i).val)
              (fun j : Fin newParams.card =>
                (newParams.equivFin.symm j).val)
              oldLive newLive = ∅ →
              ∃ RY : SMTree.Envelope.AlgorithmRun
                  (normalizedKptSMTree family) Y top,
                RY.I = RX.I ∧ RY.F = RX.F) := by
  classical
  have hX : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid U :=
    hXY.trans hY
  obtain ⟨oldParams, oldLive, _hOldFinal, _hOldInj,
      _hOldLive, hOldExact⟩ :=
    finiteNumericH_actualRun_uniform_exhaustive_source_index
      family K k N hAvoid U X hX top RX
  have hTail :
      ∀ cut : Nat, cut < top →
        RX.I (cut+1) ⊆ RX.I 0 := by
    intro cut hCut q hq
    rw [RX.I_eq_final_tail_of_run (cut+1) (by omega)] at hq
    exact hq.1
  obtain ⟨newParams, newLive, _hNewFinal, hNewExact⟩ :=
    finiteNumericH_any_I_tails_uniform_Kpt_source_index
      family K k N hAvoid U Y hY RX.I top hTail
  refine ⟨oldParams, oldLive, newParams, newLive,
    hOldExact, hNewExact, ?_⟩
  intro hBadEmpty
  exact kpt_wholeRun_transport_of_empty_canonical_BadCuts
    family X Y hXY top RX
    (fun i : Fin oldParams.card => (oldParams.equivFin.symm i).val)
    (fun j : Fin newParams.card => (newParams.equivFin.symm j).val)
    oldLive newLive hOldExact hNewExact hBadEmpty

end Kk
