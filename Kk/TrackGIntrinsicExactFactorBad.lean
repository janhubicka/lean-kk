import Kk.TrackGExactFactorBadCuts
import Kk.TrackGConstructTargetIndexWithoutRun
import Mathlib.Tactic

/-!
# Track G: the exact factor-Bad set is physically intrinsic and the
# finite Henson target index needs no input target run.

English proof and eighteen adversarial checks committed BEFORE Lean:
docs/track_g_intrinsic_factor_bad_finite_stage_english_audit_20261120.md

G406 proves that for X ⊆ Y, one actual RX, and a single EXHAUSTIVE
finite index of the complete target closure on RX.I tails, the old
total-factor Bad Finset is empty IFF one actual Y AlgorithmRun
with the same I and TOTAL F exists.

This module establishes the stronger independence of that EXACT
Bad set from ANY enumeration of the same physical candidate source
and produces the target index in one genuine finite numerical-H+
stage without any target run.

The source data retain actual Kpt nodes, auxiliary E and negative L;
this is not an executable monoid-search procedure, a diary-uniform
event budget, cross-occurrence cut reindexing or a BRD theorem.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

/-- An intrinsic one-cut physical source predicate equivalent to
the finite Kpt old-factor compatibility test under exact indexing.

The entire candidate target source uses the OLD actual run's
selected I tail, not an assumed second run. This definition has
NO finite name enumeration at all. -/
def KptPhysicalOldFactorCompatibleAt
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (cut : Nat) : Prop :=
  (¬ ∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (RX.I (cut+1)) Y ∧
      LevelTree.lev z = cut) ∧
  (¬ ∃ a : AdmissibleKptNode family,
      a ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (RX.I (cut+1)) Y ∧
      ∃ b : AdmissibleKptNode family,
        b ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (RX.I (cut+1)) Y ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) ∧
  (∀ D : MMap (normalizedKptSMTree family),
      RX.F cut = MMap.comp (normalizedKptSMTree family)
        (RX.F (cut+1)) D →
      ∀ ⦃z : AdmissibleKptNode family⦄,
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (RX.I (cut+1)) Y →
        ∀ (hCross : cut < LevelTree.lev z),
          D (LevelTree.ancestor z cut (Nat.le_of_lt hCross)) =
            LevelTree.ancestor z (cut+1)
              (Nat.succ_le_iff.mpr hCross))

/-- An independently EXACT finite index of the complete candidate
target Kpt source represents the intrinsic physical terminal,
same-component meet and unique old-total-factor crossing conditions.

No index injectivity, source inclusion, run on target Y or
no-I2 hypothesis is needed for this one-cut equivalence. -/
theorem kptIndexedOldFactorCompatibleAt_iff_physical
    {db du dd Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (newNode : Fin Q → AdmissibleKptNode family)
    (newLive : Nat → Fin Q → Bool)
    (cut : Nat)
    (hExact : ∀ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (RX.I (cut+1)) Y ↔
      ∃ j : Fin Q, newNode j = z ∧ newLive cut j = true) :
    KptIndexedOldFactorCompatibleAt
      family X top RX newNode newLive cut ↔
    KptPhysicalOldFactorCompatibleAt family X Y top RX cut := by
  constructor
  · rintro ⟨hTerminal,hMeet,hFactor⟩
    refine ⟨?_,?_,?_⟩
    · rintro ⟨z,hz,hLev⟩
      obtain ⟨j,hName,hLive⟩ := (hExact z).mp hz
      exact (hTerminal j hLive)
        (by simpa only [hName] using hLev)
    · rintro ⟨a,ha,b,hb,hSame,hLev⟩
      obtain ⟨j,hJa,hJLive⟩ := (hExact a).mp ha
      obtain ⟨k,hKb,hKLive⟩ := (hExact b).mp hb
      apply (hMeet j k hJLive hKLive)
      constructor
      · simpa only [hJa,hKb] using hSame
      · simpa only [hJa,hKb] using hLev
    · intro D hFD z hz hCross
      obtain ⟨j,hName,hLive⟩ := (hExact z).mp hz
      have hCrossJ : cut < LevelTree.lev (newNode j) := by
        simpa only [hName] using hCross
      have hAt := hFactor D hFD j hLive hCrossJ
      simpa only [hName] using hAt
  · rintro ⟨hTerminal,hMeet,hFactor⟩
    refine ⟨?_,?_,?_⟩
    · intro j hLive hLev
      have hj :
          newNode j ∈ SMTree.Envelope.closure
            (admissibleKptSTree family) (RX.I (cut+1)) Y :=
        (hExact (newNode j)).mpr ⟨j,rfl,hLive⟩
      exact hTerminal ⟨newNode j,hj,hLev⟩
    · intro j k hjLive hkLive hMeetData
      have hj :
          newNode j ∈ SMTree.Envelope.closure
            (admissibleKptSTree family) (RX.I (cut+1)) Y :=
        (hExact (newNode j)).mpr ⟨j,rfl,hjLive⟩
      have hk :
          newNode k ∈ SMTree.Envelope.closure
            (admissibleKptSTree family) (RX.I (cut+1)) Y :=
        (hExact (newNode k)).mpr ⟨k,rfl,hkLive⟩
      exact hMeet ⟨newNode j,hj,newNode k,hk,
        hMeetData.1,hMeetData.2⟩
    · intro D hFD j hLive hCross
      have hj :
          newNode j ∈ SMTree.Envelope.closure
            (admissibleKptSTree family) (RX.I (cut+1)) Y :=
        (hExact (newNode j)).mpr ⟨j,rfl,hLive⟩
      exact hFactor D hFD hj hCross

/-- The canonical exact old-factor Bad-cut Finset is independent of
EVERY choice of finite exhaustive target Kpt source indices,
including index cardinality, repetitions or name ordering.

This asserts equality of the WHOLE finite Bad support, not just
equivalence of emptiness. -/
theorem kptExactOldFactorBadCuts_index_independent
    {db du dd Q R : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (node₁ : Fin Q → AdmissibleKptNode family)
    (node₂ : Fin R → AdmissibleKptNode family)
    (live₁ : Nat → Fin Q → Bool)
    (live₂ : Nat → Fin R → Bool)
    (hExact₁ : ∀ cut : Nat, cut < top →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (RX.I (cut+1)) Y ↔
        ∃ j : Fin Q, node₁ j = z ∧ live₁ cut j = true)
    (hExact₂ : ∀ cut : Nat, cut < top →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (RX.I (cut+1)) Y ↔
        ∃ j : Fin R, node₂ j = z ∧ live₂ cut j = true) :
    kptExactOldFactorBadCuts family X top RX node₁ live₁ =
      kptExactOldFactorBadCuts family X top RX node₂ live₂ := by
  apply Finset.ext
  intro cut
  by_cases hCut : cut < top
  · have hEq :
        KptIndexedOldFactorCompatibleAt
          family X top RX node₁ live₁ cut ↔
        KptIndexedOldFactorCompatibleAt
          family X top RX node₂ live₂ cut :=
      (kptIndexedOldFactorCompatibleAt_iff_physical
        family X Y top RX node₁ live₁ cut (hExact₁ cut hCut)).trans
      (kptIndexedOldFactorCompatibleAt_iff_physical
        family X Y top RX node₂ live₂ cut (hExact₂ cut hCut)).symm
    constructor
    · intro hMem
      obtain ⟨_hOldCut,hBoring,hNot⟩ :=
        (mem_kptExactOldFactorBadCuts
          family X top RX node₁ live₁ cut).mp hMem
      apply (mem_kptExactOldFactorBadCuts
        family X top RX node₂ live₂ cut).mpr
      exact ⟨hCut,hBoring,fun hGood => hNot (hEq.mpr hGood)⟩
    · intro hMem
      obtain ⟨_hOldCut,hBoring,hNot⟩ :=
        (mem_kptExactOldFactorBadCuts
          family X top RX node₂ live₂ cut).mp hMem
      apply (mem_kptExactOldFactorBadCuts
        family X top RX node₁ live₁ cut).mpr
      exact ⟨hCut,hBoring,fun hGood => hNot (hEq.mp hGood)⟩
  · constructor
    · intro hMem
      exact False.elim (hCut
        ((mem_kptExactOldFactorBadCuts
          family X top RX node₁ live₁ cut).mp hMem).1)
    · intro hMem
      exact False.elim (hCut
        ((mem_kptExactOldFactorBadCuts
          family X top RX node₂ live₂ cut).mp hMem).1)

/-- In one finite actual numerical-H+ source stage, an actual old
RX and physical target seeds Y are enough to construct one EXACT
finite target Kpt index on ALL RX.I tails without any Y run.
For that resulting finite index the exact factor-Bad set is empty
IFF a genuine target run with the SAME I and TOTAL F exists.

No OLD finite index is needed, and index independence (above)
makes the exact Bad support physically intrinsic. The finite
carrier bound depends on N, not only on a proposed diary. -/
theorem finiteNumericH_construct_target_exact_factor_Bad_iff_transport
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Set (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid U)
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top) :
    ∃ params : Finset (AdmissibleKptNode family),
      ∃ live : Nat → Fin params.card → Bool,
        (∀ cut : Nat, cut < top →
          ∀ z : AdmissibleKptNode family,
            z ∈ SMTree.Envelope.closure
              (admissibleKptSTree family) (RX.I (cut+1)) Y ↔
            ∃ j : Fin params.card,
              (params.equivFin.symm j).val = z ∧
              live cut j = true) ∧
        (kptExactOldFactorBadCuts family X top RX
          (fun j : Fin params.card => (params.equivFin.symm j).val)
          live = ∅ ↔
         ∃ RY : SMTree.Envelope.AlgorithmRun
              (normalizedKptSMTree family) Y top,
            RY.I = RX.I ∧ RY.F = RX.F) := by
  classical
  have hTail :
      ∀ cut : Nat, cut < top →
        RX.I (cut+1) ⊆ RX.I 0 := by
    intro cut hCut q hq
    rw [RX.I_eq_final_tail_of_run (cut+1) (by omega)] at hq
    exact hq.1
  obtain ⟨params,live,_hFinal,hExact⟩ :=
    finiteNumericH_any_I_tails_uniform_Kpt_source_index
      family K k N hAvoid U Y hY RX.I top hTail
  refine ⟨params,live,hExact,?_⟩
  exact kpt_exact_factor_BadCuts_empty_iff_wholeRun_transport
    family X Y hXY top RX
    (fun j : Fin params.card => (params.equivFin.symm j).val)
    live hExact

end Kk
