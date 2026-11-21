import Kk.TrackGExactFactorBadCuts
import Kk.TrackGConstructTargetIndexWithoutRun
import Mathlib.Tactic

/-!
# Track G: intrinsic exact factor-Bad support, independent of finite Kpt index

English-first proof and fifteen hostile checks:
docs/track_g_factor_bad_index_independence_english_audit_20261121.md

The exact old-factor compatible predicate is a statement about the
COMPLETE physical Kpt source C, independently of its finite names.
An exact finite source index is just another presentation of C;
hence the exact factor-Bad Finset of G406 is invariant under
arbitrary changes of indices, even different sizes and duplicates.

For a finite numerical-H+ source, the genuine RX selected tails
and G378 yield a complete exact candidate target index WITHOUT
an input AlgorithmRun on Y. The G406 exact Bad=empty iff same-I,
same-TOTAL-F target-run equivalence then applies. There is no
diary-uniform source bound, cross-occurrence cut-coordinate map,
labelled inverse-source orbit or Kk-free BRD characterization.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

/-- Complete physical target Kpt old-factor compatibility,
without choosing any enumeration of the target source.

The three clauses record actual terminal I1, same-component
meet I2 and the unique original total F-step factor's
full dependent Kpt ancestor action. The factor clause is
formulated with a universal quantifier over TOTAL MMaps;
at a genuinely old-boring cut the factor exists and is unique. -/
def KptPhysicalOldFactorCompatibleAt
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Z : Set (AdmissibleKptNode family))
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (cut : Nat) : Prop :=
  (∀ z : AdmissibleKptNode family,
    z ∈ Z → LevelTree.lev z ≠ cut) ∧
  (∀ z : AdmissibleKptNode family, z ∈ Z →
    ∀ w : AdmissibleKptNode family, w ∈ Z →
      ¬ (SMTree.Envelope.SameComponent z w ∧
        LevelTree.lev (LevelTree.meet z w) = cut)) ∧
  (∀ D : MMap (normalizedKptSMTree family),
    RX.F cut =
      MMap.comp (normalizedKptSMTree family) (RX.F (cut+1)) D →
    ∀ (z : AdmissibleKptNode family), z ∈ Z →
      ∀ (hCross : cut < LevelTree.lev z),
        D (LevelTree.ancestor z cut (Nat.le_of_lt hCross)) =
          LevelTree.ancestor z (cut+1)
            (Nat.succ_le_iff.mpr hCross))

/-- An independently exact finite live-node presentation of the
complete target source has exactly the SAME old-factor compatibility
test as the physical predicate. Injectivity of finite names is
not needed, and there is no target AlgorithmRun assumption. -/
theorem kptIndexedOldFactorCompatibleAt_iff_physical
    {db du dd Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Z : Set (AdmissibleKptNode family))
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (node : Fin Q → AdmissibleKptNode family)
    (live : Nat → Fin Q → Bool)
    (cut : Nat)
    (hExact : ∀ z : AdmissibleKptNode family,
      z ∈ Z ↔ ∃ j : Fin Q, node j = z ∧ live cut j = true) :
    KptIndexedOldFactorCompatibleAt family X top RX
        node live cut ↔
      KptPhysicalOldFactorCompatibleAt family X Z top RX cut := by
  constructor
  · rintro ⟨hNoI1,hNoI2,hFactor⟩
    refine ⟨?_,?_,?_⟩
    · intro z hz hLev
      obtain ⟨j,hNode,hLive⟩ := (hExact z).mp hz
      exact (hNoI1 j hLive) (by
        simpa only [hNode] using hLev)
    · intro z hz w hw hMeet
      obtain ⟨j,hNodeZ,hLiveZ⟩ := (hExact z).mp hz
      obtain ⟨k,hNodeW,hLiveW⟩ := (hExact w).mp hw
      apply (hNoI2 j k hLiveZ hLiveW)
      simpa only [hNodeZ,hNodeW] using hMeet
    · intro D hEq z hz hCross
      obtain ⟨j,hNode,hLive⟩ := (hExact z).mp hz
      have hCrossJ : cut < LevelTree.lev (node j) := by
        simpa only [hNode] using hCross
      have hAt := hFactor D hEq j hLive hCrossJ
      simpa only [hNode] using hAt
  · rintro ⟨hNoI1,hNoI2,hFactor⟩
    refine ⟨?_,?_,?_⟩
    · intro j hLive hLev
      have hj : node j ∈ Z :=
        (hExact (node j)).mpr ⟨j,rfl,hLive⟩
      exact hNoI1 (node j) hj hLev
    · intro j k hLiveJ hLiveK hMeet
      have hj : node j ∈ Z :=
        (hExact (node j)).mpr ⟨j,rfl,hLiveJ⟩
      have hk : node k ∈ Z :=
        (hExact (node k)).mpr ⟨k,rfl,hLiveK⟩
      exact hNoI2 (node j) hj (node k) hk hMeet
    · intro D hEq j hLive hCross
      have hj : node j ∈ Z :=
        (hExact (node j)).mpr ⟨j,rfl,hLive⟩
      exact hFactor D hEq (node j) hj hCross

/-- The exact old-factor Bad Finset is INTRINSIC: any two
independently exhaustive finite target source indexes, including
different sizes and repeated names, compute the same literal
set of physical old-boring cut COORDINATES.

This is stronger than just equivalent emptiness; it does not
give a diary-uniform upper bound on the cardinality. -/
theorem kptExactOldFactorBadCuts_index_independent
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (node₁ : Fin P → AdmissibleKptNode family)
    (node₂ : Fin Q → AdmissibleKptNode family)
    (live₁ : Nat → Fin P → Bool)
    (live₂ : Nat → Fin Q → Bool)
    (hExact₁ : ∀ cut : Nat, cut < top →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (RX.I (cut+1)) Y ↔
        ∃ j : Fin P, node₁ j = z ∧ live₁ cut j = true)
    (hExact₂ : ∀ cut : Nat, cut < top →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (RX.I (cut+1)) Y ↔
        ∃ j : Fin Q, node₂ j = z ∧ live₂ cut j = true) :
    kptExactOldFactorBadCuts family X top RX node₁ live₁ =
      kptExactOldFactorBadCuts family X top RX node₂ live₂ := by
  classical
  apply Finset.ext
  intro cut
  constructor
  · intro hBad
    obtain ⟨hCut,hOldBoring,hNotCompat⟩ :=
      (mem_kptExactOldFactorBadCuts
        family X top RX node₁ live₁ cut).mp hBad
    refine (mem_kptExactOldFactorBadCuts
      family X top RX node₂ live₂ cut).mpr
      ⟨hCut,hOldBoring,?_⟩
    intro hCompat₂
    have hPhysical :=
      (kptIndexedOldFactorCompatibleAt_iff_physical
        family X
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) Y)
        top RX node₂ live₂ cut (hExact₂ cut hCut)).mp hCompat₂
    exact hNotCompat
      ((kptIndexedOldFactorCompatibleAt_iff_physical
        family X
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) Y)
        top RX node₁ live₁ cut (hExact₁ cut hCut)).mpr hPhysical)
  · intro hBad
    obtain ⟨hCut,hOldBoring,hNotCompat⟩ :=
      (mem_kptExactOldFactorBadCuts
        family X top RX node₂ live₂ cut).mp hBad
    refine (mem_kptExactOldFactorBadCuts
      family X top RX node₁ live₁ cut).mpr
      ⟨hCut,hOldBoring,?_⟩
    intro hCompat₁
    have hPhysical :=
      (kptIndexedOldFactorCompatibleAt_iff_physical
        family X
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) Y)
        top RX node₁ live₁ cut (hExact₁ cut hCut)).mp hCompat₁
    exact hNotCompat
      ((kptIndexedOldFactorCompatibleAt_iff_physical
        family X
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) Y)
        top RX node₂ live₂ cut (hExact₂ cut hCut)).mpr hPhysical)

/-- A real finite numerical-H+ target source pool gives a FULL
exact physical target Kpt index along an arbitrary actual old
run's selected I tails, with NO input target AlgorithmRun.

For this constructed index the exact intrinsic factor Bad Finset
is EMPTY iff a genuine target run with identical selected I and
TOTAL MMap-valued F exists. This does not make the Bad test
algorithmically decidable or uniformly bounded across N. -/
theorem finiteNumericH_construct_target_index_exact_factorBad_iff_transport
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
