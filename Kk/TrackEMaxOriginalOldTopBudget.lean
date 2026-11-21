import Kk.TrackEOldSocleOriginalMaxFrontier
import Mathlib.Tactic

/-!
# Track E E85: at most |U|+oldTop+1 original-prefix maximal tests

English-FIRST proof and 24 hostile checks committed before Lean:
docs/track_e_max_original_budget_old_run_top_english_audit_20261121.md

E79's naive ≤N maximal old-socle certificates count ALL physical
numerical-H+ originals in Fin N. But a physical original v actually
needs such a maximal test only if it represents a genuine NEW-LIVE
crossing source at some OLD-BORING source cut.

The checked selected-stage original representation places every
such v in the actual stage original pool
hStageOriginals K k N U (R.I(cut+1)), which is contained in
the ONE OLD FINAL pool hStageOriginals K k N U (R.I 0).

The genuine AlgorithmRun's R.I_mem_bounds gives every old selected
level q∈R.I0 the INCLUSIVE bound q≤oldTop. Hence the total number
of physical originals in the final pool -- and thus the number
of original-maximal OLD-Kpt prefix tests -- is at most
  |U| + (oldTop+1),
independently of the NEW physical carrier size N.

This is a substantive stage-relative finite bound, not yet
a uniform bound in an ABSTRACT diary: oldTop and |U| still need
control across resolved diary occurrences, and the maximal old
prefix witnesses themselves remain unproved.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A physical numerical-H+ original-stage pool is monotone
in its SELECTED numerical parameter-level set. The root original
pool U and physical carrier N remain fixed. No Kpt source closure
or AlgorithmRun is required for this combinatorial statement. -/
theorem finiteNumericH_stageOriginals_mono_levels
    {db du dd : Nat}
    (K : AgeTestModel db du dd) (k N : Nat)
    (U : Finset (Fin N))
    (I J : Set Nat) (hIJ : I ⊆ J) :
    hStageOriginals K k N U I ⊆
      hStageOriginals K k N U J := by
  classical
  intro v hv
  have hvOr :
      v ∈ U ∨
        (v.val ∈ I ∧
          0 < (finiteNumericH K k N).freeLevel v.val) := by
    simpa only [hStageOriginals, Finset.mem_filter,
      Finset.mem_univ, true_and] using hv
  have hvJ :
      v ∈ U ∨
        (v.val ∈ J ∧
          0 < (finiteNumericH K k N).freeLevel v.val) := by
    rcases hvOr with hRoot | ⟨hLevel,hPos⟩
    · exact Or.inl hRoot
    · exact Or.inr ⟨hIJ hLevel,hPos⟩
  simpa only [hStageOriginals, Finset.mem_filter,
    Finset.mem_univ, true_and] using hvJ

/-- The TRUE physical numerical-H+ originals for which E79
has a NONEMPTY allowed old-boring/new-live crossing support.
One genuine physical original is counted ONCE regardless of
how many new auxiliary meet/parameter nodes it represents
or how many eligible cuts lie below its maximal cut.

Classical decidability is only used to turn the finite
predicate into a Finset; no target AlgorithmRun is assumed. -/
noncomputable def kpt_originals_needing_max_old_socle_test
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (Allowed : Set Nat) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun v =>
    (kpt_actual_original_socle_allowed_cuts
      family K k N hAvoid U X Y top R Allowed v).Nonempty)

/-- Exact membership in the genuine per-original OLD-prefix
maximal-test support. No dummy, even-real or odd-safe class
hypothesis is needed; Allowed may have arbitrary gaps. -/
theorem mem_kpt_originals_needing_max_old_socle_test
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (Allowed : Set Nat) (v : Fin N) :
    v ∈ kpt_originals_needing_max_old_socle_test
      family K k N hAvoid U X Y top R Allowed ↔
    (kpt_actual_original_socle_allowed_cuts
      family K k N hAvoid U X Y top R Allowed v).Nonempty := by
  classical
  simp only [kpt_originals_needing_max_old_socle_test,
    Finset.mem_filter, Finset.mem_univ, true_and]

/-- Every original physical address that actually needs an E79
maximal OLD-Kpt prefix test already lies in the SINGLE fixed
FINAL original-stage pool of the genuine OLD AlgorithmRun R,
computed with its selected level set R.I 0.

No false claim that this original itself is OLD-LIVE or
that its required prefix witness has been constructed. -/
theorem kpt_originals_needing_max_socle_subset_old_final_stage
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (Allowed : Set Nat) :
    kpt_originals_needing_max_old_socle_test
      family K k N hAvoid U X Y top R Allowed ⊆
    hStageOriginals K k N U (R.I 0) := by
  classical
  intro v hv
  have hNonempty :=
    (mem_kpt_originals_needing_max_old_socle_test
      family K k N hAvoid U X Y top R Allowed v).mp hv
  obtain ⟨cut,hCut⟩ := hNonempty
  have hBase :
      cut ∈ kpt_candidate_original_boring_crossing_cuts
        family K k N hAvoid U X Y top R v :=
    ((mem_kpt_actual_original_socle_allowed_cuts
      family K k N hAvoid U X Y top R Allowed v cut).mp hCut).1
  have hData :=
    (mem_kpt_candidate_original_boring_crossing_cuts
      family K k N hAvoid U X Y top R v cut).mp hBase
  have hCutTop : cut < top := hData.1
  have hStage :
      v ∈ hStageOriginals K k N U (R.I (cut+1)) :=
    hData.2.2.1
  have hLevels : R.I (cut+1) ⊆ R.I 0 := by
    intro q hq
    rw [R.I_eq_final_tail_of_run (cut+1) (by omega)] at hq
    exact hq.1
  exact finiteNumericH_stageOriginals_mono_levels
    K k N U (R.I (cut+1)) (R.I 0) hLevels hStage

/-- The TRUE old FINAL physical original-stage pool has at most
|U|+(oldTop+1) distinct original addresses, independently of N.

The inclusive +1 is essential: genuine AlgorithmRuns have
topI={top}, so selected levels may actually contain top.
Each selected original outside U has its literal numerical
coordinate in R.I 0, hence at most top; this bounds it via
an injection into Finset.range (top+1). -/
theorem finiteNumericH_old_run_final_stage_originals_card_le_root_add_top
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top) :
    (hStageOriginals K k N U (R.I 0)).card ≤
      U.card + (top+1) := by
  classical
  let V : Finset (Fin N) :=
    hStageOriginals K k N U (R.I 0)
  let T : Finset (Fin N) :=
    Finset.univ.filter (fun v : Fin N => v.val ∈ R.I 0)
  have hSub : V ⊆ U ∪ T := by
    intro v hv
    have hvOr :
        v ∈ U ∨
          (v.val ∈ R.I 0 ∧
            0 < (finiteNumericH K k N).freeLevel v.val) := by
      simpa only [V, hStageOriginals, Finset.mem_filter,
        Finset.mem_univ, true_and] using hv
    rcases hvOr with hRoot | ⟨hSelected,_hFree⟩
    · exact Finset.mem_union.mpr (Or.inl hRoot)
    · apply Finset.mem_union.mpr
      right
      exact (Finset.mem_filter.mpr
        ⟨Finset.mem_univ v,hSelected⟩)
  have hTBound : T.card ≤ top+1 := by
    apply Finset.card_le_card_of_injOn
      (s := T) (t := Finset.range (top+1))
      (fun v : Fin N => v.val)
    · intro v hv
      have hSelected : v.val ∈ R.I 0 :=
        (Finset.mem_filter.mp hv).2
      have hLe : v.val ≤ top :=
        (R.I_mem_bounds 0 (Nat.zero_le top) v.val hSelected).2
      exact Finset.mem_range.mpr (by omega)
    · intro v _hv w _hw heq
      exact Fin.ext heq
  have hVCard : V.card ≤ (U ∪ T).card :=
    Finset.card_le_card hSub
  have hUnionCard : (U ∪ T).card ≤ U.card + T.card :=
    Finset.card_union_le U T
  change V.card ≤ U.card + (top+1)
  omega

/-- E85: the number of different maximal OLD Kpt prefix witness
obligations for the ENTIRE E79 support (over arbitrary Allowed
source cuts) is at most |U|+oldTop+1, regardless of how large
the later physical numerical-H+ carrier N becomes.

This controls the NUMBER of physically distinct tests, not
whether their required old-live witnesses actually exist,
nor the length of a sequence of novel bad cuts. It is
stage-relative and not yet uniform in an abstract diary. -/
theorem kpt_originals_needing_max_old_socle_test_card_le_root_add_top
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (Allowed : Set Nat) :
    (kpt_originals_needing_max_old_socle_test
      family K k N hAvoid U X Y top R Allowed).card ≤
      U.card + (top+1) := by
  have hSub :=
    kpt_originals_needing_max_socle_subset_old_final_stage
      family K k N hAvoid U X Y top R Allowed
  have hCard :=
    Finset.card_le_card hSub
  have hFinal :=
    finiteNumericH_old_run_final_stage_originals_card_le_root_add_top
      family K k N U X top R
  exact hCard.trans hFinal

end Kk
