import Kk.TrackEMaxOriginalOldTopBudget
import Mathlib.Tactic

/-!
# Track E E86: bound maximal source OLD-Kpt-prefix tests by
# the NUMBER of ACTUALLY SELECTED OLD SOURCE LEVELS, not scan height

English-first mathematical proof and adversarial checks:
docs/track_e_max_original_budget_old_selected_card_english_audit_20261121.md

E85 bounded the number of physical numerical-H+ originals that
need E79 maximal OLD Kpt prefix tests by |U|+oldTop+1, independent
of the NEW carrier N. But oldTop is a PHYSICAL coordinate and
may contain long boring numerical gaps.

For a genuine OLD AlgorithmRun R, selected R.I 0 is finite:
R.I_mem_bounds embeds it in Finset.range(oldTop+1). Let
SelectedOld be the exact Finset of these ACTUALLY selected levels.

The true FINAL physical original pool is exactly a subset of
U UNION originals at addresses selected in R.I 0. Those selected
original addresses inject into SelectedOld by their literal
physical coordinate. Consequently the number of E79 maximal
old-prefix tests is bounded by
     U.card + SelectedOld.card
regardless of N, and independent of the numerical lengths
of old boring gaps.

This remains stage-relative: neither |U| nor the number of
selected old levels is yet bounded by the fixed abstract diary
across arbitrary resolved-Q occurrences. No maximal prefix
witness existence, common labelled inverse-source orbit or
BRD theorem is asserted.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The FINITE exact set of levels selected in one genuine old
Kpt AlgorithmRun. The physical scan top is inclusive because
the actual AlgorithmRun topI contains the top itself.

No replacement of the genuine selected source-level set by
a proposed diary Plan or a graph-age shadow is made. -/
noncomputable def kpt_old_actual_selected_levels
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top) : Finset Nat := by
  classical
  exact (Finset.range (top+1)).filter (fun q => q ∈ R.I 0)

/-- The selected-level Finset contains EVERY, and ONLY,
actual old source levels q∈R.I0. The equivalence uses the
verified true AlgorithmRun inclusive oldTop membership bound;
assuming q<top would discard the genuine topI event. -/
theorem mem_kpt_old_actual_selected_levels_iff
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (q : Nat) :
    q ∈ kpt_old_actual_selected_levels family X top R ↔
      q ∈ R.I 0 := by
  classical
  simp only [kpt_old_actual_selected_levels,
    Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h
    exact h.2
  · intro hSelected
    have hBound : q ≤ top :=
      (R.I_mem_bounds 0 (Nat.zero_le top) q hSelected).2
    exact ⟨Nat.lt_succ_of_le hBound,hSelected⟩

/-- The TRUE OLD FINAL numerical-H+ physical original stage
pool has at most
  |genuine root original names U| + |actually selected OLD levels|.
The latter counts event coordinates, not their possibly long
physical span to oldTop, and is independent of new physical N.

No disjointness between U and selected original names is
assumed; cardinality union inequality remains valid. -/
theorem finiteNumericH_old_run_final_stage_originals_card_le_root_add_selected
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top) :
    (hStageOriginals K k N U (R.I 0)).card ≤
      U.card + (kpt_old_actual_selected_levels
        family X top R).card := by
  classical
  let V : Finset (Fin N) :=
    hStageOriginals K k N U (R.I 0)
  let T : Finset (Fin N) :=
    Finset.univ.filter (fun v : Fin N => v.val ∈ R.I 0)
  let Sel : Finset Nat :=
    kpt_old_actual_selected_levels family X top R
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
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ v,hSelected⟩
  have hTBound : T.card ≤ Sel.card := by
    apply Finset.card_le_card_of_injOn
      (s := T) (t := Sel) (fun v : Fin N => v.val)
    · intro v hv
      have hSelected : v.val ∈ R.I 0 :=
        (Finset.mem_filter.mp hv).2
      change v.val ∈
        kpt_old_actual_selected_levels family X top R
      exact (mem_kpt_old_actual_selected_levels_iff
        family X top R v.val).mpr hSelected
    · intro v _hv w _hw heq
      exact Fin.ext heq
  have hVCard : V.card ≤ (U ∪ T).card :=
    Finset.card_le_card hSub
  have hUnionCard : (U ∪ T).card ≤ U.card + T.card :=
    Finset.card_union_le U T
  change V.card ≤ U.card + Sel.card
  omega

/-- E86: the NUMBER of distinct physical original names whose
E79 allowed OLD-BORING new-live crossing support is nonempty
is bounded by the genuine old root-original pool cardinal
plus the number of ACTUALLY SELECTED OLD Kpt levels.

This is sharper than E85's bound by oldTop+1, independent of
arbitrary gaps between selected levels and independent of N.
It neither supplies the maximal old-prefix witnesses nor
bounds their count uniformly by the abstract diary. -/
theorem kpt_originals_needing_max_old_socle_test_card_le_root_add_selected
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
      U.card + (kpt_old_actual_selected_levels
        family X top R).card := by
  have hSub :=
    kpt_originals_needing_max_socle_subset_old_final_stage
      family K k N hAvoid U X Y top R Allowed
  have hCard := Finset.card_le_card hSub
  have hFinal :=
    finiteNumericH_old_run_final_stage_originals_card_le_root_add_selected
      family K k N U X top R
  exact hCard.trans hFinal

/-- The selected old level count is at most oldTop+1,
confirming E86 numerically strengthens E85. The extra 1
is necessary for the selected old top itself. -/
theorem kpt_old_actual_selected_levels_card_le_top_add_one
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top) :
    (kpt_old_actual_selected_levels
      family X top R).card ≤ top+1 := by
  classical
  have hSub : kpt_old_actual_selected_levels
      family X top R ⊆ Finset.range (top+1) := by
    intro q hq
    have hSelected :=
      (mem_kpt_old_actual_selected_levels_iff
        family X top R q).mp hq
    have hBound : q ≤ top :=
      (R.I_mem_bounds 0 (Nat.zero_le top) q hSelected).2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hBound)
  have hCard := Finset.card_le_card hSub
  simpa only [Finset.card_range] using hCard

end Kk
