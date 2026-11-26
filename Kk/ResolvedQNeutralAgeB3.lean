import Kk.SelectedTopAgeNeutralB3
import Kk.TrackDPlannedStageRoles
import Kk.PhysicalLowerRealCutNeighbour
import Mathlib.Tactic

/-!
# Direct whole-stage B3 from resolved-Q actual base-age neutrality

English proof and independent review preceded implementation in
`docs/cut_visible_neutral_age_full_b3_english_20261124.md` and
`docs/audits/2026-11-24-cut-visible-full-b3-review-generation-zero.md`.

The entire genuine stage may contain dummy and auxiliary names. The
bounded chronological role theorem identifies only its positive eligible
names as selected TOPs; the exact failed cut-star core needs no others.
Actual full canonical base-prefix neutrality then proves the whole-stage
chosen B3 verdict directly, with no marked-output fibre or no-I2 premise.
The infinite resolved-Q constructor must still supply the displayed
ordinary base-age identity and the genuine descending stage inclusion.
-/

namespace Kk

open SuccessorTree.V10

/-- On the WHOLE genuine current-stage list, actual full selected-TOP
base-prefix neutrality derives the chosen B3 verdict for any selected
predicate, including the actual closure-selected predicate. Only the
construction's finite ordinary target list/age and chronological roles
remain inputs; no marked B3 or structural verdict is postulated. -/
theorem k4_resolvedQ_stage_B3_of_base_prefix_neutral
    (E : Nat → Nat → Bool) (k : Nat) (hK : 4 ≤ k+1)
    (N : Nat) (U : Finset (Fin N))
    (J Plan : Set Nat) (hJPlan : J ⊆ Plan)
    (role : Nat → ResolvedQBaseRole)
    (hQ : ResolvedQChronologicalAxioms role E)
    (hLoops : ∀ i, E i i = false)
    (hClique : ¬ ∃ f : Fin 4 → Nat, StrictMono f ∧
      (∀ a b : Fin 4, a ≠ b → E (f a) (f b) = true))
    (hRootDummy : ∀ v : Fin N, v ∈ U →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m →
        role j = .dummy)
    (hPlanShape : ∀ v : Fin N, v.val ∈ Plan →
      0 < (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m →
        (role j = .coded true ∧ m = k) ∨
        (∃ block : Nat, role j = .auxiliary block true))
    (b g : Nat) (hg : g < k) (hCut : hPosition k b g < N)
    (hOmitted : ResolvedQOmittedBase (role b))
    (d : Nat) (target : Fin d → Nat)
    (hLater : ∀ t, b < target t)
    (hTargetBound : ∀ t, hPosition k (target t) k < N)
    (hTargetCover : ∀ j : Nat, b < j → role j = .coded true →
      hPosition k j k < N → ∃ t : Fin d, target t = j)
    (hNeutral : baseTopPrefixCanonicalAge E 4 d b target =
      baseTopPrefixCanonicalAge E 4 d (b+1) target)
    (Full : Fin (hStageOriginals (normalizedGraphModel E) k N U J).card → Prop) :
    (selectedStagePoolPrescribedData
      (finiteNumericH (normalizedGraphModel E) k N)
      (hPosition k b g)
      (hOriginalName (hStageOriginals (normalizedGraphModel E) k N U J))
      Full).CorrectedB3 (hensonForbiddenFamily 4 (by decide)) := by
  let K := normalizedGraphModel E
  let Stage := hStageOriginals K k N U J
  let name := hOriginalName Stage
  apply k4_selectedTop_B3_of_base_prefix_neutral
    k hK E hLoops hQ.sym hClique N b g Stage.card d hg hCut
    name Full target hLater hTargetBound
  · intro v _hFull hEligible hPositive
    obtain ⟨j,m,hbj,_hgm,hm,hAddr,hEdge⟩ :=
      finiteNumericH_eligible_lower_cut_neighbour_is_higher
        E k N b g hg hCut (name v) hEligible hPositive
    obtain ⟨hCode,hTop⟩ :=
      resolvedQ_stage_omitted_positive_name_is_selected_top
        K k N U J Plan hJPlan role E hQ hRootDummy hPlanShape
        b j m hm hbj hOmitted v hAddr hEdge
    have hTopAddr : (name v).val = hPosition k j k := by
      simpa only [hTop] using hAddr
    have hBound : hPosition k j k < N := by
      rw [← hTopAddr]
      exact (name v).isLt
    obtain ⟨t,ht⟩ := hTargetCover j hbj hCode hBound
    exact ⟨t, by simpa only [ht] using hTopAddr⟩
  · exact hNeutral

#print axioms k4_resolvedQ_stage_B3_of_base_prefix_neutral

end Kk
