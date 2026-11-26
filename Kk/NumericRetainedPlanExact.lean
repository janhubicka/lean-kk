import Kk.NumericRetainedPlan
import Kk.GenerationZeroStructural
import Kk.TopGenerationStageCoherence
import Kk.ResolvedQNeutralAgeB3
import Kk.TrackDZeroStageActualRunSkip
import Kk.PhysicalCanonicalSortTransport
import SuccessorTree.V10.KptE1EnvelopeIntegration
import Mathlib.Tactic

/-!
# Exact finite retained levels from ordinary resolved-Q invariants

English proof and independent review were committed before this source:
`docs/numeric_retained_plan_exact_closure_english_20261124.md` and
`docs/audits/2026-11-24-exact-finite-plan-adversarial-review.md`.

The finite Plan is constructed from retained real coordinates and actual
free levels. Ordinary chronological roles, selected no-split, and actual
full canonical reference-age neutrality imply every descending off-plan
skip for the enlarged family of all planned cap ancestors. The proof covers
odd cuts, TOP cuts, dummy and selected-code lower cuts, and the remaining
generation-zero and positive lower cuts. Both structural gates and full B3
are derived where required; no off-plan verdict is an input of the exact
level/envelope endpoints.

The construction must still instantiate the displayed ordinary invariants.
The record parser and identification with the retained slot enumeration are
separate from exact actual AlgorithmRun level selection.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Meaningful omitted bases that require reference-age neutrality.
Dummy and selected-code lower cuts have separate zero-star proofs. -/
def ResolvedQUnretainedMeaningfulBase (r : ResolvedQBaseRole) : Prop :=
  r = .coded false ∨ ∃ block : Nat, r = .auxiliary block false

/-- An actual finite exhaustive list of future selected coding bases,
with the COMPLETE canonical ordinary age unchanged across one base.
Repeats are allowed. Coverage is not restricted to a guessed stage. -/
def ResolvedQK4FullReferenceNeutralAt
    (role : Nat → ResolvedQBaseRole) (E : Nat → Nat → Bool)
    (k N b : Nat) : Prop :=
  ∃ (d : Nat) (target : Fin d → Nat),
    (∀ t, b < target t) ∧
    (∀ t, role (target t) = .coded true) ∧
    (∀ t, hPosition k (target t) k < N) ∧
    (∀ j : Nat, b < j → role j = .coded true →
      ∃ t : Fin d, target t = j) ∧
    baseTopPrefixCanonicalAge E 4 d b target =
      baseTopPrefixCanonicalAge E 4 d (b+1) target

/-- All assumptions of the finite exact-Plan theorem concern the ordinary
graph, chronological roles, a bounded dummy cap, and actual reference ages.
No stage coherence, structural exclusion, B3 or algorithm decision occurs
among the fields. The four-clique scope is explicit. -/
structure ResolvedQK4FinitePlanHypotheses
    (E : Nat → Nat → Bool) (k N : Nat) (cap : Fin N)
    (role : Nat → ResolvedQBaseRole) : Prop where
  height : 4 ≤ k+1
  loops : ∀ i, E i i = false
  chronological : ResolvedQChronologicalAxioms role E
  cliqueFree : ¬ ∃ f : Fin 4 → Nat, StrictMono f ∧
    (∀ a b : Fin 4, a ≠ b → E (f a) (f b) = true)
  blockInterval :
    ∀ p b j block : Nat, ∀ pastFlag futureFlag : Bool,
      p < b → b < j →
      role p = .auxiliary block pastFlag →
      role j = .auxiliary block futureFlag →
      role b = .dummy ∨
        ∃ middleFlag : Bool, role b = .auxiliary block middleFlag
  selectedIndependent : ∀ i j,
    role i = .coded true → role j = .coded true → E i j = false
  capDummy : ∃ b g : Nat, g ≤ k ∧
    cap.val = hPosition k b g ∧ role b = .dummy
  reference : ∀ b : Nat,
    hPosition k b 0 <
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel cap.val →
    ResolvedQUnretainedMeaningfulBase (role b) →
    ResolvedQSelectedNoSplitAt role E b ∧
      ResolvedQK4FullReferenceNeutralAt role E k N b

/-- Complete actual target-list age equality implies every required K4
singleton equality by the arbitrary-sort canonical pullback identity.
In particular no old positive witness is postulated independently. -/
theorem resolvedQK4_singletonNeutral_of_fullReferenceNeutral
    (role : Nat → ResolvedQBaseRole) (E : Nat → Nat → Bool)
    (k N b : Nat)
    (hReference : ResolvedQK4FullReferenceNeutralAt role E k N b) :
    ResolvedQK4SingletonNeutralAt role E b := by
  obtain ⟨d,target,_hLater,_hCode,_hBound,hCover,hAge⟩ := hReference
  intro j hbj hCode
  obtain ⟨t,ht⟩ := hCover j hbj hCode
  let pi : Fin 1 → Fin d := fun _ => t
  let U : IntegerGraphSupport 1 4 :=
    trackFSingletonSupport 1 4 (0 : Fin 1) (of_decide_eq_true rfl)
  have hBefore := finiteOldColumnCanonical_reindex
    E (Finset.range b) (fun p s => E p (target s)) pi
    (show 0 < 4 from of_decide_eq_true rfl) U
  have hAfter := finiteOldColumnCanonical_reindex
    E (Finset.range (b+1)) (fun p s => E p (target s)) pi
    (show 0 < 4 from of_decide_eq_true rfl) U
  have hSame := congrFun hAge (integerGraphSupportImage pi U)
  calc
    resolvedQK4SingletonCapacity E b j =
        baseTopPrefixCanonicalAge E 4 d b target
          (integerGraphSupportImage pi U) := by
      simpa only [resolvedQK4SingletonCapacity, baseTopPrefixCanonicalAge,
        pi, ht, U] using hBefore
    _ = baseTopPrefixCanonicalAge E 4 d (b+1) target
        (integerGraphSupportImage pi U) := hSame
    _ = resolvedQK4SingletonCapacity E (b+1) j := by
      simpa only [resolvedQK4SingletonCapacity, baseTopPrefixCanonicalAge,
        pi, ht, U] using hAfter.symm

/-- Admissibility of the actual finite numerical H is derived from the
ordinary four-clique-free graph hypotheses. -/
theorem resolvedQK4FinitePlan_avoids
    (E : Nat → Nat → Bool) (k N : Nat) (cap : Fin N)
    (role : Nat → ResolvedQBaseRole)
    (h : ResolvedQK4FinitePlanHypotheses E k N cap role) :
    ∀ bad, bad ∈ hensonForbiddenFamily 4 (of_decide_eq_true rfl) →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L := by
  exact finiteNumericH_avoids_family
    (hensonForbiddenFamily 4 (of_decide_eq_true rfl))
    (normalizedGraphModel E) (by intro i; trivial) k N
    ((hensonForbiddenFamily_avoids_iff
      4 (of_decide_eq_true rfl) E).2
        ⟨h.loops, h.chronological.sym, h.cliqueFree⟩)

/-- A direct whole-stage B3 verdict excludes an actual selected cut after
the two full structural gates have been excluded. Stage/final-name B3
transport uses the SAME actual pre-cut closure, not final Plan equality.
This is the general composition step; the exact-Plan theorem below derives
all three verdicts from its ordinary graph/reference hypotheses. -/
theorem k4_actualRun_unselected_of_full_stage_B3
    (k : Nat) (hK : 4 ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin 4 → Nat, StrictMono f ∧
      (∀ a b : Fin 4, a ≠ b → E (f a) (f b) = true))
    (N : Nat) (U : Finset (Fin N))
    (hAvoid : ∀ bad,
      bad ∈ hensonForbiddenFamily 4 (of_decide_eq_true rfl) →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (X : Set (AdmissibleKptNode
      (hensonForbiddenFamily 4 (of_decide_eq_true rfl))))
    (hX : X ⊆ ambientPrefixPool
      (hensonForbiddenFamily 4 (of_decide_eq_true rfl))
      (finiteNumericH (normalizedGraphModel E) k N)
      hAvoid (U : Set (Fin N)))
    (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily 4 (of_decide_eq_true rfl)))
      X top)
    (hTop : ∃ x ∈ X, LevelTree.lev x = top)
    (cut : Nat) (hPos : 0 < cut) (hBelow : cut < top) (hCut : cut < N) :
    let family := hensonForbiddenFamily 4 (of_decide_eq_true rfl)
    let A := finiteNumericH (normalizedGraphModel E) k N
    let Stage := hStageOriginals (normalizedGraphModel E) k N U (Run.I (cut+1))
    let original := hOriginalName Stage
    let Z := SMTree.Envelope.closure (admissibleKptSTree family)
      (Run.I (cut+1)) X
    (¬ ∃ z : AdmissibleKptNode family, z ∈ Z ∧ LevelTree.lev z = cut) →
    (¬ ∃ a : AdmissibleKptNode family, a ∈ Z ∧
      ∃ b : AdmissibleKptNode family, b ∈ Z ∧
        SMTree.Envelope.SameComponent a b ∧
          LevelTree.lev (LevelTree.meet a b) = cut) →
    (closureSelectedBoringData family A hAvoid original Z cut).CorrectedB3 family →
    cut ∉ Run.I 0 := by
  classical
  intro family A Stage original Z hNoI1 hNoI2 hStageB3
  have hPoolEq :=
    finiteNumericH_run_stage_final_full_source_and_B3_eq
      family (normalizedGraphModel E) k N hAvoid U X hX
      top Run cut hBelow hNoI2
  let P := actualHensonRunCutOccurrence
    4 (of_decide_eq_true rfl) k hK E hLoops hSym hClique
    N U hAvoid X top Run cut hCut hNoI2
  have hFinalB3 : P.fullProfile.CorrectedB3 family :=
    hPoolEq.2.mp hStageB3
  intro hSelected
  have hPhysical :
      HensonPhysicalCutStarBadCore
        4 (of_decide_eq_true rfl) P.k P.N cut P.M P.E P.original P.Full :=
    henson_actualRun_nonstructural_I3_has_exact_physical_core
      4 (of_decide_eq_true rfl) k hK E hLoops hSym hClique
      N U hAvoid X hX top Run hTop
      cut hPos hBelow hCut hSelected hNoI1 hNoI2
  have hFailure : ¬ P.fullProfile.CorrectedB3 family :=
    (henson_actualRun_complete_fullB3_failure_iff_physical_bad_core
      4 (of_decide_eq_true rfl) k hK E hLoops hSym hClique
      N U hAvoid X hX top Run cut hCut hBelow hNoI2).2.2.mpr hPhysical
  exact hFailure hFinalB3

private theorem bounded_real_address_of_even
    (k c : Nat) (hEven : c % 2 = 0) :
    ∃ b g : Nat, g ≤ k ∧ c = hPosition k b g := by
  let b := (c/2)/(k+1)
  let g := (c/2)%(k+1)
  have hMod := Nat.mod_lt (c/2) (show 0 < k+1 by omega)
  have hg : g ≤ k := by dsimp [g]; omega
  have hHalf := Nat.mod_add_div c 2
  have hEvenEq : c = 2*(c/2) := by omega
  have hParts : g + (k+1)*b = c/2 := Nat.mod_add_div (c/2) (k+1)
  refine ⟨b,g,hg,?_⟩
  calc
    c = 2*(c/2) := hEvenEq
    _ = 2*(g+(k+1)*b) := congrArg (fun z : Nat => 2*z) hParts.symm
    _ = hPosition k b g := by unfold hPosition; ring

private theorem unretained_meaningful_of_omitted
    (r : ResolvedQBaseRole) (hOmitted : ResolvedQOmittedBase r)
    (hNonDummy : r ≠ .dummy) (hNonSelected : r ≠ .coded true) :
    ResolvedQUnretainedMeaningfulBase r := by
  rcases hOmitted with hDummy | ⟨selected,hCode⟩ | ⟨block,hAux⟩
  · exact False.elim (hNonDummy hDummy)
  · cases selected with
    | false => exact Or.inl hCode
    | true => exact False.elim (hNonSelected hCode)
  · exact Or.inr ⟨block,hAux⟩

/-- Every omitted cut of the actual enlarged planned-prefix run is both
unselected and noninteresting, assuming only its TRUE higher-stage Plan
inclusion. All physical/structural/B3 gates are derived from ordinary
resolved-Q and full canonical reference-age hypotheses. -/
theorem k4_numericRetainedPlan_offPlan_skip
    (E : Nat → Nat → Bool) (k N : Nat) (cap : Fin N)
    (role : Nat → ResolvedQBaseRole)
    (h : ResolvedQK4FinitePlanHypotheses E k N cap role)
    (hAvoid : ∀ bad,
      bad ∈ hensonForbiddenFamily 4 (of_decide_eq_true rfl) →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily 4 (of_decide_eq_true rfl)))
      (plannedPrefixSeeds
        ((finiteNumericH (normalizedGraphModel E) k N).kptOriginal
          (hensonForbiddenFamily 4 (of_decide_eq_true rfl)) hAvoid cap)
        (numericRetainedPlan (normalizedGraphModel E) k N cap role : Set Nat))
      ((finiteNumericH (normalizedGraphModel E) k N).freeLevel cap.val))
    (c : Nat)
    (hBelow : c < (finiteNumericH (normalizedGraphModel E) k N).freeLevel cap.val)
    (hOmitted : c ∉ numericRetainedPlan (normalizedGraphModel E) k N cap role)
    (hAbove : Run.I (c+1) ⊆
      (numericRetainedPlan (normalizedGraphModel E) k N cap role : Set Nat)) :
    c ∉ Run.I 0 ∧
      ¬ SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree (hensonForbiddenFamily 4 (of_decide_eq_true rfl)))
        (SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily 4 (of_decide_eq_true rfl)))
          (Run.I (c+1))
          (plannedPrefixSeeds
            ((finiteNumericH (normalizedGraphModel E) k N).kptOriginal
              (hensonForbiddenFamily 4 (of_decide_eq_true rfl)) hAvoid cap)
            (numericRetainedPlan (normalizedGraphModel E) k N cap role : Set Nat))) c := by
  classical
  let family := hensonForbiddenFamily 4 (of_decide_eq_true rfl)
  let K := normalizedGraphModel E
  let A := finiteNumericH K k N
  let Plan : Set Nat := numericRetainedPlan K k N cap role
  let U : Finset (Fin N) := {cap}
  let X := plannedPrefixSeeds (A.kptOriginal family hAvoid cap) Plan
  let top := A.freeLevel cap.val
  have hk : 0 < k := by have hK := h.height; omega
  have hX : X ⊆ ambientPrefixPool family A hAvoid (U : Set (Fin N)) := by
    intro z hz
    refine ⟨A.kptOriginal family hAvoid cap, ⟨cap, ?_, rfl⟩, hz.1⟩
    exact Finset.mem_singleton_self cap
  have hTopMem : top ∈ Plan := numericRetainedPlan_cap_end_mem K k N cap role
  have hTop : ∃ z ∈ X, LevelTree.lev z = top := by
    refine ⟨A.kptOriginal family hAvoid cap, ?_, rfl⟩
    exact ⟨le_rfl,hTopMem⟩
  have hPos : 0 < c := by
    have hZero := numericRetainedPlan_zero_mem K k N cap role
    by_contra hn
    have hc : c = 0 := by omega
    apply hOmitted
    simpa only [hc] using hZero
  have hCut : c < N :=
    (hBelow.trans_le (A.freeLevel_le cap.val)).trans cap.isLt
  have hNoSeed : ¬ ∃ z ∈ X, LevelTree.lev z = c :=
    plannedPrefixSeeds_no_seed_outside
      (A.kptOriginal family hAvoid cap) Plan c hOmitted
  obtain ⟨capBase,capGen,hCapGen,hCapAddr,hCapDummy⟩ := h.capDummy
  have hRootDummy : ∀ v : Fin N, v ∈ U →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m → role j = .dummy :=
    numericRetainedPlan_dummy_cap_root_role
      k N cap role capBase capGen hCapGen hCapAddr hCapDummy
  have hPlanShape : ∀ v : Fin N, v.val ∈ Plan → 0 < A.freeLevel v.val →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m →
        (role j = .coded true ∧ m = k) ∨
        (∃ block : Nat, role j = .auxiliary block true) := by
    intro v hv hPositive j m hm hAddr
    exact numericRetainedPlan_bounded_role_shape
      K k N cap role v hv hPositive j m hm hAddr
  have hUnselected : c ∉ Run.I 0 := by
    rcases Nat.mod_two_eq_zero_or_one c with hEven | hOdd
    · obtain ⟨b,g,hg,hAddr⟩ := bounded_real_address_of_even k c hEven
      subst c
      have hRole : ResolvedQOmittedBase (role b) :=
        numericRetainedPlan_omitted_real_role
          K k N cap role b g hg hBelow hOmitted
      rcases lt_or_eq_of_le hg with hLower | hTopGen
      · by_cases hDummy : role b = .dummy
        · exact henson_actualRun_isolated_dummy_lower_real_skip_of_no_seed
            4 (of_decide_eq_true rfl) k h.height E h.loops h.chronological.sym
            h.cliqueFree N U hAvoid X hX top Run hTop b g hLower
            hPos hBelow hCut hNoSeed (fun j => h.chronological.dummy b j hDummy)
        · by_cases hSelectedBase : role b = .coded true
          · exact henson_actualRun_selected_coded_lower_real_skip_of_no_seed
              4 (of_decide_eq_true rfl) k h.height E h.loops h.chronological.sym
              h.cliqueFree N U hAvoid X hX top Run hTop b g hLower
              hPos hBelow hCut hNoSeed Plan hAbove role h.chronological
              h.selectedIndependent hRootDummy hPlanShape hSelectedBase
          · have hMeaningful : ResolvedQUnretainedMeaningfulBase (role b) :=
              unretained_meaningful_of_omitted (role b) hRole hDummy hSelectedBase
            have hZeroBelow : hPosition k b 0 < A.freeLevel cap.val := by
              apply lt_of_le_of_lt (show hPosition k b 0 ≤ hPosition k b g by
                unfold hPosition
                omega) hBelow
            obtain ⟨hNoSplit,hReference⟩ := h.reference b hZeroBelow hMeaningful
            have hSingleton := resolvedQK4_singletonNeutral_of_fullReferenceNeutral
              role E k N b hReference
            let cut := hPosition k b g
            let Stage := hStageOriginals K k N U (Run.I (cut+1))
            let original := hOriginalName Stage
            let Z := SMTree.Envelope.closure (admissibleKptSTree family)
              (Run.I (cut+1)) X
            have hStructural :
                (¬ ∃ z : AdmissibleKptNode family, z ∈ Z ∧ LevelTree.lev z = cut) ∧
                (¬ ∃ a : AdmissibleKptNode family, a ∈ Z ∧
                  ∃ b' : AdmissibleKptNode family, b' ∈ Z ∧
                    SMTree.Envelope.SameComponent a b' ∧
                      LevelTree.lev (LevelTree.meet a b') = cut) := by
              by_cases hZero : g = 0
              · subst g
                exact resolvedQ_actualRun_zero_generation_no_full_I1_I2
                  family E k N hk hAvoid U X hX top Run b hPos hCut hNoSeed
                  Plan hAbove role h.chronological hRootDummy hPlanShape
                  h.blockInterval hRole hDummy hNoSplit hSingleton
              · have hgPositive : 0 < g := by omega
                exact resolvedQ_actualRun_positive_generation_no_full_I1_I2
                  family E k N hAvoid U X hX top Run b g hgPositive hg hCut
                  hNoSeed Plan hAbove role h.chronological hRootDummy hPlanShape hRole
            obtain ⟨d,target,hLater,_hCode,hTargetBound,hTargetCover,hNeutral⟩ :=
              hReference
            have hFullB3 :
                (closureSelectedBoringData family A hAvoid original Z cut).CorrectedB3
                  family := by
              exact k4_resolvedQ_stage_B3_of_base_prefix_neutral
                E k h.height N U (Run.I (cut+1)) Plan hAbove role h.chronological
                h.loops h.cliqueFree hRootDummy hPlanShape b g hLower hCut hRole
                d target hLater hTargetBound
                (fun j hbj hCode _hInside => hTargetCover j hbj hCode) hNeutral
                (closureSelectedOriginal family A hAvoid original Z cut)
            exact k4_actualRun_unselected_of_full_stage_B3
              k h.height E h.loops h.chronological.sym h.cliqueFree
              N U hAvoid X hX top Run hTop cut hPos hBelow hCut
              hStructural.1 hStructural.2 hFullB3
      · subst g
        exact (henson_actualRun_omitted_top_generation_skip
          4 (of_decide_eq_true rfl) k h.height E h.loops h.chronological.sym
          h.cliqueFree N U hAvoid X hX top Run hTop b hBelow hCut hNoSeed
          Plan hAbove role h.chronological hRootDummy hPlanShape hRole).1
    · obtain ⟨a,hAddr⟩ : ∃ a : Nat, c = 2*a+1 := by
        have hParts := Nat.mod_add_div c 2
        exact ⟨c/2, by omega⟩
      subst c
      exact (henson_numericRetainedPlan_odd_run_skip
        4 (of_decide_eq_true rfl) k h.height E h.loops h.chronological.sym
        h.cliqueFree N cap role hAvoid Run a hBelow hAbove hOmitted).1
  refine ⟨hUnselected,?_⟩
  intro hInteresting
  have hSelected : c ∈ Run.I c := by
    rw [(Run.interesting_step c hBelow hInteresting).1]
    exact Set.mem_insert _ _
  rw [Run.I_eq_final_tail_of_run c (Nat.le_of_lt hBelow)] at hSelected
  exact hUnselected hSelected.1

/-- The ACTUAL run on all planned cap prefixes has exactly the constructed
finite retained levels, exact selected tails, whole-node envelope coverage,
and the stated full output level range. No off-plan skip premise remains.
The displayed avoidance proof only fixes the admissible original's type;
it is supplied from the ordinary hypotheses by the next existence theorem. -/
theorem k4_numericRetainedPlan_run_exact
    (E : Nat → Nat → Bool) (k N : Nat) (cap : Fin N)
    (role : Nat → ResolvedQBaseRole)
    (h : ResolvedQK4FinitePlanHypotheses E k N cap role)
    (hAvoid : ∀ bad,
      bad ∈ hensonForbiddenFamily 4 (of_decide_eq_true rfl) →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily 4 (of_decide_eq_true rfl)))
      (plannedPrefixSeeds
        ((finiteNumericH (normalizedGraphModel E) k N).kptOriginal
          (hensonForbiddenFamily 4 (of_decide_eq_true rfl)) hAvoid cap)
        (numericRetainedPlan (normalizedGraphModel E) k N cap role : Set Nat))
      ((finiteNumericH (normalizedGraphModel E) k N).freeLevel cap.val)) :
    let Plan : Set Nat := numericRetainedPlan (normalizedGraphModel E) k N cap role
    let top := (finiteNumericH (normalizedGraphModel E) k N).freeLevel cap.val
    let X := plannedPrefixSeeds
      ((finiteNumericH (normalizedGraphModel E) k N).kptOriginal
        (hensonForbiddenFamily 4 (of_decide_eq_true rfl)) hAvoid cap) Plan
    Run.I 0 = Plan ∧
      (∀ i : Nat, i ≤ top → Run.I i = {q | q ∈ Plan ∧ i ≤ q}) ∧
      SMTree.Envelope.IsEnvelope (Run.F 0).map X ∧
      (Run.F 0).map.levelRange = {q | q ∈ Plan ∨ top < q} := by
  classical
  intro Plan top X
  let family := hensonForbiddenFamily 4 (of_decide_eq_true rfl)
  let A := finiteNumericH (normalizedGraphModel E) k N
  let C := A.kptOriginal family hAvoid cap
  have hExact := plannedPrefixSeeds_run_exact_plan
    (normalizedKptSMTree family)
    (normalizedKpt_oneLevelPullback_for_envelopes family) C Plan
    (numericRetainedPlan_cap_end_mem (normalizedGraphModel E) k N cap role)
    (fun i hi => numericRetainedPlan_bounded
      (normalizedGraphModel E) k N cap role i hi)
    Run (fun c hBelow hOmitted hAbove =>
      (k4_numericRetainedPlan_offPlan_skip E k N cap role h hAvoid
        Run c hBelow hOmitted hAbove).2)
  refine ⟨?_,hExact⟩
  apply Set.ext
  intro q
  rw [hExact.1 0 (Nat.zero_le _)]
  change (q ∈ Plan ∧ 0 ≤ q) ↔ q ∈ Plan
  simp

/-- Ordinary finite resolved-Q invariants construct the genuine canonical
run and its exact retained-plan envelope. Finite-H admissibility and the
normalized Kpt E1 requirement are both derived. The zero-cap boundary is
allowed; no positive-size G+ source is asserted by this endpoint. -/
theorem k4_numericRetainedPlan_exists_exact_envelope
    (E : Nat → Nat → Bool) (k N : Nat) (cap : Fin N)
    (role : Nat → ResolvedQBaseRole)
    (h : ResolvedQK4FinitePlanHypotheses E k N cap role) :
    let family := hensonForbiddenFamily 4 (of_decide_eq_true rfl)
    let A := finiteNumericH (normalizedGraphModel E) k N
    let hAvoid := resolvedQK4FinitePlan_avoids E k N cap role h
    let Plan : Set Nat := numericRetainedPlan (normalizedGraphModel E) k N cap role
    let top := A.freeLevel cap.val
    let X := plannedPrefixSeeds (A.kptOriginal family hAvoid cap) Plan
    ∃ Run : SMTree.Envelope.AlgorithmRun (normalizedKptSMTree family) X top,
      Run.I 0 = Plan ∧
      (∀ i : Nat, i ≤ top → Run.I i = {q | q ∈ Plan ∧ i ≤ q}) ∧
      SMTree.Envelope.IsEnvelope (Run.F 0).map X ∧
      (Run.F 0).map.levelRange = {q | q ∈ Plan ∨ top < q} := by
  intro family A hAvoid Plan top X
  let Run := SMTree.Envelope.canonicalAlgorithmRun
    (normalizedKptSMTree family) X top
  exact ⟨Run,k4_numericRetainedPlan_run_exact E k N cap role h hAvoid Run⟩

#print axioms Kk.resolvedQK4_singletonNeutral_of_fullReferenceNeutral
#print axioms Kk.resolvedQK4FinitePlan_avoids
#print axioms Kk.k4_actualRun_unselected_of_full_stage_B3
#print axioms Kk.k4_numericRetainedPlan_offPlan_skip
#print axioms Kk.k4_numericRetainedPlan_run_exact
#print axioms Kk.k4_numericRetainedPlan_exists_exact_envelope

end Kk
