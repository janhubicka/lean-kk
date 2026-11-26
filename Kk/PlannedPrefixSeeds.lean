import SuccessorTree.EnvelopeRunExistence
import SuccessorTree.V10.ConcreteOriginalPool
import Mathlib.Tactic

/-!
# Exact prescribed levels from selected cap-prefix seeds

English proof and independent review were committed before this module:
`docs/retained_prefix_source_and_plan_seeds_english_20261124.md` and
`docs/audits/2026-11-24-retained-prefix-source-independent-review.md`.

Seed precisely the cap ancestors whose levels belong to Plan. The ordinary
AlgorithmRun then retains every planned level by actual I1 witnesses. If
the genuine descending off-plan boringness implication is established for
THIS seed family, its final level set is exactly Plan. E1 supplies actual
whole-node range coverage and the exact output level range.

All these seeds are represented by one physical cap original. They are
not the entire ancestor-prefix pool, and they are not the smaller literal
`numericHTopGenerationSeeds` family. The resolved-Q off-plan boringness
premise remains an application obligation.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

universe u v

/-- Only cap prefixes at planned levels are initial seeds. The order
condition already bounds every seed by the cap's actual level. -/
def plannedPrefixSeeds
    {T : Type u} [PartialOrder T] [LevelTree T]
    (cap : T) (Plan : Set Nat) : Set T :=
  {z | z ≤ cap ∧ LevelTree.lev z ∈ Plan}

/-- Every planned level below the cap has a literal ancestor seed. -/
theorem plannedPrefixSeeds_seed_at
    {T : Type u} [PartialOrder T] [LevelTree T]
    (cap : T) (Plan : Set Nat)
    (i : Nat) (hi : i ∈ Plan) (hBound : i ≤ LevelTree.lev cap) :
    ∃ z ∈ plannedPrefixSeeds cap Plan, LevelTree.lev z = i := by
  refine ⟨LevelTree.ancestor cap i hBound, ?_,
    LevelTree.level_ancestor cap i hBound⟩
  constructor
  · exact LevelTree.ancestor_le cap i hBound
  · simpa only [LevelTree.level_ancestor] using hi

/-- A cut outside Plan cannot be an endpoint of an initial planned
prefix seed. No assertion about generated closure nodes is made here. -/
theorem plannedPrefixSeeds_no_seed_outside
    {T : Type u} [PartialOrder T] [LevelTree T]
    (cap : T) (Plan : Set Nat)
    (cut : Nat) (hOutside : cut ∉ Plan) :
    ¬ ∃ z ∈ plannedPrefixSeeds cap Plan, LevelTree.lev z = cut := by
  rintro ⟨z, hz, hLev⟩
  apply hOutside
  simpa only [hLev] using hz.2

/-- Planned prefix seeds satisfy the actual algorithm height bound,
even before any proposed bound on the set Plan is supplied. -/
theorem plannedPrefixSeeds_bounded
    {T : Type u} [PartialOrder T] [LevelTree T]
    (cap : T) (Plan : Set Nat) :
    plannedPrefixSeeds cap Plan ⊆
      SMTree.Envelope.levelLe (LevelTree.lev cap) := by
  intro z hz
  exact LevelTree.level_le_of_le hz.1

/-- Enlarging the cap seeds to its planned ancestors preserves the
literal singleton PHYSICAL original representation. It does not assert
that the subsequent meet/parameter closure has no other originals. -/
theorem plannedPrefixSeeds_subset_singleton_original_pool
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (cap : Fin A.size) (Plan : Set Nat) :
    plannedPrefixSeeds (A.kptOriginal family hAvoid cap) Plan ⊆
      ambientPrefixPool family A hAvoid ({cap} : Set (Fin A.size)) := by
  intro z hz
  exact ⟨A.kptOriginal family hAvoid cap,
    ⟨cap, Set.mem_singleton cap, rfl⟩, hz.1⟩

private theorem planned_induction_down
    {top : Nat} {P : Nat → Prop}
    (hTop : P top)
    (hStep : ∀ i, i < top → P (i+1) → P i) :
    ∀ i, i ≤ top → P i := by
  have main : ∀ d : Nat, ∀ i, top-i = d → i ≤ top → P i := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro i hdi hi
      by_cases hEq : i = top
      · simpa only [hEq] using hTop
      · have hLt : i < top := by omega
        apply hStep i hLt
        exact ih (top-(i+1)) (by omega) (i+1) rfl (by omega)
  intro i hi
  exact main (top-i) i rfl hi

/-- A genuine run has exactly the planned FINAL levels when each
planned level has an initial seed and the actual descending off-plan
boringness implication holds. The latter concerns this run's complete
pre-cut closure, not a smaller seed family or selected-type shadow.

The result derives both containments; final-level equality is not an
input. E1 is unnecessary for this decision theorem. -/
theorem algorithmRun_final_levels_eq_plan_of_seed_levels
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    {S : STree T Label}
    (H : SMTree S) (X : Set T) (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun H X top)
    (Plan : Set Nat)
    (hTop : top ∈ Plan)
    (hBound : ∀ i ∈ Plan, i ≤ top)
    (hSeed : ∀ i ∈ Plan, ∃ z ∈ X, LevelTree.lev z = i)
    (hOffPlan : ∀ c : Nat, c < top → c ∉ Plan →
      R.I (c+1) ⊆ Plan →
      ¬ SMTree.Envelope.IsInterestingAt H
        (SMTree.Envelope.closure S (R.I (c+1)) X) c) :
    R.I 0 = Plan := by
  have hSubset : ∀ i, i ≤ top → R.I i ⊆ Plan := by
    apply planned_induction_down
    · rw [R.topI]
      intro q hq
      have hEq : q = top := Set.mem_singleton_iff.mp hq
      simpa only [hEq] using hTop
    · intro i hi hNext
      by_cases hIn : i ∈ Plan
      · rcases R.level_step i hi with hSame | hInsert
        · rw [hSame]
          exact hNext
        · rw [hInsert]
          intro q hq
          rcases Set.mem_insert_iff.mp hq with hEq | hOld
          · simpa only [hEq] using hIn
          · exact hNext hOld
      · obtain ⟨D, _hSkip, _hCross, hSame, _hMap⟩ :=
          R.noninteresting_step i hi (hOffPlan i hi hIn hNext)
        rw [hSame]
        exact hNext
  apply Set.Subset.antisymm (hSubset 0 (Nat.zero_le top))
  intro i hi
  have hiTop : i ≤ top := hBound i hi
  have hSelected : i ∈ R.I i := by
    by_cases hEq : i = top
    · rw [hEq, R.topI]
      exact Set.mem_singleton top
    · have hLt : i < top := by omega
      obtain ⟨z, hz, hLev⟩ := hSeed i hi
      have hInteresting : SMTree.Envelope.IsInterestingAt H
          (SMTree.Envelope.closure S (R.I (i+1)) X) i :=
        Or.inl ⟨z,
          SMTree.Envelope.subset_closure S (R.I (i+1)) X hz, hLev⟩
      rw [(R.interesting_step i hLt hInteresting).1]
      exact Set.mem_insert i (R.I (i+1))
  rw [R.I_eq_final_tail_of_run i hiTop] at hSelected
  exact hSelected.1

/-- For selected cap-prefix seeds, derive exact final/tail levels,
whole-node coverage and the exact output level range of the ACTUAL run.
Its top and physical original representation are intrinsic to the cap.

The case of a level-zero cap is allowed; no positive-size G+ vertex is
claimed by this generic algorithm statement. -/
theorem plannedPrefixSeeds_run_exact_plan
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    {S : STree T Label}
    (H : SMTree S)
    (hE1 : SMTree.Envelope.OneLevelPullback H)
    (cap : T) (Plan : Set Nat)
    (hTop : LevelTree.lev cap ∈ Plan)
    (hBound : ∀ i ∈ Plan, i ≤ LevelTree.lev cap)
    (R : SMTree.Envelope.AlgorithmRun
      H (plannedPrefixSeeds cap Plan) (LevelTree.lev cap))
    (hOffPlan : ∀ c : Nat, c < LevelTree.lev cap → c ∉ Plan →
      R.I (c+1) ⊆ Plan →
      ¬ SMTree.Envelope.IsInterestingAt H
        (SMTree.Envelope.closure S (R.I (c+1))
          (plannedPrefixSeeds cap Plan)) c) :
    (∀ i : Nat, i ≤ LevelTree.lev cap →
      R.I i = {q | q ∈ Plan ∧ i ≤ q}) ∧
    SMTree.Envelope.IsEnvelope (R.F 0).map
      (plannedPrefixSeeds cap Plan) ∧
    (R.F 0).map.levelRange = {q | q ∈ Plan ∨ LevelTree.lev cap < q} := by
  have hFinal : R.I 0 = Plan :=
    algorithmRun_final_levels_eq_plan_of_seed_levels
      H (plannedPrefixSeeds cap Plan) (LevelTree.lev cap)
      R Plan hTop hBound
      (fun i hi => plannedPrefixSeeds_seed_at cap Plan i hi (hBound i hi))
      hOffPlan
  have hInv := R.fullInvariant hE1
    (plannedPrefixSeeds_bounded cap Plan) 0 (Nat.zero_le _)
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [R.I_eq_final_tail_of_run i hi, hFinal]
  · intro z hz
    exact hInv.1.1
      (SMTree.Envelope.subset_closure S (R.I 0)
        (plannedPrefixSeeds cap Plan) hz)
  · have hRange := SMTree.Envelope.stageFullInvariant_levelRange
      H (plannedPrefixSeeds cap Plan) (LevelTree.lev cap) 0
      (R.I 0) (R.F 0) hInv
    simpa only [Nat.not_lt_zero, false_or, hFinal] using hRange

/-- Construct an actual run and its envelope output from the planned
cap-prefix seeds. Only the explicitly stated off-plan implication for
genuine runs is left to the physical application. -/
theorem plannedPrefixSeeds_exists_exact_envelope
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    {S : STree T Label}
    (H : SMTree S)
    (hE1 : SMTree.Envelope.OneLevelPullback H)
    (cap : T) (Plan : Set Nat)
    (hTop : LevelTree.lev cap ∈ Plan)
    (hBound : ∀ i ∈ Plan, i ≤ LevelTree.lev cap)
    (hOffPlan : ∀ R : SMTree.Envelope.AlgorithmRun
        H (plannedPrefixSeeds cap Plan) (LevelTree.lev cap),
      ∀ c : Nat, c < LevelTree.lev cap → c ∉ Plan →
        R.I (c+1) ⊆ Plan →
        ¬ SMTree.Envelope.IsInterestingAt H
          (SMTree.Envelope.closure S (R.I (c+1))
            (plannedPrefixSeeds cap Plan)) c) :
    ∃ R : SMTree.Envelope.AlgorithmRun
        H (plannedPrefixSeeds cap Plan) (LevelTree.lev cap),
      (∀ i : Nat, i ≤ LevelTree.lev cap →
        R.I i = {q | q ∈ Plan ∧ i ≤ q}) ∧
      SMTree.Envelope.IsEnvelope (R.F 0).map
        (plannedPrefixSeeds cap Plan) ∧
      (R.F 0).map.levelRange =
        {q | q ∈ Plan ∨ LevelTree.lev cap < q} := by
  let R := SMTree.Envelope.canonicalAlgorithmRun
    H (plannedPrefixSeeds cap Plan) (LevelTree.lev cap)
  exact ⟨R, plannedPrefixSeeds_run_exact_plan
    H hE1 cap Plan hTop hBound R (hOffPlan R)⟩

end Kk
