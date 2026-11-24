import Kk.PlannedPrefixSeeds
import Kk.TrackDResolvedQBaseRoles
import Kk.TrackDOddPlanFreeClosure
import SuccessorTree.V10.HPositiveFreeLevelOdd
import Mathlib.Tactic

/-!
# A concrete finite retained plan for numerical H

English proof and independent review were committed before implementation:
`docs/numeric_retained_plan_english_20261124.md` and
`docs/audits/2026-11-24-numeric-retained-plan-independent-review-generation-zero.md`.

Keep exactly the canonical real coordinates below the actual cap end that
are selected coding TOPs or members of retained auxiliary blocks. Add zero,
the cap end, and every kept original's actual free cut. This constructs a
finite bounded plan and derives its free-cut closure and bounded role shape.

Applying the actual numerical-H free-level operation twice gives zero.
Consequently the added free cuts cannot introduce unexpected positive-free
stage originals. The actual enlarged planned-prefix-seed run skips omitted
odd cuts under its true descending stage inclusion. No selected-age proxy,
final-stage inclusion or independently postulated Plan closure is used.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Canonical retained real coordinates strictly below a chosen end.
The actual finite carrier, generation bounds, retained flags and coding
TOP condition all occur in the definition. -/
noncomputable def numericRetainedOriginals
    (k N top : Nat) (role : Nat → ResolvedQBaseRole) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun v => v.val < top ∧
    ∃ b g : Nat, g ≤ k ∧ v.val = hPosition k b g ∧
      ((role b = .coded true ∧ g = k) ∨
        ∃ block : Nat, role b = .auxiliary block true))

theorem mem_numericRetainedOriginals_iff
    (k N top : Nat) (role : Nat → ResolvedQBaseRole) (v : Fin N) :
    v ∈ numericRetainedOriginals k N top role ↔
      v.val < top ∧
        ∃ b g : Nat, g ≤ k ∧ v.val = hPosition k b g ∧
          ((role b = .coded true ∧ g = k) ∨
            ∃ block : Nat, role b = .auxiliary block true) := by
  classical
  simp only [numericRetainedOriginals, Finset.mem_filter,
    Finset.mem_univ, true_and]

/-- The finite plan contains the initial anchor, the actual cap end,
all retained real coordinates below that end, and their actual E free cuts.
No closure or role-shape condition is taken as an input. -/
noncomputable def numericRetainedPlan
    {db du dd : Nat} (K : AgeTestModel db du dd)
    (k N : Nat) (cap : Fin N) (role : Nat → ResolvedQBaseRole) :
    Finset Nat := by
  classical
  let A := finiteNumericH K k N
  let Kept := numericRetainedOriginals k N (A.freeLevel cap.val) role
  exact insert 0 (insert (A.freeLevel cap.val)
    (Kept.image Fin.val ∪ Kept.image (fun v => A.freeLevel v.val)))

/-- The incoming E column at an odd target is empty in the actual
finite constructor. Its canonical free cut is therefore zero. -/
theorem finiteNumericH_odd_target_freeLevel_zero
    {db du dd : Nat} (K : AgeTestModel db du dd)
    (k N a : Nat) :
    (finiteNumericH K k N).freeLevel (2*a+1) = 0 := by
  let A := finiteNumericH K k N
  have hNot : ¬ 0 < A.freeLevel (2*a+1) := by
    intro hPositive
    have hE : A.E 0 (2*a+1) = true :=
      (A.E_iff_freeLevel 0 (2*a+1)).2 hPositive
    have hExact : exactHEBool k 0 (2*a+1) = true :=
      ((finiteNumericHE_true_iff k N 0 (2*a+1)).1 hE).2
    rw [exactHEBool_odd_target_false] at hExact
    cases hExact
  change A.freeLevel (2*a+1) = 0
  omega

/-- On genuine finite original addresses, the actual free-level
operation followed by itself is zero. Positive free cuts are odd,
and odd targets have zero free level. This also covers height k=0. -/
theorem finiteNumericH_freeLevel_freeLevel_zero
    {db du dd : Nat} (K : AgeTestModel db du dd)
    (k N v : Nat) (hv : v < N) :
    (finiteNumericH K k N).freeLevel
      ((finiteNumericH K k N).freeLevel v) = 0 := by
  let A := finiteNumericH K k N
  by_cases hZero : A.freeLevel v = 0
  · change A.freeLevel (A.freeLevel v) = 0
    rw [hZero]
    exact Nat.eq_zero_of_le_zero (A.freeLevel_le 0)
  · have hPositive : 0 < A.freeLevel v := by omega
    obtain ⟨a, hOdd⟩ :=
      finiteNumericH_positive_freeLevel_odd K k N v hv hPositive
    rw [hOdd]
    exact finiteNumericH_odd_target_freeLevel_zero K k N a

theorem numericRetainedPlan_zero_mem
    {db du dd : Nat} (K : AgeTestModel db du dd)
    (k N : Nat) (cap : Fin N) (role : Nat → ResolvedQBaseRole) :
    0 ∈ numericRetainedPlan K k N cap role := by
  classical
  simp only [numericRetainedPlan, Finset.mem_insert, true_or]

theorem numericRetainedPlan_cap_end_mem
    {db du dd : Nat} (K : AgeTestModel db du dd)
    (k N : Nat) (cap : Fin N) (role : Nat → ResolvedQBaseRole) :
    (finiteNumericH K k N).freeLevel cap.val ∈
      numericRetainedPlan K k N cap role := by
  classical
  simp only [numericRetainedPlan, Finset.mem_insert, true_or, or_true]

theorem numericRetainedPlan_kept_position_mem
    {db du dd : Nat} (K : AgeTestModel db du dd)
    (k N : Nat) (cap : Fin N) (role : Nat → ResolvedQBaseRole)
    (v : Fin N)
    (hv : v ∈ numericRetainedOriginals k N
      ((finiteNumericH K k N).freeLevel cap.val) role) :
    v.val ∈ numericRetainedPlan K k N cap role := by
  classical
  apply Finset.mem_insert_of_mem
  apply Finset.mem_insert_of_mem
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)

theorem numericRetainedPlan_kept_free_mem
    {db du dd : Nat} (K : AgeTestModel db du dd)
    (k N : Nat) (cap : Fin N) (role : Nat → ResolvedQBaseRole)
    (v : Fin N)
    (hv : v ∈ numericRetainedOriginals k N
      ((finiteNumericH K k N).freeLevel cap.val) role) :
    (finiteNumericH K k N).freeLevel v.val ∈
      numericRetainedPlan K k N cap role := by
  classical
  apply Finset.mem_insert_of_mem
  apply Finset.mem_insert_of_mem
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)

set_option maxHeartbeats 1000000 in
/-- Every planned coordinate is below or equal to the actual cap end.
The strict bound on retained real coordinates is in Kept itself. -/
theorem numericRetainedPlan_bounded
    {db du dd : Nat} (K : AgeTestModel db du dd)
    (k N : Nat) (cap : Fin N) (role : Nat → ResolvedQBaseRole) :
    ∀ q ∈ numericRetainedPlan K k N cap role,
      q ≤ (finiteNumericH K k N).freeLevel cap.val := by
  classical
  let A := finiteNumericH K k N
  let Kept := numericRetainedOriginals k N (A.freeLevel cap.val) role
  intro q hq
  unfold numericRetainedPlan at hq
  rcases Finset.mem_insert.mp hq with hZero | hq
  · subst q
    exact Nat.zero_le _
  rcases Finset.mem_insert.mp hq with hTop | hq
  · rw [hTop]
  rcases Finset.mem_union.mp hq with hReal | hFree
  · obtain ⟨v, hv, hEq⟩ := Finset.mem_image.mp hReal
    have hBelow :=
      ((mem_numericRetainedOriginals_iff k N (A.freeLevel cap.val)
        role v).1 hv).1
    rw [← hEq]
    exact Nat.le_of_lt hBelow
  · obtain ⟨v, hv, hEq⟩ := Finset.mem_image.mp hFree
    have hBelow :=
      ((mem_numericRetainedOriginals_iff k N (A.freeLevel cap.val)
        role v).1 hv).1
    rw [← hEq]
    exact (A.freeLevel_le v.val).trans (Nat.le_of_lt hBelow)

set_option maxHeartbeats 1000000 in
/-- A Plan address with positive free level must come from the kept
REAL-coordinate summand. The anchor, end and added free-cut addresses
all have free level zero. -/
theorem numericRetainedPlan_positive_member_kept
    {db du dd : Nat} (K : AgeTestModel db du dd)
    (k N : Nat) (cap : Fin N) (role : Nat → ResolvedQBaseRole)
    (v : Fin N)
    (hPlan : v.val ∈ numericRetainedPlan K k N cap role)
    (hPositive : 0 < (finiteNumericH K k N).freeLevel v.val) :
    v ∈ numericRetainedOriginals k N
      ((finiteNumericH K k N).freeLevel cap.val) role := by
  classical
  let A := finiteNumericH K k N
  let Kept := numericRetainedOriginals k N (A.freeLevel cap.val) role
  unfold numericRetainedPlan at hPlan
  rcases Finset.mem_insert.mp hPlan with hZero | hPlan
  · have hLe := A.freeLevel_le v.val
    change 0 < A.freeLevel v.val at hPositive
    omega
  rcases Finset.mem_insert.mp hPlan with hTop | hPlan
  · have hZero : A.freeLevel v.val = 0 := by
      rw [hTop]
      exact finiteNumericH_freeLevel_freeLevel_zero K k N cap.val cap.isLt
    change 0 < A.freeLevel v.val at hPositive
    omega
  rcases Finset.mem_union.mp hPlan with hReal | hFree
  · obtain ⟨w, hw, hEq⟩ := Finset.mem_image.mp hReal
    have hwv : w = v := Fin.ext hEq
    exact hwv ▸ hw
  · obtain ⟨w, _hw, hEq⟩ := Finset.mem_image.mp hFree
    have hZero : A.freeLevel v.val = 0 := by
      rw [← hEq]
      exact finiteNumericH_freeLevel_freeLevel_zero K k N w.val w.isLt
    change 0 < A.freeLevel v.val at hPositive
    omega

/-- The CONSTRUCTED finite Plan is closed under actual E free cuts.
No closure premise and no positive-free-level premise are necessary. -/
theorem numericRetainedPlan_free_closed
    {db du dd : Nat} (K : AgeTestModel db du dd)
    (k N : Nat) (cap : Fin N) (role : Nat → ResolvedQBaseRole)
    (v : Fin N) (hPlan : v.val ∈ numericRetainedPlan K k N cap role) :
    (finiteNumericH K k N).freeLevel v.val ∈
      numericRetainedPlan K k N cap role := by
  by_cases hZero : (finiteNumericH K k N).freeLevel v.val = 0
  · rw [hZero]
    exact numericRetainedPlan_zero_mem K k N cap role
  · have hPositive : 0 < (finiteNumericH K k N).freeLevel v.val := by omega
    exact numericRetainedPlan_kept_free_mem K k N cap role v
      (numericRetainedPlan_positive_member_kept
        K k N cap role v hPlan hPositive)

/-- The repaired canonical-generation Plan role contract is a theorem
of the concrete finite Plan. The bound m<=k is essential for decoding. -/
theorem numericRetainedPlan_bounded_role_shape
    {db du dd : Nat} (K : AgeTestModel db du dd)
    (k N : Nat) (cap : Fin N) (role : Nat → ResolvedQBaseRole)
    (v : Fin N) (hPlan : v.val ∈ numericRetainedPlan K k N cap role)
    (hPositive : 0 < (finiteNumericH K k N).freeLevel v.val)
    (j m : Nat) (hm : m ≤ k) (hAddr : v.val = hPosition k j m) :
    (role j = .coded true ∧ m = k) ∨
      ∃ block : Nat, role j = .auxiliary block true := by
  have hKept := numericRetainedPlan_positive_member_kept
    K k N cap role v hPlan hPositive
  obtain ⟨_hBelow, b, g, hg, hCanonical, hRole⟩ :=
    (mem_numericRetainedOriginals_iff k N
      ((finiteNumericH K k N).freeLevel cap.val) role v).1 hKept
  obtain ⟨hj, hmEq⟩ := hPosition_injective_bounded
    k j m b g hm hg (hAddr.symm.trans hCanonical)
  simpa only [hj, hmEq] using hRole

/-- Every canonically retained real position below the actual cap end
belongs to the explicit finite Plan, at every retained generation. -/
theorem numericRetainedPlan_contains_real
    {db du dd : Nat} (K : AgeTestModel db du dd)
    (k N : Nat) (cap : Fin N) (role : Nat → ResolvedQBaseRole)
    (b g : Nat) (hg : g ≤ k)
    (hBelow : hPosition k b g < (finiteNumericH K k N).freeLevel cap.val)
    (hRole : (role b = .coded true ∧ g = k) ∨
      ∃ block : Nat, role b = .auxiliary block true) :
    hPosition k b g ∈ numericRetainedPlan K k N cap role := by
  have hInside : hPosition k b g < N :=
    (hBelow.trans_le ((finiteNumericH K k N).freeLevel_le cap.val)).trans cap.isLt
  let v : Fin N := ⟨hPosition k b g, hInside⟩
  have hKept : v ∈ numericRetainedOriginals k N
      ((finiteNumericH K k N).freeLevel cap.val) role :=
    (mem_numericRetainedOriginals_iff k N
      ((finiteNumericH K k N).freeLevel cap.val) role v).2
        ⟨hBelow, b, g, hg, rfl, hRole⟩
  exact numericRetainedPlan_kept_position_mem K k N cap role v hKept

/-- Omission of an actual bounded real cut from the constructed Plan
excludes a retained auxiliary base. No omitted-role premise remains. -/
theorem numericRetainedPlan_omitted_real_role
    {db du dd : Nat} (K : AgeTestModel db du dd)
    (k N : Nat) (cap : Fin N) (role : Nat → ResolvedQBaseRole)
    (b g : Nat) (hg : g ≤ k)
    (hBelow : hPosition k b g < (finiteNumericH K k N).freeLevel cap.val)
    (hOmitted : hPosition k b g ∉ numericRetainedPlan K k N cap role) :
    ResolvedQOmittedBase (role b) := by
  cases hRole : role b with
  | dummy => exact Or.inl rfl
  | coded selected => exact Or.inr (Or.inl ⟨selected, rfl⟩)
  | auxiliary block retained =>
    cases retained with
    | false => exact Or.inr (Or.inr ⟨block, rfl⟩)
    | true =>
      exact False.elim (hOmitted (numericRetainedPlan_contains_real
        K k N cap role b g hg hBelow (Or.inr ⟨block, hRole⟩)))

/-- A cap's actual bounded dummy-base presentation supplies the entire
bounded root-role contract for the singleton physical root pool. -/
theorem numericRetainedPlan_dummy_cap_root_role
    (k N : Nat) (cap : Fin N) (role : Nat → ResolvedQBaseRole)
    (b g : Nat) (hg : g ≤ k)
    (hCap : cap.val = hPosition k b g) (hDummy : role b = .dummy) :
    ∀ v : Fin N, v ∈ ({cap} : Finset (Fin N)) →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m → role j = .dummy := by
  intro v hv j m hm hAddr
  have hvCap : v = cap := Finset.mem_singleton.mp hv
  subst v
  have hBase :=
    (hPosition_injective_bounded k j m b g hm hg (hAddr.symm.trans hCap)).1
  rw [hBase]
  exact hDummy

/-- On the actual enlarged planned-prefix-seed run, an omitted ODD cut
is unselected and noninteresting on its full genuine pre-cut closure.
The explicit Plan discharges root closure, Plan closure, finite-cut and
initial-seed absence conditions. Only true higher-stage inclusion and
the displayed Henson hypotheses remain.
-/
theorem henson_numericRetainedPlan_odd_run_skip
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N : Nat) (cap : Fin N) (role : Nat → ResolvedQBaseRole)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell))
      (plannedPrefixSeeds
        ((finiteNumericH (normalizedGraphModel E) k N).kptOriginal
          (hensonForbiddenFamily ell hell) hAvoid cap)
        (numericRetainedPlan (normalizedGraphModel E) k N cap role : Set Nat))
      ((finiteNumericH (normalizedGraphModel E) k N).freeLevel cap.val))
    (a : Nat)
    (hBelow : 2*a+1 < (finiteNumericH (normalizedGraphModel E) k N).freeLevel cap.val)
    (hAbove : Run.I ((2*a+1)+1) ⊆
      (numericRetainedPlan (normalizedGraphModel E) k N cap role : Set Nat))
    (hOmitted : 2*a+1 ∉ numericRetainedPlan (normalizedGraphModel E) k N cap role) :
    2*a+1 ∉ Run.I 0 ∧
      ¬ SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree (hensonForbiddenFamily ell hell))
        (SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily ell hell))
          (Run.I ((2*a+1)+1))
          (plannedPrefixSeeds
            ((finiteNumericH (normalizedGraphModel E) k N).kptOriginal
              (hensonForbiddenFamily ell hell) hAvoid cap)
            (numericRetainedPlan (normalizedGraphModel E) k N cap role : Set Nat)))
        (2*a+1) := by
  classical
  let family := hensonForbiddenFamily ell hell
  let K := normalizedGraphModel E
  let A := finiteNumericH K k N
  let Plan : Set Nat := numericRetainedPlan K k N cap role
  let U : Finset (Fin N) := {cap}
  let X := plannedPrefixSeeds (A.kptOriginal family hAvoid cap) Plan
  let top := A.freeLevel cap.val
  have hX : X ⊆ ambientPrefixPool family A hAvoid (U : Set (Fin N)) := by
    intro z hz
    refine ⟨A.kptOriginal family hAvoid cap, ⟨cap, ?_, rfl⟩, hz.1⟩
    exact Finset.mem_singleton_self cap
  have hTopMem : top ∈ Plan := numericRetainedPlan_cap_end_mem K k N cap role
  have hTop : ∃ z ∈ X, LevelTree.lev z = top := by
    refine ⟨A.kptOriginal family hAvoid cap, ?_, rfl⟩
    exact ⟨le_rfl, hTopMem⟩
  have hCut : 2*a+1 < N :=
    (hBelow.trans_le (A.freeLevel_le cap.val)).trans cap.isLt
  have hRootClosed : ∀ v : Fin N, v ∈ U →
      A.freeLevel v.val = 0 ∨ A.freeLevel v.val ∈ Plan := by
    intro v hv
    have hvCap : v = cap := by simpa only [U, Finset.mem_singleton] using hv
    subst v
    exact Or.inr hTopMem
  have hPlanClosed : ∀ v : Fin N, v.val ∈ Plan →
      0 < A.freeLevel v.val → A.freeLevel v.val ∈ Plan := by
    intro v hv _hPositive
    exact numericRetainedPlan_free_closed K k N cap role v hv
  have hNoSeed : ¬ ∃ z ∈ X, LevelTree.lev z = 2*a+1 :=
    plannedPrefixSeeds_no_seed_outside
      (A.kptOriginal family hAvoid cap) Plan (2*a+1) hOmitted
  have hUnselected : 2*a+1 ∉ Run.I 0 :=
    henson_actualRun_odd_omitted_of_closed_plan
      ell hell k hK E hLoops hSym hClique
      N U hAvoid X hX top Run hTop a hBelow hCut
      Plan hAbove hRootClosed hPlanClosed hOmitted hNoSeed
  refine ⟨hUnselected, ?_⟩
  intro hInteresting
  have hSelected : 2*a+1 ∈ Run.I (2*a+1) := by
    rw [(Run.interesting_step (2*a+1) hBelow hInteresting).1]
    exact Set.mem_insert _ _
  rw [Run.I_eq_final_tail_of_run (2*a+1) (Nat.le_of_lt hBelow)] at hSelected
  exact hUnselected hSelected.1

end Kk
