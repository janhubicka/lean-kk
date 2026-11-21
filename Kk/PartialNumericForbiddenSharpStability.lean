import Kk.PartialNumericLateAgeStability
import Kk.FiniteOldColumnAge
import Kk.HensonEncoding
import Kk.PartialNumericCanonicalVisibleEvent
import Mathlib.Tactic

/-!
# Track A: sharply bounded support events under actual finite clique-freeness

English proof and hostile audit:
  docs/track_a_forbidden_sharp_partial_stability_english_audit_20261118.md

This module uses an actual finite forbidden-clique certificate at the
relevant original pool, not an invented abstract graph-age assumption.
The module derives each finite no-clique certificate directly from
Henson's normalized forbidden-family avoidance.
No dependent Kpt E/B3 or global BRD claim.
-/

namespace Kk

open SuccessorTree.V10


/-- Every finite original pool really is K_ell-free if the actual
normalized graph avoids the full Henson forbidden family. Convert a
candidate unordered finite clique to its increasing enumeration. -/
theorem trackA_finite_pool_free_of_henson
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (P : Finset Nat) :
    finitePoolCliqueCheck E ell P = false := by
  classical
  have hNoClique :=
    hensonForbiddenFamily_no_cliques ell hell E hAvoid
  apply (finitePoolCliqueCheck_false_iff E ell P).2
  rintro ⟨s, hsP, hsCard, hsClique⟩
  let f : Fin ell ↪o Nat := s.orderEmbOfFin hsCard
  apply hNoClique
  refine ⟨f, f.strictMono, ?_⟩
  intro a b hab
  exact hsClique (f a) (s.orderEmbOfFin_mem hsCard a)
    (f b) (s.orderEmbOfFin_mem hsCard b)
    (f.injective.ne hab)

/-- A finite set S of original vertices all before b, linked to b
and to one later vertex t, with b linked to t, has capacity at most
ell-3 when the actual pool S ∪ {b,t} is K_ell-free.
This is a finite *actual graph* argument, not arithmetic on raw ages. -/
theorem trackA_linked_clique_capacity_two_vertex_budget
    (E : Nat → Nat → Bool)
    (hSym : ∀ x y, E x y = E y x)
    (ell b t : Nat) (S : Finset Nat)
    (hBefore : ∀ x ∈ S, x < b)
    (hbt : b < t)
    (hLinkB : ∀ x ∈ S, E x b = true)
    (hLinkT : ∀ x ∈ S, E x t = true)
    (hBtEdge : E b t = true)
    (hFree : finitePoolCliqueCheck E ell
      (insert t (insert b S)) = false) :
    finiteDirectedCliqueCapacity E S + 2 < ell := by
  classical
  obtain ⟨C,hSub,hClique,hCard⟩ :=
    finiteDirectedCliqueCapacity_attained E S
  have hbNot : b ∉ C := by
    intro hb
    exact (Nat.lt_irrefl b) (hBefore b (hSub hb))
  have htNot : t ∉ C := by
    intro ht
    have h := hBefore t (hSub ht)
    omega
  have hBt : b ≠ t := ne_of_lt hbt
  let D : Finset Nat := insert t (insert b C)
  have hSubD : D ⊆ insert t (insert b S) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · simp
    rcases Finset.mem_insert.mp hx with rfl | hx
    · simp
    · exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (hSub hx))
  have hCliqueD : IsDirectedCliqueOn E D := by
    intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with hxT | hx
    · subst x
      rcases Finset.mem_insert.mp hy with hyT | hy
      · exact False.elim (hxy hyT.symm)
      · rcases Finset.mem_insert.mp hy with hyB | hyC
        · subst y
          simpa [hSym b t] using hBtEdge
        · exact (hSym y t).symm.trans (hLinkT y (hSub hyC))
    · rcases Finset.mem_insert.mp hx with hxB | hxC
      · subst x
        rcases Finset.mem_insert.mp hy with hyT | hy
        · subst y
          exact hBtEdge
        · rcases Finset.mem_insert.mp hy with hyB | hyC
          · exact False.elim (hxy hyB.symm)
          · exact (hSym y b).symm.trans (hLinkB y (hSub hyC))
      · rcases Finset.mem_insert.mp hy with hyT | hy
        · subst y
          exact hLinkT x (hSub hxC)
        · rcases Finset.mem_insert.mp hy with hyB | hyC
          · subst y
            exact hLinkB x (hSub hxC)
          · exact hClique x hxC y hyC hxy
  have htNotInsert : t ∉ insert b C := by
    simp [htNot, hBt.symm]
  have hCardD : D.card = C.card + 2 := by
    dsimp [D]
    rw [Finset.card_insert_of_notMem htNotInsert,
        Finset.card_insert_of_notMem hbNot] <;> omega
  have hCapacity :=
    directedClique_card_le_capacity E
      (insert t (insert b S)) D hSubD hCliqueD
  have hFreeCapacity :=
    (finitePoolCliqueCheck_false_iff_capacity_lt E ell
      (insert t (insert b S))).mp hFree
  omega

/-- Exact source-local criterion: if every eligible equal-capacity
support has a genuine finite K_ell-free two-vertex original pool,
ordinary-L raw age is constant after generation ell-2.
This is the sharp forbidden-graph specialization of general ell-1
stability, and avoids silently assuming a Kpt/B3 identification. -/
theorem trackA_partial_raw_stable_of_two_vertex_free
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ x y, E x y = E y x)
    (ell k b g h M : Nat)
    (hLate : ell - 2 ≤ g) (hgh : g ≤ h) (hh : h ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t)
    (hPoolsFree : ∀ (U : IntegerGraphSupport d ell)
      (t : Fin d), t ∈ U.1 →
      finitePoolCliqueCheck E ell
        (insert (j t)
          (insert b
            ((oldSupportCommonNeighbourPool (Finset.range b)
              (fun i z => E i (j z)) U.1).filter
                (fun i => E i b = true)))) = false) :
    finiteNumericHPartialActualRawAt E ell k b h M j =
      finiteNumericHPartialActualRawAt E ell k b g M j := by
  classical
  funext U
  have hMono :
      finiteNumericHPartialActualRawAt E ell k b h M j U ≤
        finiteNumericHPartialActualRawAt E ell k b g M j U :=
    finiteNumericH_partial_actual_raw_age_antitone
      E ell k b M g h hgh j U
  by_contra hNe
  have hStrict :
      finiteNumericHPartialActualRawAt E ell k b h M j U <
        finiteNumericHPartialActualRawAt E ell k b g M j U := by
    omega
  obtain ⟨hEligible,hCapacity,hCut,_,_⟩ :=
    (finiteNumericH_partial_actual_raw_support_event_iff
      E hSym ell k b g h M hgh hh j hj U).mp hStrict
  obtain ⟨t, ht⟩ := U.2.1
  let P : Finset Nat :=
    oldSupportCommonNeighbourPool (Finset.range b)
      (fun i z => E i (j z)) U.1
  let S : Finset Nat := P.filter (fun i => E i b = true)
  have hBefore : ∀ x ∈ S, x < b := by
    intro x hx
    exact Finset.mem_range.mp
      (Finset.mem_filter.mp
        ((Finset.mem_filter.mp hx).1)).1
  have hLinkB : ∀ x ∈ S, E x b = true := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hLinkT : ∀ x ∈ S, E x (j t) = true := by
    intro x hx
    exact (Finset.mem_filter.mp
      ((Finset.mem_filter.mp hx).1)).2 t ht
  have hFree : finitePoolCliqueCheck E ell
      (insert (j t) (insert b S)) = false :=
    hPoolsFree U t ht
  have hBound := trackA_linked_clique_capacity_two_vertex_budget
    E hSym ell b (j t) S hBefore (hj t)
    hLinkB hLinkT (hEligible t ht) hFree
  change finiteDirectedCliqueCapacity E S =
    finiteDirectedCliqueCapacity E P at hCapacity
  change g ≤ finiteDirectedCliqueCapacity E P at hCut
  omega

/-- Canonical ordinary-L ages inherit the sharp source-local
stability by rewriting the whole raw support function. -/
theorem trackA_partial_canonical_stable_of_two_vertex_free
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ x y, E x y = E y x)
    (ell k b g h M : Nat)
    (hLate : ell - 2 ≤ g) (hgh : g ≤ h) (hh : h ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t)
    (hPoolsFree : ∀ (U : IntegerGraphSupport d ell)
      (t : Fin d), t ∈ U.1 →
      finitePoolCliqueCheck E ell
        (insert (j t)
          (insert b
            ((oldSupportCommonNeighbourPool (Finset.range b)
              (fun i z => E i (j z)) U.1).filter
                (fun i => E i b = true)))) = false) :
    integerGraphAgeCanonical d ell
      (finiteNumericHPartialActualRawAt E ell k b h M j) =
    integerGraphAgeCanonical d ell
      (finiteNumericHPartialActualRawAt E ell k b g M j) := by
  rw [trackA_partial_raw_stable_of_two_vertex_free
    E hSym ell k b g h M hLate hgh hh j hj hPoolsFree]

/-- Feasible normalized integer clique vectors also stabilize. -/
theorem trackA_partial_feasible_stable_of_two_vertex_free
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ x y, E x y = E y x)
    (ell k b g h M : Nat)
    (hLate : ell - 2 ≤ g) (hgh : g ≤ h) (hh : h ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t)
    (hPoolsFree : ∀ (U : IntegerGraphSupport d ell)
      (t : Fin d), t ∈ U.1 →
      finitePoolCliqueCheck E ell
        (insert (j t)
          (insert b
            ((oldSupportCommonNeighbourPool (Finset.range b)
              (fun i z => E i (j z)) U.1).filter
                (fun i => E i b = true)))) = false) :
    feasibleIntegerCliqueVectors d ell
      (finiteNumericHPartialActualRawAt E ell k b h M j) =
    feasibleIntegerCliqueVectors d ell
      (finiteNumericHPartialActualRawAt E ell k b g M j) := by
  rw [trackA_partial_raw_stable_of_two_vertex_free
    E hSym ell k b g h M hLate hgh hh j hj hPoolsFree]


/-- The sharp stability theorem directly in the original Henson
forbidden-family interface. No separate pool-freeness premise. -/
theorem trackA_henson_partial_raw_stable_after_ell_sub_two
    {d : Nat} (E : Nat → Nat → Bool)
    (ell : Nat) (hell : 2 ≤ ell)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (k b g h M : Nat)
    (hLate : ell - 2 ≤ g) (hgh : g ≤ h) (hh : h ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t) :
    finiteNumericHPartialActualRawAt E ell k b h M j =
      finiteNumericHPartialActualRawAt E ell k b g M j := by
  have hSym := hensonForbiddenFamily_symmetric ell hell E hAvoid
  apply trackA_partial_raw_stable_of_two_vertex_free
    E hSym ell k b g h M hLate hgh hh j hj
  intro U t _
  exact trackA_finite_pool_free_of_henson ell hell E hAvoid _

theorem trackA_henson_partial_canonical_stable_after_ell_sub_two
    {d : Nat} (E : Nat → Nat → Bool)
    (ell : Nat) (hell : 2 ≤ ell)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (k b g h M : Nat)
    (hLate : ell - 2 ≤ g) (hgh : g ≤ h) (hh : h ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t) :
    integerGraphAgeCanonical d ell
      (finiteNumericHPartialActualRawAt E ell k b h M j) =
    integerGraphAgeCanonical d ell
      (finiteNumericHPartialActualRawAt E ell k b g M j) := by
  rw [trackA_henson_partial_raw_stable_after_ell_sub_two
    E ell hell hAvoid k b g h M hLate hgh hh j hj]

theorem trackA_henson_partial_feasible_stable_after_ell_sub_two
    {d : Nat} (E : Nat → Nat → Bool)
    (ell : Nat) (hell : 2 ≤ ell)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (k b g h M : Nat)
    (hLate : ell - 2 ≤ g) (hgh : g ≤ h) (hh : h ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t) :
    feasibleIntegerCliqueVectors d ell
      (finiteNumericHPartialActualRawAt E ell k b h M j) =
    feasibleIntegerCliqueVectors d ell
      (finiteNumericHPartialActualRawAt E ell k b g M j) := by
  rw [trackA_henson_partial_raw_stable_after_ell_sub_two
    E ell hell hAvoid k b g h M hLate hgh hh j hj]


/-- On a genuine Henson original graph, the old raw-event criterion
has no independent truncation clause: an eligible equal-capacity
support forces the strictly stronger p+2<ell by a real two-vertex
clique extension. This is still the literal finite ordinary-L age. -/
theorem trackA_henson_partial_raw_event_iff_simple
    {d : Nat} (E : Nat → Nat → Bool)
    (ell : Nat) (hell : 2 ≤ ell)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (k b g h M : Nat) (hgh : g ≤ h) (hh : h ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t)
    (U : IntegerGraphSupport d ell) :
    finiteNumericHPartialActualRawAt E ell k b h M j U <
      finiteNumericHPartialActualRawAt E ell k b g M j U ↔
    (∀ t ∈ U.1, E b (j t) = true) ∧
      finiteDirectedCliqueCapacity E
        ((oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1).filter
            (fun i => E i b = true)) =
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1) ∧
      g ≤ finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1) ∧
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1) < h := by
  classical
  have hSym := hensonForbiddenFamily_symmetric ell hell E hAvoid
  have hFull :=
    finiteNumericH_partial_actual_raw_support_event_iff
      E hSym ell k b g h M hgh hh j hj U
  constructor
  · intro hStrict
    obtain ⟨he,hc,hg,hh',_⟩ := hFull.mp hStrict
    exact ⟨he,hc,hg,hh'⟩
  · rintro ⟨hEligible,hCapacity,hCut,hLater⟩
    let P : Finset Nat :=
      oldSupportCommonNeighbourPool (Finset.range b)
        (fun i t => E i (j t)) U.1
    let S : Finset Nat := P.filter (fun i => E i b = true)
    obtain ⟨t,ht⟩ := U.2.1
    have hBefore : ∀ x ∈ S, x < b := by
      intro x hx
      exact Finset.mem_range.mp
        (Finset.mem_filter.mp
          ((Finset.mem_filter.mp hx).1)).1
    have hLinkB : ∀ x ∈ S, E x b = true := by
      intro x hx
      exact (Finset.mem_filter.mp hx).2
    have hLinkT : ∀ x ∈ S, E x (j t) = true := by
      intro x hx
      exact (Finset.mem_filter.mp
        ((Finset.mem_filter.mp hx).1)).2 t ht
    have hFree : finitePoolCliqueCheck E ell
        (insert (j t) (insert b S)) = false :=
      trackA_finite_pool_free_of_henson ell hell E hAvoid _
    have hBound :=
      trackA_linked_clique_capacity_two_vertex_budget
        E hSym ell b (j t) S hBefore (hj t)
        hLinkB hLinkT (hEligible t ht) hFree
    have hPositive : finiteDirectedCliqueCapacity E P < ell - 1 := by
      change finiteDirectedCliqueCapacity E S =
        finiteDirectedCliqueCapacity E P at hCapacity
      omega
    exact hFull.mpr ⟨hEligible,hCapacity,hCut,hLater,hPositive⟩


/-- For genuine K_ell-free Henson original graphs, the raw support
event at ONE partial generation step g -> g+1 occurs precisely when
the original common-neighbour capacity equals g and the actual
linked-old capacity does too. In particular each fixed support has
at most one raw event in the entire current-original block. -/
theorem trackA_henson_partial_raw_single_step_iff
    {d : Nat} (E : Nat → Nat → Bool)
    (ell : Nat) (hell : 2 ≤ ell)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (k b g M : Nat) (hg : g + 1 ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t)
    (U : IntegerGraphSupport d ell) :
    finiteNumericHPartialActualRawAt E ell k b (g + 1) M j U <
      finiteNumericHPartialActualRawAt E ell k b g M j U ↔
    (∀ t ∈ U.1, E b (j t) = true) ∧
      finiteDirectedCliqueCapacity E
        ((oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1).filter
            (fun i => E i b = true)) =
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1) ∧
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1) = g := by
  have hIff := trackA_henson_partial_raw_event_iff_simple
    E ell hell hAvoid k b g (g + 1) M (by omega) hg j hj U
  constructor
  · intro h
    obtain ⟨he,hc,hLe,hLt⟩ := hIff.mp h
    exact ⟨he,hc,by omega⟩
  · rintro ⟨he,hc,hEq⟩
    apply hIff.mpr
    refine ⟨he,hc,?_,?_⟩ <;> omega


/-- Different generations cannot both strictly lower the same genuine
Henson raw support. This is a SAME original-graph, SAME top-family,
SAME named support claim: the two genuine event witnesses would
identify their capacities with two different generation indices. -/
theorem trackA_henson_partial_raw_at_most_one_single_step
    {d : Nat} (E : Nat → Nat → Bool)
    (ell : Nat) (hell : 2 ≤ ell)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (k b g₁ g₂ M : Nat)
    (hSep : g₁ < g₂) (hFinal : g₂ + 1 ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t)
    (U : IntegerGraphSupport d ell)
    (hFirst :
      finiteNumericHPartialActualRawAt E ell k b (g₁ + 1) M j U <
        finiteNumericHPartialActualRawAt E ell k b g₁ M j U) :
    ¬ finiteNumericHPartialActualRawAt E ell k b (g₂ + 1) M j U <
        finiteNumericHPartialActualRawAt E ell k b g₂ M j U := by
  have hFirstStep :=
    (trackA_henson_partial_raw_single_step_iff
      E ell hell hAvoid k b g₁ M
        (by omega) j hj U).mp hFirst
  intro hSecond
  have hSecondStep :=
    (trackA_henson_partial_raw_single_step_iff
      E ell hell hAvoid k b g₂ M hFinal j hj U).mp hSecond
  have hEq₁ := hFirstStep.2.2
  have hEq₂ := hSecondStep.2.2
  omega


set_option maxHeartbeats 1000000

/-- Exact visibility of genuine Henson canonical ordinary-L age changes:
a globally OLD-feasible normalized clique-weight vector must saturate
a physical U-support whose linked original capacity is critical at
a cut between g and h. Unlike the general raw-event theorem, there is
NO independent Nat-subtraction saturation premise because genuine
K_ell-freeness supplies p_U+2<ell. This is not a cover assertion. -/
theorem trackA_henson_canonical_change_iff_saturating_event
    {d : Nat} (E : Nat → Nat → Bool)
    (ell : Nat) (hell : 2 ≤ ell)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (k b g h M : Nat) (hgh : g ≤ h) (hh : h ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t) :
    integerGraphAgeCanonical d ell
      (finiteNumericHPartialActualRawAt E ell k b h M j) ≠
    integerGraphAgeCanonical d ell
      (finiteNumericHPartialActualRawAt E ell k b g M j) ↔
    ∃ w : IntegerCliqueWeights d ell,
    ∃ U : IntegerGraphSupport d ell,
      WitnessRespects
        (integerCliqueOnSupport (d := d) (ell := ell))
        (finiteNumericHPartialActualRawAt E ell k b g M j) w ∧
      integerCliqueOnSupport w U =
        finiteNumericHPartialActualRawAt E ell k b g M j U ∧
      (∀ t ∈ U.1, E b (j t) = true) ∧
      finiteDirectedCliqueCapacity E
        ((oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1).filter
            (fun i => E i b = true)) =
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1) ∧
      g ≤ finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1) ∧
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1) < h := by
  classical
  have hSym := hensonForbiddenFamily_symmetric ell hell E hAvoid
  have hGeneral :=
    finiteNumericH_partial_canonical_change_iff_saturating_raw_event
      E hSym ell k b g h M hgh hh j hj
  constructor
  · intro hDifferent
    have hChange :
        integerGraphAgeCanonical d ell
          (finiteNumericHPhysicalPartialOldRaw E ell k b h M j) ≠
        integerGraphAgeCanonical d ell
          (finiteNumericHPhysicalPartialOldRaw E ell k b g M j) := hDifferent
    obtain ⟨w,U,hOld,hSat,hEligible,hCap,hCut,hLater,_⟩ :=
      hGeneral.mp hChange
    exact ⟨w,U,hOld,hSat,hEligible,hCap,hCut,hLater⟩
  · rintro ⟨w,U,hOld,hSat,hEligible,hCap,hCut,hLater⟩
    have hPhysicalEvent :
        finiteNumericHPartialActualRawAt E ell k b h M j U <
          finiteNumericHPartialActualRawAt E ell k b g M j U :=
      (trackA_henson_partial_raw_event_iff_simple
        E ell hell hAvoid k b g h M hgh hh j hj U).2
        ⟨hEligible,hCap,hCut,hLater⟩
    have hEvent :=
      (finiteNumericH_partial_actual_raw_support_event_iff
        E hSym ell k b g h M hgh hh j hj U).1 hPhysicalEvent
    exact hGeneral.mpr
      ⟨w,U,hOld,hSat,hEligible,hCap,hCut,hLater,hEvent.2.2.2.2⟩


set_option maxHeartbeats 200000

/-- The ENTIRE genuine Henson raw ordinary-L support function changes
across two partial cuts iff SOME nonempty support has the original
clique-capacity threshold between them. It is not enough to check
only singleton supports, and it makes no canonical-cover claim. -/
theorem trackA_henson_raw_function_change_iff_exists_support
    {d : Nat} (E : Nat → Nat → Bool)
    (ell : Nat) (hell : 2 ≤ ell)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (k b g h M : Nat) (hgh : g ≤ h) (hh : h ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t) :
    finiteNumericHPartialActualRawAt E ell k b h M j ≠
      finiteNumericHPartialActualRawAt E ell k b g M j ↔
    ∃ U : IntegerGraphSupport d ell,
      (∀ t ∈ U.1, E b (j t) = true) ∧
      finiteDirectedCliqueCapacity E
        ((oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1).filter
            (fun i => E i b = true)) =
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1) ∧
      g ≤ finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1) ∧
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1) < h := by
  classical
  have hSym := hensonForbiddenFamily_symmetric ell hell E hAvoid
  constructor
  · intro hDifferent
    by_contra hNone
    apply hDifferent
    funext U
    have hMono :
        finiteNumericHPartialActualRawAt E ell k b h M j U ≤
          finiteNumericHPartialActualRawAt E ell k b g M j U :=
      finiteNumericH_partial_actual_raw_age_antitone
        E ell k b M g h hgh j U
    by_contra hUnequal
    have hStrict :
        finiteNumericHPartialActualRawAt E ell k b h M j U <
          finiteNumericHPartialActualRawAt E ell k b g M j U := by
      omega
    exact hNone ⟨U,
      (trackA_henson_partial_raw_event_iff_simple
        E ell hell hAvoid k b g h M hgh hh j hj U).mp hStrict⟩
  · rintro ⟨U,hEligible,hCap,hCut,hLater⟩ hEq
    have hStrict :
        finiteNumericHPartialActualRawAt E ell k b h M j U <
          finiteNumericHPartialActualRawAt E ell k b g M j U :=
      (trackA_henson_partial_raw_event_iff_simple
        E ell hell hAvoid k b g h M hgh hh j hj U).mpr
          ⟨hEligible,hCap,hCut,hLater⟩
    rw [hEq] at hStrict
    exact (Nat.lt_irrefl _) hStrict

#print axioms Kk.trackA_henson_raw_function_change_iff_exists_support
#print axioms Kk.trackA_henson_canonical_change_iff_saturating_event
#print axioms Kk.trackA_henson_partial_raw_at_most_one_single_step
#print axioms Kk.trackA_henson_partial_raw_single_step_iff
#print axioms Kk.trackA_henson_partial_raw_event_iff_simple
#print axioms Kk.trackA_finite_pool_free_of_henson
#print axioms Kk.trackA_linked_clique_capacity_two_vertex_budget
#print axioms Kk.trackA_partial_raw_stable_of_two_vertex_free
#print axioms Kk.trackA_partial_canonical_stable_of_two_vertex_free
#print axioms Kk.trackA_partial_feasible_stable_of_two_vertex_free
#print axioms Kk.trackA_henson_partial_raw_stable_after_ell_sub_two
#print axioms Kk.trackA_henson_partial_canonical_stable_after_ell_sub_two
#print axioms Kk.trackA_henson_partial_feasible_stable_after_ell_sub_two

end Kk
