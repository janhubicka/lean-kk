import Kk.PhysicalCanonicalCoverStage
import Mathlib.Tactic

/-!
# Track B: true positive Henson-original neutral clique blocks, anchored by old capacity

English proof and hostile counterexample audit were committed BEFORE Lean in
docs/track_b_anchored_positive_neutral_block_english_audit.md.

An isolated new original clique Q with complete positive future sort
support T does NOT automatically lower the whole old-column age:
if its actual directed-clique capacity is bounded by the old
common-neighbour capacity at the FULL support T, then the entire
literal raw age (all supports) remains IDENTICAL. This uses the
verified exact max formula, including all proper sub-supports.

A genuine old directed clique R, positive to all of T, with
|Q| <= |R| is a simple physical certificate. Under actual Henson
avoidance and left density, one can construct the entire new
clique Q in the unchanged original E, with all physical gap columns,
and one complete finite positive T top stage. This supplies a REAL
positive age-neutral block, not a zero-tail fake.

No selected future of an earlier construction is identified with Q,
no coherent unbounded resolution or dependent Kpt/B3 labelled
inverse-source orbit is inferred.
-/

namespace Kk

/-- A genuine isolated support-T block of clique capacity no larger
than the entire old common-neighbour capacity at T preserves
the WHOLE literal raw age. Nonempty supported U ⊆ T has
X(T) ⊆ X(U): reversing this inclusion would be invalid. -/
theorem supportBlockRawBound_eq_of_dominated_capacity
    (E : Nat → Nat → Bool) (ell d : Nat)
    (P Q : Finset Nat) (hDisjoint : Disjoint P Q)
    (hZero : ∀ p ∈ P, ∀ q ∈ Q, E p q = false)
    (c : Nat → Fin d → Bool)
    (T : IntegerGraphSupport d ell)
    (hDom : finiteDirectedCliqueCapacity E Q ≤
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool P c T.1)) :
    finiteOldColumnRawBound E ell d (P ∪ Q)
        (supportBlockOldColumn Q T.1 c) =
      finiteOldColumnRawBound E ell d P c := by
  classical
  funext U
  rw [supportBlockRawBound_exact E ell d P Q hDisjoint hZero c T U]
  by_cases hSub : U.1 ⊆ T.1
  · have hPool : oldSupportCommonNeighbourPool P c T.1 ⊆
        oldSupportCommonNeighbourPool P c U.1 := by
      intro p hp
      obtain ⟨hpP, hAll⟩ := Finset.mem_filter.mp hp
      apply Finset.mem_filter.mpr
      refine ⟨hpP, ?_⟩
      intro t ht
      exact hAll t (hSub ht)
    have hCap : finiteDirectedCliqueCapacity E Q ≤
        finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool P c U.1) :=
      hDom.trans (finiteDirectedCliqueCapacity_mono E _ _ hPool)
    simp only [if_pos hSub, max_eq_left hCap]
    rfl
  · simp only [if_neg hSub]
    rfl

/-- A PRE-EXISTING physical directed clique R entirely positive on T
dominates the capacity of any new genuine directed clique Q of
cardinality at most |R|. This is a source-level sufficient
certificate, not a statement about canonical ages alone. -/
theorem anchored_old_clique_dominates_new_capacity
    (E : Nat → Nat → Bool) (ell d : Nat)
    (P R Q : Finset Nat)
    (c : Nat → Fin d → Bool)
    (T : IntegerGraphSupport d ell)
    (hRSub : R ⊆ P)
    (hRPositive : ∀ p ∈ R, ∀ t ∈ T.1, c p t = true)
    (hRClique : IsDirectedCliqueOn E R)
    (hQClique : IsDirectedCliqueOn E Q)
    (hCard : Q.card ≤ R.card) :
    finiteDirectedCliqueCapacity E Q ≤
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool P c T.1) := by
  have hRPool : R ⊆ oldSupportCommonNeighbourPool P c T.1 := by
    intro p hp
    exact Finset.mem_filter.mpr
      ⟨hRSub hp, hRPositive p hp⟩
  calc
    finiteDirectedCliqueCapacity E Q = Q.card :=
      isolatedReservedClique_capacity_eq_card E Q hQClique
    _ ≤ R.card := hCard
    _ = finiteDirectedCliqueCapacity E R :=
      (isolatedReservedClique_capacity_eq_card E R hRClique).symm
    _ ≤ finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool P c T.1) :=
      finiteDirectedCliqueCapacity_mono E _ _ hRPool

/-- The exact raw and canonical age of the original prefix does
not change after a real physically isolated support-T clique block
with a sufficiently large old positive anchor clique R. -/
theorem supportBlockGappedRawAndCanonical_eq_of_anchor
    (E : Nat → Nat → Bool) (ell d b F : Nat)
    (hBF : b ≤ F)
    (R Q : Finset Nat)
    (hRWithin : R ⊆ Finset.range b)
    (hRClique : IsDirectedCliqueOn E R)
    (hQWithin : ∀ q ∈ Q, b ≤ q ∧ q < F)
    (hQClique : IsDirectedCliqueOn E Q)
    (hQIsolated : ∀ p, p < b → ∀ q ∈ Q,
      E p q = false ∧ E q p = false)
    (c : Nat → Fin d → Bool)
    (T : IntegerGraphSupport d ell)
    (hRPositive : ∀ p ∈ R, ∀ t ∈ T.1, c p t = true)
    (hCard : Q.card ≤ R.card) :
    finiteOldColumnRawBound E ell d (Finset.range F)
        (supportBlockGappedColumn b Q T.1 c) =
      finiteOldColumnRawBound E ell d (Finset.range b) c ∧
    integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range F)
          (supportBlockGappedColumn b Q T.1 c)) =
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range b) c) := by
  classical
  have hDisjoint : Disjoint (Finset.range b) Q := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hpB := Finset.mem_range.mp hp
    have hqb := (hQWithin p hq).1
    omega
  have hZero : ∀ p ∈ Finset.range b, ∀ q ∈ Q,
      E p q = false := by
    intro p hp q hq
    exact (hQIsolated p (Finset.mem_range.mp hp) q hq).1
  have hDom := anchored_old_clique_dominates_new_capacity
    E ell d (Finset.range b) R Q c T
    hRWithin hRPositive hRClique hQClique hCard
  have hRaw : finiteOldColumnRawBound E ell d (Finset.range F)
        (supportBlockGappedColumn b Q T.1 c) =
      finiteOldColumnRawBound E ell d (Finset.range b) c := by
    calc
      _ = finiteOldColumnRawBound E ell d
          (Finset.range b ∪ Q) (supportBlockOldColumn Q T.1 c) :=
        supportBlockGappedRawBound_eq E ell d b F hBF Q hQWithin T c
      _ = finiteOldColumnRawBound E ell d (Finset.range b) c :=
        supportBlockRawBound_eq_of_dominated_capacity
          E ell d (Finset.range b) Q hDisjoint hZero c T hDom
  exact ⟨hRaw, by rw [hRaw]⟩

/-- GENUINE Henson existence of an isolated positive-T clique Q
with 0 < |Q| = r ≤ |R|, where the PRE-EXISTING old clique R
is already positive on T. Q is a real later original block
in the same E, and the complete gap-inclusive future column
has literally the original full raw/canonical age.

The positive top-stage finite numerical-H witness is genuine but
not asserted coherent with earlier selected future witnesses. -/
theorem henson_leftDense_exists_anchored_positive_neutral_block
    (d ell b k r : Nat)
    (hell : 2 ≤ ell) (hd : 0 < d)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool)
    (T : IntegerGraphSupport d ell)
    (R : Finset Nat)
    (hRWithin : R ⊆ Finset.range b)
    (hRClique : IsDirectedCliqueOn E R)
    (hRPositive : ∀ p ∈ R, ∀ t ∈ T.1, c p t = true)
    (hrPos : 0 < r) (hrLe : r ≤ R.card) (hrEll : r < ell) :
    ∃ (Q : Finset Nat) (F : Nat),
      Q.card = r ∧
      (∀ q ∈ Q, b ≤ q ∧ q < F) ∧
      IsDirectedCliqueOn E Q ∧
      (∀ p, p < b → ∀ q ∈ Q,
        E p q = false ∧ E q p = false) ∧
      finiteOldColumnRawBound E ell d (Finset.range F)
          (supportBlockGappedColumn b Q T.1 c) =
        finiteOldColumnRawBound E ell d (Finset.range b) c ∧
      integerGraphAgeCanonical d ell
          (finiteOldColumnRawBound E ell d (Finset.range F)
            (supportBlockGappedColumn b Q T.1 c)) =
        integerGraphAgeCanonical d ell
          (finiteOldColumnRawBound E ell d (Finset.range b) c) ∧
      HasUniformPositiveSupportStage E d ell b F k hd c Q T := by
  classical
  obtain ⟨Q, F, hCard, hWithin, hClique, hIso, hStage⟩ :=
    henson_leftDense_exists_uniform_finite_support_stage
      d ell b k r hell hd hrEll E hAvoid hDense c T
  have hQNonempty : Q.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨q, hq⟩ := hQNonempty
  have hBF : b ≤ F :=
    (hWithin q hq).1.trans (Nat.le_of_lt (hWithin q hq).2)
  have hSmall : Q.card ≤ R.card := by omega
  obtain ⟨hRaw, hCanonical⟩ :=
    supportBlockGappedRawAndCanonical_eq_of_anchor
      E ell d b F hBF R Q hRWithin hRClique
      hWithin hClique hIso c T hRPositive hSmall
  exact ⟨Q, F, hCard, hWithin, hClique, hIso,
    hRaw, hCanonical, hStage⟩

#print axioms Kk.supportBlockRawBound_eq_of_dominated_capacity
#print axioms Kk.anchored_old_clique_dominates_new_capacity
#print axioms Kk.supportBlockGappedRawAndCanonical_eq_of_anchor
#print axioms Kk.henson_leftDense_exists_anchored_positive_neutral_block

end Kk
