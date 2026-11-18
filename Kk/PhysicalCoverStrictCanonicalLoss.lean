import Kk.PhysicalCoverAnchorCriticality
import Kk.PreservedTypedNeutralGap
import Kk.IsolatedSupportCanonicalAge
import Mathlib.Tactic

/-!
# Track B: a physical cover's fully linked positive successor forces CANONICAL loss

English proof and twelve hostile checks were committed BEFORE Lean:
docs/track_b_strict_postcover_canonical_loss_english_audit.md

The previous physical Track B theorem proved that a later original
fully linked to a real post-cover maximum reserved clique is RAW
critical. Raw criticality does not usually force a canonical change.
But at the distinguished support T of a GENUINE canonical cover,
the post-cover RAW bound itself equals its CANONICAL age lower(T).

A later original v fully linked to every member of Q, with complete
future T-positive bits, joins Q to a directed clique of size r+1
in the ENTIRE actual original common-neighbourhood [0,v+1).
Thus the new RAW T-bound is at most lower(T)-1; the new canonical
T-age is STRICTLY smaller than lower(T). No no-gap or K_ell-free
safety hypothesis is required. This is not an exact one-cover drop,
does not give a joint infinite selected embedding, and does not
verify dependent Kpt E/L+ B3 or a labelled inverse-source orbit.
-/

namespace Kk

/-- A physical directed clique Q below F and a later original v>=F
with BOTH-direction links to every q in Q, all with complete positive
future typed columns on T, force a raw support-T upper bound
ell-1-(|Q|+1) over the ENTIRE actual original prefix [0,v+1).

No assumption on any original gap F<=p<v: those vertices can only
enlarge the true common-neighbour pool, not destroy the clique. -/
theorem positive_clique_and_later_full_link_raw_upper_bound
    (E : Nat → Nat → Bool) (ell d F v : Nat)
    (cNext : Nat → Fin d → Bool)
    (T : IntegerGraphSupport d ell)
    (Q : Finset Nat)
    (hQBefore : ∀ q ∈ Q, q < F)
    (hQClique : IsDirectedCliqueOn E Q)
    (hAfter : F ≤ v)
    (hQPositive : ∀ q ∈ Q, ∀ t ∈ T.1, cNext q t = true)
    (hVPositive : ∀ t ∈ T.1, cNext v t = true)
    (hLinks : ∀ q ∈ Q, E q v = true ∧ E v q = true) :
    finiteOldColumnRawBound E ell d (Finset.range (v+1)) cNext T ≤
      ell - 1 - (Q.card + 1) := by
  classical
  have hvNotQ : v ∉ Q := by
    intro hvq
    have hvBefore := hQBefore v hvq
    omega
  have hBigClique : IsDirectedCliqueOn E (insert v Q) := by
    intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with hxV | hxQ
    · subst x
      rcases Finset.mem_insert.mp hy with hyV | hyQ
      · subst y
        exact False.elim (hxy rfl)
      · exact (hLinks y hyQ).2
    · rcases Finset.mem_insert.mp hy with hyV | hyQ
      · subst y
        exact (hLinks x hxQ).1
      · exact hQClique x hxQ y hyQ hxy
  have hBigSubset :
      insert v Q ⊆
        oldSupportCommonNeighbourPool
          (Finset.range (v+1)) cNext T.1 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hxV | hxQ
    · subst x
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hVPositive⟩
    · have hxBefore := hQBefore x hxQ
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hQPositive x hxQ⟩
  have hCapacity :
      (insert v Q).card ≤
        finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool
            (Finset.range (v+1)) cNext T.1) :=
    directedClique_card_le_capacity E
      (oldSupportCommonNeighbourPool (Finset.range (v+1)) cNext T.1)
      (insert v Q) hBigSubset hBigClique
  have hSize : (insert v Q).card = Q.card + 1 := by
    simp [hvNotQ]
  change ell - 1 -
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool
          (Finset.range (v+1)) cNext T.1) ≤
    ell - 1 - (Q.card + 1)
  omega

/-- Under the full genuine physical canonical-cover hypotheses,
ANY later original v linked in BOTH E directions to all of the real
reserved Q, positive on all of T and retaining all previous typed
prefix bits, forces a STRICT drop of the *CANONICAL* T-age over
the TRUE physical prefix [0,v+1), even with arbitrary intervening
original gaps.

The old canonical entire age at F is DERIVED to be lower from
the existing isolated-block and physical-gap theorems, rather than
assumed. No 'one further cover' conclusion is made: coupled witness
constraints may cause a larger canonical jump. -/
theorem real_cover_later_full_link_forces_strict_canonical_T_drop
    (E : Nat → Nat → Bool) (ell d b F r : Nat)
    (c cNext : Nat → Fin d → Bool)
    (T : IntegerGraphSupport d ell)
    (Q : Finset Nat)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hBF : b ≤ F)
    (hWithin : ∀ q ∈ Q, b ≤ q ∧ q < F)
    (hClique : IsDirectedCliqueOn E Q)
    (hCard : Q.card = r)
    (hIso : ∀ p, p < b → ∀ q ∈ Q,
      E p q = false ∧ E q p = false)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (hEll : ell = lower T + r + 1)
    (hAt : upper T = lower T + 1)
    (hPrior : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) = upper)
    (v : Nat) (hAfter : F ≤ v)
    (hPrefix : ∀ p, p < F → ∀ t,
      cNext p t = supportBlockGappedColumn b Q T.1 c p t)
    (hVPositive : ∀ t ∈ T.1, cNext v t = true)
    (hLinks : ∀ q ∈ Q, E q v = true ∧ E v q = true) :
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d
        (Finset.range (v+1)) cNext) T <
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d
          (Finset.range F) cNext) T ∧
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d
        (Finset.range F) cNext) = lower := by
  classical
  have hDisjoint : Disjoint (Finset.range b) Q := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hpB := Finset.mem_range.mp hp
    have hqb := (hWithin p hq).1
    omega
  have hZero : ∀ p ∈ Finset.range b, ∀ q ∈ Q,
      E p q = false := by
    intro p hp q hq
    exact (hIso p (Finset.mem_range.mp hp) q hq).1
  have hCapQ : finiteDirectedCliqueCapacity E Q = r := by
    rw [isolatedReservedClique_capacity_eq_card E Q hClique]
    exact hCard
  have hIdeal := isolatedSupportCanonicalAge_cover_step
    E ell d r (Finset.range b) Q hDisjoint hZero c T
    lower upper hCover hEll hAt hPrior (le_of_eq hCapQ)
  have hIdealAge :
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d
          (Finset.range b ∪ Q)
          (supportBlockOldColumn Q T.1 c)) = lower := by
    simpa only [hCapQ, if_neg (lt_irrefl r)] using hIdeal
  have hPhysicalAge :
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d
          (Finset.range F)
          (supportBlockGappedColumn b Q T.1 c)) = lower :=
    (supportBlockGappedCanonicalAge_eq
      E ell d b F hBF Q hWithin T c).trans hIdealAge
  have hBeforeAge :
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d
          (Finset.range F) cNext) = lower :=
    (integerGraphAgeCanonical_eq_of_column_prefix
      E ell d F cNext
      (supportBlockGappedColumn b Q T.1 c) hPrefix).trans
      hPhysicalAge
  have hQPositive : ∀ q ∈ Q, ∀ t ∈ T.1,
      cNext q t = true := by
    intro q hq t ht
    rw [hPrefix q (hWithin q hq).2 t]
    simp [supportBlockGappedColumn, supportBlockOldColumn, hq, ht]
  have hNewRawBound :=
    positive_clique_and_later_full_link_raw_upper_bound
      E ell d F v cNext T Q
      (fun q hq => (hWithin q hq).2)
      hClique hAfter hQPositive hVPositive hLinks
  have hTBound :
      finiteOldColumnRawBound E ell d
        (Finset.range (v+1)) cNext T ≤ lower T - 1 := by
    rw [hCard] at hNewRawBound
    omega
  have hCanLe :=
    (integerGraphAgeCanonical_le_raw d ell
      (finiteOldColumnRawBound E ell d
        (Finset.range (v+1)) cNext)) T
  have hLowerPos : 1 ≤ lower T := (hCover.lower_age.1 T).1
  have hStrict :
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d
          (Finset.range (v+1)) cNext) T < lower T := by
    omega
  constructor
  · rw [hBeforeAge]
    exact hStrict
  · exact hBeforeAge

#print axioms Kk.positive_clique_and_later_full_link_raw_upper_bound
#print axioms Kk.real_cover_later_full_link_forces_strict_canonical_T_drop

end Kk
