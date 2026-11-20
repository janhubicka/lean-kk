import Kk.PhysicalCanonicalSortTransport
import Kk.PhysicalPointedContinuation
import Kk.HensonLeftDensityAge
import Mathlib.Tactic

/-!
# A constructed free pivot preserves the complete canonical age

English proof and hostile audit were committed before this source in
`docs/track_b_physical_free_split_english_audit.md`.

The old prefix contains EVERY protected active/reserved original. A fresh
pivot has no old neighbours; only genuinely new gap originals get zero
future columns. The full mixed-support budgets are derived from this
geometry and canonical caps. For one positive daughter, a single nonmaximal
parent cap suffices. The last theorem constructs the pivot and one complete
finite numerical-Henson future in the same fixed graph.

No auxiliary Kpt source or global diary/orbit theorem is asserted.
-/

namespace Kk

/-- An actual pivot with no old neighbours imposes exactly the cap ell-2
on every all-positive new support. The full old columns are retained and
the actual prefix includes every gap original. -/
theorem freePointedContinuation_raw_eq {d e ell : Nat}
    (E : Nat → Nat → Bool) (b v H : Nat) (hell : 2 ≤ ell)
    (c : Nat → Fin d → Bool) (pi : Fin e → Fin d)
    (beta : Fin e → Bool) (hbv : b ≤ v) (hvH : v < H)
    (hFree : ∀ p, p < b → E p v = false ∧ E v p = false)
    (U : IntegerGraphSupport e ell) :
    finiteOldColumnRawBound E ell e (Finset.range H)
        (pointedContinuationColumn b v c pi beta) U =
      if ∀ u ∈ U.1, beta u = true then
        min (finiteOldColumnRawBound E ell d (Finset.range b) c
          (integerGraphSupportImage pi U)) (ell - 2)
      else finiteOldColumnRawBound E ell d (Finset.range b) c
        (integerGraphSupportImage pi U) := by
  classical
  let X := oldSupportCommonNeighbourPool (Finset.range b) c (U.1.image pi)
  have hvNot : v ∉ X := by
    intro hv
    have hvb := Finset.mem_range.mp (Finset.mem_filter.mp hv).1
    omega
  have hEmpty : mutualLinkedNeighbours E X v = ∅ := by
    ext p
    constructor
    · intro hp
      obtain ⟨hpX, hpv, _⟩ := Finset.mem_filter.mp hp
      have hpb := Finset.mem_range.mp (Finset.mem_filter.mp hpX).1
      rw [(hFree p hpb).1] at hpv
      cases hpv
    · simp
  unfold finiteOldColumnRawBound
  rw [pointedContinuation_common_pool b v H c pi beta hbv hvH U.1 U.2.1]
  by_cases hAll : ∀ u ∈ U.1, beta u = true
  · simp only [if_pos hAll]
    change ell - 1 - finiteDirectedCliqueCapacity E (insert v X) =
      min (ell - 1 - finiteDirectedCliqueCapacity E X) (ell - 2)
    rw [finiteDirectedCliqueCapacity_insert_eq E X v hvNot,
      hEmpty, finiteDirectedCliqueCapacity_empty]
    omega
  · simp only [if_neg hAll]
    rfl

/-- A zero-old-neighbour pivot has no extra canonical effect when the
genuine old age already meets its all-positive support caps. No independent
all-support clique-capacity budget is assumed here. -/
theorem freePointedContinuation_canonical_eq {d e ell : Nat}
    (E : Nat → Nat → Bool) (b v H : Nat) (hell : 2 ≤ ell)
    (c : Nat → Fin d → Bool) (pi : Fin e → Fin d)
    (beta : Fin e → Bool) (hbv : b ≤ v) (hvH : v < H)
    (hFree : ∀ p, p < b → E p v = false ∧ E v p = false)
    (F : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell F)
    (hOld : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) = F)
    (hSafe : ∀ U : IntegerGraphSupport e ell,
      (∀ u ∈ U.1, beta u = true) →
        F (integerGraphSupportImage pi U) ≤ ell - 2) :
    integerGraphAgeCanonical e ell
        (finiteOldColumnRawBound E ell e (Finset.range H)
          (pointedContinuationColumn b v c pi beta)) =
      fun U => F (integerGraphSupportImage pi U) := by
  classical
  let B := finiteOldColumnRawBound E ell e (Finset.range b)
    (fun p u => c p (pi u))
  let Bnew := finiteOldColumnRawBound E ell e (Finset.range H)
    (pointedContinuationColumn b v c pi beta)
  let F' := fun U => F (integerGraphSupportImage pi U)
  have hPos : 0 < ell := by omega
  have hAge' : IsIntegerGraphAge e ell F' :=
    isIntegerGraphAge_pullback pi hPos F hAge
  have hBase : integerGraphAgeCanonical e ell B = F' := by
    funext U
    calc
      integerGraphAgeCanonical e ell B U =
          integerGraphAgeCanonical d ell
            (finiteOldColumnRawBound E ell d (Finset.range b) c)
            (integerGraphSupportImage pi U) :=
        finiteOldColumnCanonical_reindex E (Finset.range b) c pi hPos U
      _ = F' U := by rw [hOld]
  have hRaw : ∀ U, Bnew U =
      if ∀ u ∈ U.1, beta u = true then
        min (B U) (ell - 2) else B U := by
    intro U
    rw [show B U = finiteOldColumnRawBound E ell d (Finset.range b) c
        (integerGraphSupportImage pi U) from
      finiteOldColumnRawBound_reindex E (Finset.range b) c pi U]
    exact freePointedContinuation_raw_eq E b v H hell c pi beta hbv hvH hFree U
  have hBelow : AgeLe F' Bnew := by
    intro U
    have hFB : F' U ≤ B U := by
      rw [← hBase]
      exact integerGraphAgeCanonical_le_raw e ell B U
    rw [hRaw U]
    by_cases hAll : ∀ u ∈ U.1, beta u = true
    · simp only [if_pos hAll]
      exact le_min hFB (hSafe U hAll)
    · simpa only [if_neg hAll] using hFB
  have hNewLe : AgeLe Bnew B := by
    intro U
    rw [hRaw U]
    split_ifs
    · exact min_le_left _ _
    · exact le_rfl
  have hNewAge := integerGraphAgeCanonical_is_age e ell Bnew F' hAge' hBelow
  have hLower := integerGraphAgeCanonical_greatest e ell Bnew F' hAge' hBelow
  have hUpper : AgeLe (integerGraphAgeCanonical e ell Bnew) F' := by
    rw [← hBase]
    apply integerGraphAgeCanonical_greatest e ell B
      (integerGraphAgeCanonical e ell Bnew) hNewAge
    intro U
    exact (integerGraphAgeCanonical_le_raw e ell Bnew U).trans (hNewLe U)
  funext U
  exact Nat.le_antisymm (hUpper U) (hLower U)

/-- One positive daughter of a nonmaximal parent preserves the entire
canonical age, including every mixed support and repeated parent labels.
The only new numerical premise is the SINGLE parent's nonmaximal age. -/
theorem freeSplit_canonical_eq {d e ell : Nat}
    (E : Nat → Nat → Bool) (b v H : Nat) (hell : 2 ≤ ell)
    (c : Nat → Fin d → Bool) (pi : Fin e → Fin d) (u : Fin e)
    (hbv : b ≤ v) (hvH : v < H)
    (hFree : ∀ p, p < b → E p v = false ∧ E v p = false)
    (F : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell F)
    (hOld : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) = F)
    (hParent : F ⟨{pi u}, Finset.singleton_nonempty _, by simp; omega⟩ ≤ ell - 2) :
    integerGraphAgeCanonical e ell
        (finiteOldColumnRawBound E ell e (Finset.range H)
          (pointedContinuationColumn b v c pi (fun t => decide (t = u)))) =
      fun U => F (integerGraphSupportImage pi U) := by
  classical
  apply freePointedContinuation_canonical_eq E b v H hell c pi
    (fun t => decide (t = u)) hbv hvH hFree F hAge hOld
  intro U hAll
  have hU : U.1 = {u} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    obtain ⟨t, ht⟩ := U.2.1
    have htu : t = u := of_decide_eq_true (hAll t ht)
    refine ⟨htu ▸ ht, ?_⟩
    intro x hx
    exact of_decide_eq_true (hAll x hx)
  have hImage : integerGraphSupportImage pi U =
      ⟨{pi u}, Finset.singleton_nonempty _, by simp; omega⟩ := by
    apply Subtype.ext
    change U.1.image pi = {pi u}
    rw [hU, Finset.image_singleton]
  rw [hImage]
  exact hParent

/-- Construct a genuine free marker and its complete finite Henson future.
The old passing data on EVERY original below b are retained. One shared
embedding/cutoff fixes the entire prefix through the same new marker. -/
theorem henson_leftDense_constructs_freePointed_stage
    (E : Nat → Nat → Bool) (d e ell b k : Nat)
    (hell : 2 ≤ ell) (he : 0 < e)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool) (pi : Fin e → Fin d)
    (beta : Fin e → Bool)
    (F : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell F)
    (hOld : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) = F)
    (hSafe : ∀ U : IntegerGraphSupport e ell,
      (∀ u ∈ U.1, beta u = true) →
        F (integerGraphSupportImage pi U) ≤ ell - 2) :
    ∃ (v : Nat) (f : Nat → Nat) (M : Nat),
      b ≤ v ∧
      (∀ p, p < v → E p v = false ∧ E v p = false) ∧
      integerGraphAgeCanonical e ell
          (finiteOldColumnRawBound E ell e (Finset.range (v + 1))
            (pointedContinuationColumn b v c pi beta)) =
        (fun U => F (integerGraphSupportImage pi U)) ∧
      FiniteNumericStageWitness E e ell (v + 1) k he
        (pointedContinuationColumn b v c pi beta) f M ∧
      (∀ p, p < v + 1 → f p = p) := by
  classical
  have hCheck : finiteNeighbourCliqueCheck E b (ell - 1)
      (fun _ => false) = false := by
    apply finiteNeighbourCliqueCheck_false_of_small_neighbour_set
    have hEmpty : oldNeighbourSet b (fun _ => false) = ∅ := by
      simp [oldNeighbourSet]
    rw [hEmpty, Finset.card_empty]
    omega
  obtain ⟨v, hbv, hZero⟩ := henson_leftDense_realizes_certified_original
    ell hell E hAvoid hDense b (fun _ => false) hCheck
  have hFreeAll : ∀ p, p < v → E p v = false ∧ E v p = false := by
    intro p hp
    simpa only [ite_self] using hZero p hp
  have hFree : ∀ p, p < b → E p v = false ∧ E v p = false := by
    intro p hp
    exact hFreeAll p (by omega)
  have hCanonical := freePointedContinuation_canonical_eq E b v (v + 1)
    hell c pi beta hbv (by omega) hFree F hAge hOld hSafe
  obtain ⟨f, M, hStage⟩ := henson_leftDense_finite_numeric_stage_witness
    E e ell (v + 1) k hell he hAvoid hDense
    (pointedContinuationColumn b v c pi beta)
  have hFix : ∀ p, p < v + 1 → f p = p := hStage.1
  exact ⟨v, f, M, hbv, hFreeAll, hCanonical, hStage, hFix⟩

/-- A genuine nonmaximal free split is constructed from one parent cap,
with no separately assumed mixed-support budget or safe pivot. For the
usual two-daughter parent map this is the finite physical split step. -/
theorem henson_leftDense_constructs_freeSplit_stage
    (E : Nat → Nat → Bool) (d e ell b k : Nat)
    (hell : 2 ≤ ell) (he : 0 < e)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool) (pi : Fin e → Fin d) (u : Fin e)
    (F : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell F)
    (hOld : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) = F)
    (hParent : F ⟨{pi u}, Finset.singleton_nonempty _, by simp; omega⟩ ≤ ell - 2) :
    ∃ (v : Nat) (f : Nat → Nat) (M : Nat),
      b ≤ v ∧
      (∀ p, p < v → E p v = false ∧ E v p = false) ∧
      integerGraphAgeCanonical e ell
          (finiteOldColumnRawBound E ell e (Finset.range (v + 1))
            (pointedContinuationColumn b v c pi (fun t => decide (t = u)))) =
        (fun U => F (integerGraphSupportImage pi U)) ∧
      FiniteNumericStageWitness E e ell (v + 1) k he
        (pointedContinuationColumn b v c pi (fun t => decide (t = u))) f M ∧
      (∀ p, p < v + 1 → f p = p) := by
  classical
  apply henson_leftDense_constructs_freePointed_stage E d e ell b k
    hell he hAvoid hDense c pi (fun t => decide (t = u)) F hAge hOld
  intro U hAll
  have hU : U.1 = {u} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    obtain ⟨t, ht⟩ := U.2.1
    have htu : t = u := of_decide_eq_true (hAll t ht)
    refine ⟨htu ▸ ht, ?_⟩
    intro x hx
    exact of_decide_eq_true (hAll x hx)
  have hImage : integerGraphSupportImage pi U =
      ⟨{pi u}, Finset.singleton_nonempty _, by simp; omega⟩ := by
    apply Subtype.ext
    change U.1.image pi = {pi u}
    rw [hU, Finset.image_singleton]
  rw [hImage]
  exact hParent

end Kk
