import Kk.CanonicalAgeSortPullback
import Kk.CanonicalCoverEventLocality
import Kk.IntegerAgeCoverUnitDrop
import Mathlib.Tactic

/-!
# Covers project to covers or equality on a subfront of distinct sorts

The intermediate-age lifting argument is independent of K4 and of the
number of selected vertices. Injectivity of the selected class map is
essential: duplicating a class is not restriction. The occupied classes,
not the list of possibly repeated terminal names, form the subfront.
-/

namespace Kk

theorem integerGraphSupportImage_injective {e d ell : Nat}
    (pi : Fin e → Fin d) (hi : Function.Injective pi) :
    Function.Injective (integerGraphSupportImage (ell := ell) pi) := by
  classical
  intro U V h
  have hEq : U.1.image pi = V.1.image pi := congrArg Subtype.val h
  apply Subtype.ext
  ext i
  constructor
  · intro hm
    have hmem : pi i ∈ V.1.image pi := by
      rw [← hEq]
      exact Finset.mem_image.mpr ⟨i,hm,rfl⟩
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hmem
    exact hi he ▸ hj
  · intro hm
    have hmem : pi i ∈ U.1.image pi := by
      rw [hEq]
      exact Finset.mem_image.mpr ⟨i,hm,rfl⟩
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hmem
    exact hi he ▸ hj

theorem integerGraphSupportImage_exists_of_subset {e d ell : Nat}
    (pi : Fin e → Fin d) (hi : Function.Injective pi)
    (T : IntegerGraphSupport d ell)
    (hT : T.1 ⊆ Finset.univ.image pi) :
    ∃ U : IntegerGraphSupport e ell, integerGraphSupportImage pi U = T := by
  classical
  let R := (Finset.univ : Finset (Fin e)).filter (fun i => pi i ∈ T.1)
  have hImage : R.image pi = T.1 := by
    ext j
    constructor
    · intro hj
      obtain ⟨i,hm,rfl⟩ := Finset.mem_image.mp hj
      exact (Finset.mem_filter.mp hm).2
    · intro hj
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp (hT hj)
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩,rfl⟩
  have hNE : R.Nonempty := by
    obtain ⟨j,hj⟩ := T.2.1
    have hj' : j ∈ R.image pi := by rw [hImage]; exact hj
    obtain ⟨i,hi',_⟩ := Finset.mem_image.mp hj'
    exact ⟨i,hi'⟩
  have hCard : R.card ≤ ell - 1 := by
    have hc := Finset.card_image_of_injective R hi
    rw [hImage] at hc
    rw [← hc]
    exact T.2.2
  exact ⟨⟨R,hNE,hCard⟩,Subtype.ext hImage⟩

/-- Injectivity makes the mass of an image support EXACT, not merely
an upper bound obtained by summing possibly duplicated class fibres. -/
theorem integerCliquePushforward_image_mass_eq {e d ell : Nat}
    (pi : Fin e → Fin d) (hi : Function.Injective pi) (hell : 0 < ell)
    (w : IntegerCliqueWeights e ell) (U : IntegerGraphSupport e ell) :
    integerCliqueOnSupport (integerCliquePushforward pi hell w)
        (integerGraphSupportImage pi U) = integerCliqueOnSupport w U := by
  classical
  rw [integerCliquePushforward_mass]
  have hFilter : (Finset.univ.filter
      (fun i => pi i ∈ (integerGraphSupportImage pi U).1)) = U.1 := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hm
      obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hm
      exact hi he ▸ hj
    · intro hm
      exact Finset.mem_image.mpr ⟨i,hm,rfl⟩
  rw [hFilter]
  rfl

noncomputable def integerAgeRestrictionExtensionRaw {e d ell : Nat}
    (pi : Fin e → Fin d) (upper : IntegerGraphSupport d ell → Nat)
    (M : IntegerGraphSupport e ell → Nat) (T : IntegerGraphSupport d ell) : Nat := by
  classical
  exact if h : ∃ U, integerGraphSupportImage pi U = T
    then M (Classical.choose h) else upper T

theorem integerAgeRestrictionExtensionRaw_image {e d ell : Nat}
    (pi : Fin e → Fin d) (hi : Function.Injective pi)
    (upper : IntegerGraphSupport d ell → Nat)
    (M : IntegerGraphSupport e ell → Nat) (U : IntegerGraphSupport e ell) :
    integerAgeRestrictionExtensionRaw pi upper M (integerGraphSupportImage pi U) = M U := by
  classical
  have h : ∃ V, integerGraphSupportImage pi V = integerGraphSupportImage pi U := ⟨U,rfl⟩
  unfold integerAgeRestrictionExtensionRaw
  rw [dif_pos h]
  exact congrArg M (integerGraphSupportImage_injective pi hi (Classical.choose_spec h))

/-- Lift any intermediate restricted age to a genuine intermediate
full age. Clip exactly the supports in the image, then canonicalize.
Pushing forward a saturated selected witness proves exact recovery. -/
theorem integerGraphAge_restriction_lift_between {e d ell : Nat}
    (pi : Fin e → Fin d) (hi : Function.Injective pi) (hell : 0 < ell)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hLower : IsIntegerGraphAge d ell lower) (hUpper : IsIntegerGraphAge d ell upper)
    (hLe : AgeLe lower upper) (M : IntegerGraphSupport e ell → Nat)
    (hM : IsIntegerGraphAge e ell M)
    (hLM : ∀ U, lower (integerGraphSupportImage pi U) ≤ M U)
    (hMU : ∀ U, M U ≤ upper (integerGraphSupportImage pi U)) :
    ∃ C : IntegerGraphSupport d ell → Nat,
      IsIntegerGraphAge d ell C ∧ AgeLe lower C ∧ AgeLe C upper ∧
      ∀ U, C (integerGraphSupportImage pi U) = M U := by
  classical
  let B := integerAgeRestrictionExtensionRaw pi upper M
  have hLB : AgeLe lower B := by
    intro T
    by_cases h : ∃ U, integerGraphSupportImage pi U = T
    · obtain ⟨U,rfl⟩ := h
      rw [show B (integerGraphSupportImage pi U) = M U from
        integerAgeRestrictionExtensionRaw_image pi hi upper M U]
      exact hLM U
    · simpa [B,integerAgeRestrictionExtensionRaw,h] using hLe T
  have hBU : AgeLe B upper := by
    intro T
    by_cases h : ∃ U, integerGraphSupportImage pi U = T
    · obtain ⟨U,rfl⟩ := h
      rw [show B (integerGraphSupportImage pi U) = M U from
        integerAgeRestrictionExtensionRaw_image pi hi upper M U]
      exact hMU U
    · simp [B,integerAgeRestrictionExtensionRaw,h]
  let C := integerGraphAgeCanonical d ell B
  refine ⟨C, integerGraphAgeCanonical_is_age d ell B lower hLower hLB,
    integerGraphAgeCanonical_greatest d ell B lower hLower hLB,
    fun T => (integerGraphAgeCanonical_le_raw d ell B T).trans (hBU T), ?_⟩
  intro U
  apply Nat.le_antisymm
  · exact (integerGraphAgeCanonical_le_raw d ell B _).trans_eq
      (integerAgeRestrictionExtensionRaw_image pi hi upper M U)
  · obtain ⟨w,hw,hsat⟩ := hM.2 U
    have hwU : WitnessRespects (integerCliqueOnSupport (d := e) (ell := ell))
        (fun V => upper (integerGraphSupportImage pi V)) w :=
      fun V => (hw V).trans (hMU V)
    have hPushU := integerCliquePushforward_feasible pi hell upper
      (integerGraphAge_monotone d ell upper hUpper) w hwU
    have hPushB : WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell))
        B (integerCliquePushforward pi hell w) := by
      intro T
      by_cases h : ∃ V, integerGraphSupportImage pi V = T
      · obtain ⟨V,rfl⟩ := h
        rw [integerCliquePushforward_image_mass_eq pi hi hell w V,
          show B (integerGraphSupportImage pi V) = M V from
            integerAgeRestrictionExtensionRaw_image pi hi upper M V]
        exact hw V
      · simpa [B,integerAgeRestrictionExtensionRaw,h] using hPushU T
    rw [← hsat, ← integerCliquePushforward_image_mass_eq pi hi hell w U]
    exact witnessValue_le_canonical _ B _ hPushB _

/-- The restriction of a genuine full cover is a cover or equality. -/
theorem integerGraphAge_cover_injective_pullback {e d ell : Nat}
    (pi : Fin e → Fin d) (hi : Function.Injective pi) (hell : 0 < ell)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper) :
    (fun U => lower (integerGraphSupportImage pi U)) =
      (fun U => upper (integerGraphSupportImage pi U)) ∨
    AgeCover (IsIntegerGraphAge e ell)
      (fun U => lower (integerGraphSupportImage pi U))
      (fun U => upper (integerGraphSupportImage pi U)) := by
  classical
  by_cases hEq : (fun U => lower (integerGraphSupportImage pi U)) =
      (fun U => upper (integerGraphSupportImage pi U))
  · exact Or.inl hEq
  · right
    refine ⟨isIntegerGraphAge_pullback pi hell lower hCover.lower_age,
      isIntegerGraphAge_pullback pi hell upper hCover.upper_age,
      fun U => hCover.le _, hEq, ?_⟩
    intro M hM hLM hMU
    obtain ⟨C,hC,hLC,hCU,hRes⟩ := integerGraphAge_restriction_lift_between
      pi hi hell lower upper hCover.lower_age hCover.upper_age hCover.le M hM hLM hMU
    rcases hCover.no_intermediate C hC hLC hCU with h | h
    · left
      funext U
      exact (hRes U).symm.trans (congrFun h _)
    · right
      funext U
      exact (hRes U).symm.trans (congrFun h _)

/-- When a minimal changed support survives, so does the strict cover.
When even one of its classes is missing, the entire restricted age
is unchanged. This is the precise keep/omit criterion for a cover. -/
theorem integerGraphAge_cover_restriction_strict_iff {e d ell : Nat}
    (pi : Fin e → Fin d) (hi : Function.Injective pi) (hell : 0 < ell)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (T : IntegerGraphSupport d ell) (hChanged : lower T < upper T)
    (hMin : ∀ U : IntegerGraphSupport d ell, U.1 ⊆ T.1 → U.1 ≠ T.1 →
      lower U = upper U) :
    (fun U => lower (integerGraphSupportImage pi U)) ≠
      (fun U => upper (integerGraphSupportImage pi U)) ↔
      T.1 ⊆ Finset.univ.image pi := by
  classical
  constructor
  · intro h
    by_contra hNot
    apply h
    funext U
    have hSize := integerGraphAge_cover_changed_support_block_size d ell
      lower upper hCover T hChanged
    have hUnit := integerGraphAge_cover_changed_support_unit_drop d ell
      lower upper hCover T hChanged
    apply integerGraphAge_cover_event_preserves_without_full_support
      d ell (ell - 1 - lower T) hell lower upper T _
      hCover hSize.2.2 hUnit hMin
    intro hSub
    apply hNot
    intro j hj
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp (hSub hj)
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  · intro h hEq
    obtain ⟨U,hU⟩ := integerGraphSupportImage_exists_of_subset pi hi T h
    have hAt := congrFun hEq U
    rw [hU] at hAt
    exact (ne_of_lt hChanged) hAt

end Kk
