import Kk.CoherentKptIndexComposition

/-!
# Track C — exact cut-live image criterion

English-first audit: `docs/track_c_live_image_criterion_english_audit.md`.

A coherent old-to-new source index preserves live status only forward.
At each cut, the exact image of old live names is all new live names
if and only if every new live name has an old preimage AND old inactive
names do not newly activate. This is strictly weaker than a reverse
map of the entire new source index, which may be impossible by the
verified fresh-dependent-source obstruction.

No new physical root-stage completeness or BRD bound is asserted.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

namespace CoherentKptIndex

/-- Exact criterion for equality of indexed live names at one cut.
The left side is pointwise equality of the new live family with the
forward image of the old live family. The two conditions on the right
are (i) coverage of every new live name by the full old index, and
(ii) reflection of liveness on the image of the old index.

The forward liveness implication is already part of `h`.
In particular, surjectivity on live names alone is insufficient. -/
theorem live_image_iff_coverage_and_reflection
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    {P Q : Nat}
    {oldNode : Fin P → AdmissibleKptNode family}
    {newNode : Fin Q → AdmissibleKptNode family}
    {oldLive : Nat → Fin P → Bool}
    {newLive : Nat → Fin Q → Bool}
    {horizon cut : Nat}
    (h : CoherentKptIndex family oldNode newNode
      oldLive newLive horizon)
    (hcut : cut < horizon) :
    (∀ j : Fin Q,
      newLive cut j = true ↔
        ∃ i : Fin P, oldLive cut i = true ∧ h.map i = j) ↔
    ((∀ j : Fin Q, newLive cut j = true →
        ∃ i : Fin P, h.map i = j) ∧
      (∀ i : Fin P, newLive cut (h.map i) = true →
        oldLive cut i = true)) := by
  constructor
  · intro heq
    constructor
    · intro j hj
      obtain ⟨i, _, hij⟩ := (heq j).mp hj
      exact ⟨i, hij⟩
    · intro i hi
      obtain ⟨k, hk, hki⟩ := (heq (h.map i)).mp hi
      have hki' : k = i := h.map_injective hki
      exact hki' ▸ hk
  · rintro ⟨hcover, hreflect⟩ j
    constructor
    · intro hj
      obtain ⟨i, hij⟩ := hcover j hj
      have hnew : newLive cut (h.map i) = true := by
        rw [hij]
        exact hj
      exact ⟨i, hreflect i hnew, hij⟩
    · rintro ⟨i, hi, hij⟩
      rw [← hij]
      exact h.live_forward cut hcut i hi


/-- Every newly live target index not transported from an old *live*
index has exactly one of two explanations at the source-name level:
either it is the image of an old index which was inactive at this
cut, or it is outside the entire old index image.

This is a finite-index logical decomposition, not a physical
classification of Kpt novelty into diary microevents. -/
theorem new_live_untransported_is_activation_or_outside
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    {P Q : Nat}
    {oldNode : Fin P → AdmissibleKptNode family}
    {newNode : Fin Q → AdmissibleKptNode family}
    {oldLive : Nat → Fin P → Bool}
    {newLive : Nat → Fin Q → Bool}
    {horizon : Nat}
    (h : CoherentKptIndex family oldNode newNode
      oldLive newLive horizon)
    (cut : Nat) (j : Fin Q)
    (_hnew : newLive cut j = true)
    (hnot : ¬ ∃ i : Fin P,
      oldLive cut i = true ∧ h.map i = j) :
    (∃ i : Fin P,
      oldLive cut i ≠ true ∧ h.map i = j) ∨
      (∀ i : Fin P, h.map i ≠ j) := by
  classical
  by_cases hpre : ∃ i : Fin P, h.map i = j
  · obtain ⟨i, hij⟩ := hpre
    left
    refine ⟨i, ?_, hij⟩
    intro hi
    exact hnot ⟨i, hi, hij⟩
  · right
    intro i hij
    exact hpre ⟨i, hij⟩

/-- In particular, if a new live target index has an old
representative and no old-inactive name becomes new-live, then the
index must be transported from an old live name. -/
theorem transported_of_coverage_and_no_activation
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    {P Q : Nat}
    {oldNode : Fin P → AdmissibleKptNode family}
    {newNode : Fin Q → AdmissibleKptNode family}
    {oldLive : Nat → Fin P → Bool}
    {newLive : Nat → Fin Q → Bool}
    {horizon : Nat}
    (h : CoherentKptIndex family oldNode newNode
      oldLive newLive horizon)
    (cut : Nat) (j : Fin Q)
    (hj : newLive cut j = true)
    (hcover : ∃ i : Fin P, h.map i = j)
    (hreflect : ∀ i : Fin P,
      newLive cut (h.map i) = true → oldLive cut i = true) :
    ∃ i : Fin P, oldLive cut i = true ∧ h.map i = j := by
  obtain ⟨i, hij⟩ := hcover
  refine ⟨i, ?_, hij⟩
  apply hreflect i
  rw [hij]
  exact hj


/-- Under injective enumeration of the NEW actual source nodes,
being outside the name-map image is precisely the same as being
a literal Kpt node with no OLD indexed representative.

Without target enumeration injectivity this is false: an unused
new index could duplicate a transported old Kpt node. -/
theorem outside_image_iff_literal_new_source
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    {P Q : Nat}
    {oldNode : Fin P → AdmissibleKptNode family}
    {newNode : Fin Q → AdmissibleKptNode family}
    {oldLive : Nat → Fin P → Bool}
    {newLive : Nat → Fin Q → Bool}
    {horizon : Nat}
    (h : CoherentKptIndex family oldNode newNode
      oldLive newLive horizon)
    (hNewInjective : Function.Injective newNode)
    (j : Fin Q) :
    (∀ i : Fin P, h.map i ≠ j) ↔
      (∀ i : Fin P, oldNode i ≠ newNode j) := by
  constructor
  · intro hOutside i hEqual
    apply hOutside i
    apply hNewInjective
    calc
      newNode (h.map i) = oldNode i := h.same_node i
      _ = newNode j := hEqual
  · intro hAbsent i hMaps
    apply hAbsent i
    calc
      oldNode i = newNode (h.map i) := (h.same_node i).symm
      _ = newNode j := congrArg newNode hMaps

/-- At a genuine injective target enumeration, every new live index
not transported from an old live name is either a formerly inactive
OLD Kpt node, or a genuinely absent-from-old Kpt node. This is the
exact node-level refinement of the earlier index-level disjunction. -/
theorem new_live_residual_old_inactive_or_literal_fresh
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    {P Q : Nat}
    {oldNode : Fin P → AdmissibleKptNode family}
    {newNode : Fin Q → AdmissibleKptNode family}
    {oldLive : Nat → Fin P → Bool}
    {newLive : Nat → Fin Q → Bool}
    {horizon : Nat}
    (h : CoherentKptIndex family oldNode newNode
      oldLive newLive horizon)
    (hNewInjective : Function.Injective newNode)
    (cut : Nat) (j : Fin Q)
    (hj : newLive cut j = true)
    (hNotOldLive : ¬ ∃ i : Fin P,
      oldLive cut i = true ∧ h.map i = j) :
    (∃ i : Fin P,
      oldLive cut i ≠ true ∧ oldNode i = newNode j) ∨
      (∀ i : Fin P, oldNode i ≠ newNode j) := by
  rcases h.new_live_untransported_is_activation_or_outside
      cut j hj hNotOldLive with hActive | hOutside
  · left
    obtain ⟨i, hInactive, hMap⟩ := hActive
    refine ⟨i, hInactive, ?_⟩
    calc
      oldNode i = newNode (h.map i) := (h.same_node i).symm
      _ = newNode j := congrArg newNode hMap
  · right
    exact (h.outside_image_iff_literal_new_source hNewInjective j).mp hOutside


/-- The canonical Fin-index enumeration of an actual finite Kpt source
set is injective: unlike an arbitrary list, it cannot contain
duplicate names for the same full dependent Kpt node. -/
theorem canonical_source_index_injective
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (newParams : Finset (AdmissibleKptNode family)) :
    Function.Injective
      (fun j : Fin newParams.card =>
        (newParams.equivFin.symm j).val) := by
  classical
  intro i j hij
  apply (newParams.equivFin.symm).injective
  exact Subtype.ext hij

/-- Consequently, the node-level residual dichotomy applies to
every coherent source index whose target enumeration is the canonical
Fin-indexing of an actual physical finite source Finset. -/
theorem canonical_new_live_residual_old_inactive_or_fresh
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    {P : Nat}
    {oldNode : Fin P → AdmissibleKptNode family}
    (newParams : Finset (AdmissibleKptNode family))
    {oldLive : Nat → Fin P → Bool}
    {newLive : Nat → Fin newParams.card → Bool}
    {horizon : Nat}
    (h : CoherentKptIndex family oldNode
      (fun j : Fin newParams.card => (newParams.equivFin.symm j).val)
      oldLive newLive horizon)
    (cut : Nat) (j : Fin newParams.card)
    (hj : newLive cut j = true)
    (hNotOldLive : ¬ ∃ i : Fin P,
      oldLive cut i = true ∧ h.map i = j) :
    (∃ i : Fin P,
      oldLive cut i ≠ true ∧
        oldNode i = (newParams.equivFin.symm j).val) ∨
      (∀ i : Fin P,
        oldNode i ≠ (newParams.equivFin.symm j).val) := by
  exact h.new_live_residual_old_inactive_or_literal_fresh
    (canonical_source_index_injective newParams) cut j hj hNotOldLive

/-- A one-element index can retain the identical literal source map
while its live mask changes from false to true. This is a pure Boolean
interface countermodel; no physical Kpt realizability is claimed. -/
theorem forward_live_does_not_imply_reflection (cut : Nat) :
    ∃ (oldLive newLive : Nat → Fin 1 → Bool),
      (∀ c i, oldLive c i = true → newLive c i = true) ∧
      newLive cut 0 = true ∧ oldLive cut 0 = false := by
  refine ⟨(fun _ _ => false), (fun _ _ => true), ?_, rfl, rfl⟩
  intro c i h
  simp at h

end CoherentKptIndex

end Kk

-- Direct named axiom audit, intentionally local until the exact-head build passes.
#check Kk.CoherentKptIndex.live_image_iff_coverage_and_reflection
#print axioms Kk.CoherentKptIndex.live_image_iff_coverage_and_reflection
#check Kk.CoherentKptIndex.new_live_untransported_is_activation_or_outside
#print axioms Kk.CoherentKptIndex.new_live_untransported_is_activation_or_outside
#check Kk.CoherentKptIndex.transported_of_coverage_and_no_activation
#print axioms Kk.CoherentKptIndex.transported_of_coverage_and_no_activation
#check Kk.CoherentKptIndex.outside_image_iff_literal_new_source
#print axioms Kk.CoherentKptIndex.outside_image_iff_literal_new_source
#check Kk.CoherentKptIndex.new_live_residual_old_inactive_or_literal_fresh
#print axioms Kk.CoherentKptIndex.new_live_residual_old_inactive_or_literal_fresh
#check Kk.CoherentKptIndex.canonical_source_index_injective
#print axioms Kk.CoherentKptIndex.canonical_source_index_injective
#check Kk.CoherentKptIndex.canonical_new_live_residual_old_inactive_or_fresh
#print axioms Kk.CoherentKptIndex.canonical_new_live_residual_old_inactive_or_fresh
#check Kk.CoherentKptIndex.forward_live_does_not_imply_reflection
#print axioms Kk.CoherentKptIndex.forward_live_does_not_imply_reflection
