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
#check Kk.CoherentKptIndex.forward_live_does_not_imply_reflection
#print axioms Kk.CoherentKptIndex.forward_live_does_not_imply_reflection
