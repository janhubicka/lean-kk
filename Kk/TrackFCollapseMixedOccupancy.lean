import Kk.TrackFCollapseCliqueFeasibility
import Mathlib.Tactic

/-!
# Track F: finite collapse with untouched lower-rank sorts

English-first proof and hostile audit:
docs/track_f_collapse_mixed_occupancy_english_audit.md

The earlier verified collapse theorem is correct but its assumption
that EVERY refined sort contains at most one selected vertex is
too restrictive for the richness induction: unchanged lower-rank
sorts may still carry multiple vertices.

This module proves the general finite singleton-bound transfer
and derives an application-ready split/untouched version.
No new axioms, diary count or global BRD theorem are assumed.
-/

namespace Kk

/-- Any finite labelled clique satisfying every parent support
bound also satisfies EVERY refined support bound if each refined
singleton count obeys its own (possibly >1) singleton capacity,
and all mixed raw bounds are exact parent-image pullbacks.

The collapse map π may identify many daughter sorts. This theorem
does not claim the mixed raw pullback premise automatically; the
physical Henson marker lemmas establish that separately. -/
theorem trackFCollapse_singletonBounds_preserve_raw
    (d p : Nat)
    (π : Fin d → Fin p)
    (sort : Nat → Fin d)
    (B : Finset Nat)
    (oldRaw : Finset (Fin p) → Nat)
    (newRaw : Finset (Fin d) → Nat)
    (hOld : ∀ T : Finset (Fin p), T.Nonempty →
      (B.filter (fun x => π (sort x) ∈ T)).card ≤ oldRaw T)
    (hSingleton : ∀ i : Fin d,
      (B.filter (fun x => sort x = i)).card ≤ newRaw {i})
    (hMixed : ∀ S : Finset (Fin d), 2 ≤ S.card →
      newRaw S = oldRaw (S.image π)) :
    ∀ S : Finset (Fin d), S.Nonempty →
      (B.filter (fun x => sort x ∈ S)).card ≤ newRaw S := by
  classical
  intro S hS
  by_cases hSingletonS : S.card = 1
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hSingletonS
    subst S
    simpa only [Finset.mem_singleton] using hSingleton i
  · have hPos : 0 < S.card := Finset.card_pos.mpr hS
    have hTwo : 2 ≤ S.card := by omega
    have hImageNonempty : (S.image π).Nonempty := by
      obtain ⟨i, hi⟩ := hS
      exact ⟨π i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
    have hSubset :
        B.filter (fun x => sort x ∈ S) ⊆
          B.filter (fun x => π (sort x) ∈ S.image π) := by
      intro x hx
      obtain ⟨hxB, hxS⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr
        ⟨hxB, Finset.mem_image.mpr ⟨sort x, hxS, rfl⟩⟩
    calc
      (B.filter (fun x => sort x ∈ S)).card ≤
          (B.filter (fun x => π (sort x) ∈ S.image π)).card :=
        Finset.card_le_card hSubset
      _ ≤ oldRaw (S.image π) := hOld (S.image π) hImageNonempty
      _ = newRaw S := (hMixed S hTwo).symm

/-- Application form: only NEW daughters must hold at most one
selected vertex. All untouched lower-rank sorts may hold several
vertices, up to their actual unchanged (or larger) singleton
bound. The old parent singleton bounds control their counts.

This is the finite occupancy condition actually used in the
richness induction, but the existence of the marker sets and
multi-sort source/target synchronization remain separate. -/
theorem trackFCollapse_split_untouched_preserve_raw
    (d p : Nat)
    (π : Fin d → Fin p)
    (sort : Nat → Fin d)
    (B : Finset Nat)
    (newDaughters : Finset (Fin d))
    (oldRaw : Finset (Fin p) → Nat)
    (newRaw : Finset (Fin d) → Nat)
    (hOld : ∀ T : Finset (Fin p), T.Nonempty →
      (B.filter (fun x => π (sort x) ∈ T)).card ≤ oldRaw T)
    (hNewOne : ∀ i ∈ newDaughters,
      (B.filter (fun x => sort x = i)).card ≤ 1)
    (hNewPositive : ∀ i ∈ newDaughters, 1 ≤ newRaw {i})
    (hUntouched : ∀ i : Fin d, i ∉ newDaughters →
      oldRaw {π i} ≤ newRaw {i})
    (hMixed : ∀ S : Finset (Fin d), 2 ≤ S.card →
      newRaw S = oldRaw (S.image π)) :
    ∀ S : Finset (Fin d), S.Nonempty →
      (B.filter (fun x => sort x ∈ S)).card ≤ newRaw S := by
  classical
  apply trackFCollapse_singletonBounds_preserve_raw
    d p π sort B oldRaw newRaw hOld
  · intro i
    by_cases hi : i ∈ newDaughters
    · exact (hNewOne i hi).trans (hNewPositive i hi)
    · have hSubset :
          B.filter (fun x => sort x = i) ⊆
            B.filter (fun x => π (sort x) ∈ ({π i} : Finset (Fin p))) := by
        intro x hx
        obtain ⟨hxB, hxi⟩ := Finset.mem_filter.mp hx
        refine Finset.mem_filter.mpr ⟨hxB, ?_⟩
        simpa [hxi]
      have hOldOne : (B.filter
            (fun x => π (sort x) ∈ ({π i} : Finset (Fin p)))).card ≤
          oldRaw {π i} := hOld {π i} (by simp)
      exact (Finset.card_le_card hSubset).trans
        (hOldOne.trans (hUntouched i hi))
  · exact hMixed

end Kk
