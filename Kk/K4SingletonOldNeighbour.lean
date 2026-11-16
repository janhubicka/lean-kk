import Kk.FiniteOldColumnAge
import Kk.TrackFSingletonCapacity
import Mathlib.Tactic

/-!
# Track D: K4 finite old-column singleton ≤2 iff REAL old neighbour

English-first proof and 16 hostile checks:
docs/audits/2026-11-16-track-d-k4-singleton-old-neighbour-english.md

The small-independent full I2-fork argument uses that if a selected
future singleton has actual old-prefix clique-age capacity ≤2, then
SOME GENUINE OLD ORIGINAL in the ACTUAL old Q prefix is adjacent to
that complete type.

For the exact finite old-column raw age, this follows from
B({i}) = 3 - directedCliqueCapacity(commonOldNeighbourPool({i})).
We prove the raw capacity is support-monotone, use the already checked
canonical-singleton-equals-raw theorem, then prove BOTH directions
of the old-neighbour equivalence.

An arbitrary stipulated graph age with singleton value 2 need NOT
have a physical old prefix neighbour; the conclusion relies on the
genuine old-column reference-age representation. This is a finite
ordinary-L component, not the full Kpt no-I2 claim or a diary orbit.
-/

namespace Kk

/-- Exact finite-old-reference raw clique capacity is monotone
under enlarging the support: common old-neighbour sets shrink,
their maximal clique capacities decrease, and the raw
new-vertex allowance consequently increases.

No graph symmetry or K4-freeness hypothesis is needed for this
pure common-neighbour calculation. -/
theorem finiteOldColumnRawBound_support_mono
    (E : Nat → Nat → Bool)
    (ell d : Nat)
    (P : Finset Nat)
    (c : Nat → Fin d → Bool)
    (U V : IntegerGraphSupport d ell)
    (hUV : U.1 ⊆ V.1) :
    finiteOldColumnRawBound E ell d P c U ≤
      finiteOldColumnRawBound E ell d P c V := by
  classical
  have hPool :
      oldSupportCommonNeighbourPool P c V.1 ⊆
        oldSupportCommonNeighbourPool P c U.1 := by
    intro p hp
    change p ∈ P.filter (fun x => ∀ t ∈ V.1, c x t = true) at hp
    change p ∈ P.filter (fun x => ∀ t ∈ U.1, c x t = true)
    obtain ⟨hpP,hpV⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨hpP, fun t ht => hpV t (hUV ht)⟩
  have hCapacity :=
    finiteDirectedCliqueCapacity_mono E
      (oldSupportCommonNeighbourPool P c V.1)
      (oldSupportCommonNeighbourPool P c U.1) hPool
  unfold finiteOldColumnRawBound
  omega

/-- For an ACTUAL finite old Q prefix P and one complete future
ordinary-L type column i, canonical singleton K4 capacity ≤2
is EQUIVALENT to an actual old vertex whose prescribed
ordinary-L adjacency bit to i is true.

The canonicalizer has ALL support constraints, but its value on
this singleton agrees with the monotone raw old-column bound
by the already checked Track F singleton theorem.

This does not yet show that the generation-zero numerical-H copy
of the old neighbour separates all auxiliary Kpt source records;
that is a separate application-specific I2 obligation. -/
theorem k4_canonical_singleton_le_two_iff_old_neighbour
    (E : Nat → Nat → Bool)
    (d : Nat)
    (P : Finset Nat)
    (c : Nat → Fin d → Bool)
    (i : Fin d) :
    integerGraphAgeCanonical d 4
      (finiteOldColumnRawBound E 4 d P c)
      (trackFSingletonSupport d 4 i (by decide)) ≤ 2 ↔
    ∃ p : Nat, p ∈ P ∧ c p i = true := by
  classical
  let T : IntegerGraphSupport d 4 :=
    trackFSingletonSupport d 4 i (by decide)
  let B : IntegerGraphSupport d 4 → Nat :=
    finiteOldColumnRawBound E 4 d P c
  have hMono : TrackFRawSupportMonotone d 4 B := by
    intro U V hUV
    exact finiteOldColumnRawBound_support_mono E 4 d P c U V hUV
  have hCap : B T ≤ 4-1 := by
    dsimp [B, finiteOldColumnRawBound]
    omega
  have hCanonical :
      integerGraphAgeCanonical d 4 B T = B T :=
    trackFCanonical_singleton_eq_raw
      d 4 (by decide) B hMono i hCap
  have hPool :
      oldSupportCommonNeighbourPool P c T.1 =
        P.filter (fun p => c p i = true) := by
    ext p
    simp [oldSupportCommonNeighbourPool, T, trackFSingletonSupport]
  change integerGraphAgeCanonical d 4 B T ≤ 2 ↔
    ∃ p : Nat, p ∈ P ∧ c p i = true
  constructor
  · intro hSmall
    rw [hCanonical] at hSmall
    by_contra hNoOld
    have hEmpty :
        oldSupportCommonNeighbourPool P c T.1 = ∅ := by
      rw [hPool]
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro p hp
      obtain ⟨hpP,hBit⟩ := Finset.mem_filter.mp hp
      exact hNoOld ⟨p,hpP,hBit⟩
    have hRawFull : B T = 3 := by
      simp [B, finiteOldColumnRawBound, hEmpty,
        finiteDirectedCliqueCapacity]
    omega
  · rintro ⟨p,hpP,hBit⟩
    have hpPool : p ∈ oldSupportCommonNeighbourPool P c T.1 := by
      rw [hPool]
      exact Finset.mem_filter.mpr ⟨hpP,hBit⟩
    have hSub : ({p} : Finset Nat) ⊆
        oldSupportCommonNeighbourPool P c T.1 := by
      intro x hx
      have heq : x = p := Finset.mem_singleton.mp hx
      simpa only [heq] using hpPool
    have hOneClique : IsDirectedCliqueOn E ({p} : Finset Nat) := by
      intro x hx y hy hne
      have hxEq : x = p := Finset.mem_singleton.mp hx
      have hyEq : y = p := Finset.mem_singleton.mp hy
      exact False.elim (hne (hxEq.trans hyEq.symm))
    have hCapacity : 1 ≤
        finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool P c T.1) := by
      have hBound :=
        directedClique_card_le_capacity
          E (oldSupportCommonNeighbourPool P c T.1)
          ({p} : Finset Nat) hSub hOneClique
      simpa using hBound
    have hRawSmall : B T ≤ 2 := by
      dsimp [B, finiteOldColumnRawBound]
      omega
    rw [hCanonical]
    exact hRawSmall

#print axioms finiteOldColumnRawBound_support_mono
#print axioms k4_canonical_singleton_le_two_iff_old_neighbour

end Kk
