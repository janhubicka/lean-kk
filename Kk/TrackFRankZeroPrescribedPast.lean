import Kk.TrackFActualCodingFibre
import Kk.TrackFRealHensonTypeTree
import Mathlib.Tactic

/-!
# Track F: rank-zero dense source fibres realize one safe finite past pattern

English proof and hostile audit committed BEFORE Lean:
docs/track_f_rank_zero_prescribed_old_edges_english_audit.md

A rank-zero LARGE set of ACTUAL source coding nodes is dense.
Given a source root u and a FINITE set of previously chosen later
originals past, prescribe every positive/negative bit from the
next original to past by a subset positive ⊆ past.

If the genuine old-neighbour pool u.neighbours ∪ positive passes
the EXACT finite K_(ell-1)-free test, form a hypothetical type at
a finite cutoff and use density to choose an ACTUAL coding original
from the specified large set. Its complete two-directed old column
has precisely the prescribed bits on past, and its rank stays zero.

This is the concrete single-vertex BASE STEP for the still-open
multi-sort finite graph richness induction. No Henson left-density
assumption or published diary/BRD theorem is used.
-/

namespace Kk.HensonOneType

variable {ell : Nat} {E : Nat → Nat → Bool}

/-- In a rank-zero-Large set consisting entirely of ACTUAL coding
nodes, a new genuine original can be selected after any finite
cutoff, with EVERY edge to a specified finite set of past original
indices prescribed in BOTH orientations.

The old source neighbourhood U is frozen: all elements of past
lie at or beyond u.level, and positive ⊆ past. The complete
hypothetical source neighbourhood U ∪ positive must be
genuinely K_(ell-1)-free, with its actual finite directed-clique
test supplied explicitly.

No condition is placed on the chosen coding original's bits at
indices after the finite cutoff and before its own level. Those
must be handled by zero padding in later graph-gluing steps. -/
theorem rank_zero_dense_actualCoding_realizes_safe_past
    (S : Set (HensonOneType ell E))
    (u : HensonOneType ell E)
    (hu : rank u = 0)
    (hLarge : RankLargeness.Large rank S 0 u)
    (hActual : ∀ x : HensonOneType ell E,
      x ∈ S → IsCodingNode x)
    (front : Nat) (hFront : u.level ≤ front)
    (past positive : Finset Nat)
    (hPast : ∀ p ∈ past, u.level ≤ p ∧ p < front)
    (hPositive : positive ⊆ past)
    (hSafe : finitePoolCliqueCheck E (ell - 1)
      (u.neighbours ∪ positive) = false) :
    ∃ x : HensonOneType ell E,
      u ≤ x ∧ x ∈ S ∧ front ≤ x.level ∧ rank x = 0 ∧
      (∀ p ∈ past,
        E p x.level = decide (p ∈ positive) ∧
        E x.level p = decide (p ∈ positive)) := by
  classical
  let t : HensonOneType ell E := {
    level := front
    neighbours := u.neighbours ∪ positive
    below := by
      intro p hp
      rcases Finset.mem_union.mp hp with hpU | hpQ
      · exact lt_of_lt_of_le (u.below p hpU) hFront
      · exact (hPast p (hPositive hpQ)).2
    safe := hSafe
  }
  have hUT : u ≤ t := by
    constructor
    · exact hFront
    · intro p hpOld
      change p ∈ u.neighbours ↔ p ∈ u.neighbours ∪ positive
      constructor
      · intro hpU
        exact Finset.mem_union.mpr (Or.inl hpU)
      · intro hpNew
        rcases Finset.mem_union.mp hpNew with hpU | hpQ
        · exact hpU
        · have hpPast := (hPast p (hPositive hpQ)).1
          omega
  obtain ⟨x, hTX, hxS⟩ := hLarge t hUT
  have hUX : u ≤ x := le_trans hUT hTX
  have hXRank : rank x = 0 := by
    have hAnti : rank x ≤ rank u := rank_antitone hUX
    omega
  refine ⟨x, hUX, hxS, hTX.1, hXRank, ?_⟩
  intro p hpPast
  have hpFront : p < front := (hPast p hpPast).2
  have hpNotU : p ∉ u.neighbours := by
    intro hpU
    have hpOld := u.below p hpU
    have hpNew := (hPast p hpPast).1
    omega
  have hTBit : (p ∈ t.neighbours) ↔ (p ∈ positive) := by
    change (p ∈ u.neighbours ∪ positive) ↔ p ∈ positive
    simp only [Finset.mem_union, hpNotU, false_or]
  have hXBit : (p ∈ x.neighbours) ↔ (p ∈ positive) :=
    (hTX.2 p hpFront).symm.trans hTBit
  have hpActual : p < x.level :=
    lt_of_lt_of_le hpFront hTX.1
  have hCols := (hActual x hxS) p hpActual
  by_cases hpPos : p ∈ positive
  · have hpX : p ∈ x.neighbours := hXBit.mpr hpPos
    simpa [hpPos, hpX] using hCols
  · have hpX : p ∉ x.neighbours := by
      intro hpx
      exact hpPos (hXBit.mp hpx)
    simpa [hpPos, hpX] using hCols

end Kk.HensonOneType
