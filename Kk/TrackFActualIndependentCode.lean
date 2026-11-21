import Kk.TrackFNonrootPrefixFibre
import Kk.TrackFActualCodingFibre
import Mathlib.Tactic

/-!
# Track F: actual independent-code vertices with finitely many zero columns

English proof and 16 hostile checks committed FIRST:
docs/track_f_rankzero_actual_independent_code_english_audit_20261121.md

This is a physical step in realizing the zero-code event of a history:
from an ACTUAL rank-large target coding fibre choose a genuine source
coding original, later than any prescribed TARGET cutoff, whose full
ordinary source AND induced target two-direction edges to any finite
already-coded source set vanish.

A prerequisite is that every past index already below the old source
type's level has a zero bit there. Indices not yet in the prefix are
forced to zero by exact rank-preserving source padding.

No assumption that the embedding preserves chronological order.
This does NOT construct the surviving synchronized front, identify
the whole history at the coding cut, or prove diary unavoidability.
-/

namespace Kk.HensonOneType

/-- Zero padding a genuine source root beyond all finite previously
coded source originals preserves an ACTUAL rank-large target coding
fibre and makes every such old index a zero bit in the padded type.

This works at every rank; for an independent code we later take rank 0.
A past index below u.level must already have bit zero in u, as no
chronological refinement can erase an old positive neighbour. -/
theorem sourceCodingFibre_large_zeroPad_avoids_past
    (ell : Nat)
    (Esrc Etgt : Nat → Nat → Bool)
    (e : Nat → Nat)
    (v : HensonOneType ell Etgt)
    (u : HensonOneType ell Esrc)
    (hLarge : RankLargeness.Large rank
      (sourceCodingFibre (E := Esrc) Etgt e v)
      (rank u) u)
    (past : Finset Nat)
    (hPastOldZero : ∀ p ∈ past, p < u.level →
      p ∉ u.neighbours)
    (sourceBound : Nat) :
    ∃ z : HensonOneType ell Esrc,
      u ≤ z ∧
      sourceBound ≤ z.level ∧
      rank z = rank u ∧
      RankLargeness.Large rank
        (sourceCodingFibre (E := Esrc) Etgt e v)
        (rank u) z ∧
      (∀ p ∈ past, p < z.level ∧
        p ∉ z.neighbours) := by
  classical
  let H : Nat :=
    max (max u.level sourceBound)
      ((past.sup id) + 1)
  have huH : u.level ≤ H :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hSource : sourceBound ≤ H :=
    (le_max_right _ _).trans (le_max_left _ _)
  let z : HensonOneType ell Esrc := zeroPad u H huH
  have huz : u ≤ z := le_zeroPad u H huH
  have hzRank : rank z = rank u := rank_zeroPad u H huH
  have hzLarge :
      RankLargeness.Large rank
        (sourceCodingFibre (E := Esrc) Etgt e v)
        (rank u) z :=
    RankLargeness.large_mono_cone rank
      (sourceCodingFibre (E := Esrc) Etgt e v)
      (rank u) u z huz hLarge
  refine ⟨z, huz, hSource, hzRank, hzLarge, ?_⟩
  intro p hp
  have hpSup : p ≤ past.sup id :=
    Finset.le_sup (f := id) hp
  have hpLtH : p < H := by
    have hBound : past.sup id + 1 ≤ H := le_max_right _ _
    omega
  have hpNotU : p ∉ u.neighbours := by
    by_cases hOld : p < u.level
    · exact hPastOldZero p hp hOld
    · intro hpU
      exact hOld (u.below p hpU)
  change p < H ∧ p ∉ u.neighbours
  exact ⟨hpLtH, hpNotU⟩

/-- Choose a GENUINE actual source coding original in a rank-large
target fibre, strictly after any target cutoff under an arbitrary
injective (possibly nonmonotone) induced original-index embedding.
Its source and target ORDINARY edges to all previously coded source
originals vanish in both orientations.

The source root need not be rank zero; the rank-zero specialisation
below is the exact independent-code application. -/
theorem sourceCodingFibre_large_actual_future_zero_past
    (ell cutoff : Nat)
    (Esrc Etgt : Nat → Nat → Bool)
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (v : HensonOneType ell Etgt)
    (u : HensonOneType ell Esrc)
    (hLarge : RankLargeness.Large rank
      (sourceCodingFibre (E := Esrc) Etgt e v)
      (rank u) u)
    (past : Finset Nat)
    (hPastOldZero : ∀ p ∈ past, p < u.level →
      p ∉ u.neighbours) :
    ∃ x : HensonOneType ell Esrc,
      u ≤ x ∧
      x ∈ sourceCodingFibre (E := Esrc) Etgt e v ∧
      cutoff < e x.level ∧
      rank x ≤ rank u ∧
      (∀ p ∈ past,
        p < x.level ∧
        Esrc p x.level = false ∧
        Esrc x.level p = false ∧
        Etgt (e p) (e x.level) = false ∧
        Etgt (e x.level) (e p) = false) := by
  classical
  obtain ⟨M, hFuture⟩ :=
    injective_eventually_beyond_target_prefix
      e he (cutoff + 1)
  obtain ⟨z, huz, hMZ, hzRank, hzLarge, hPastZ⟩ :=
    sourceCodingFibre_large_zeroPad_avoids_past
      ell Esrc Etgt e v u hLarge
      past hPastOldZero M
  obtain ⟨x, hzx, hxFibre⟩ :=
    RankLargeness.large_has_member rank
      (sourceCodingFibre (E := Esrc) Etgt e v)
      (rank u) z hzRank hzLarge
  have hux : u ≤ x := le_trans huz hzx
  have hFutureX : cutoff < e x.level := by
    have hMX : M ≤ x.level := hMZ.trans hzx.1
    have hCut := hFuture x.level hMX
    omega
  have hxRank : rank x ≤ rank u :=
    (rank_antitone hux)
  refine ⟨x, hux, hxFibre, hFutureX, hxRank, ?_⟩
  intro p hp
  obtain ⟨hpZLt, hpNotZ⟩ := hPastZ p hp
  have hpXLt : p < x.level :=
    lt_of_lt_of_le hpZLt hzx.1
  have hpNotX : p ∉ x.neighbours := by
    intro hpX
    have hpZ : p ∈ z.neighbours :=
      (hzx.2 p hpZLt).mpr hpX
    exact hpNotZ hpZ
  have hSourceCol := hxFibre.1 p hpXLt
  have hSource1 : Esrc p x.level = false := by
    simpa [hpNotX] using hSourceCol.1
  have hSource2 : Esrc x.level p = false := by
    simpa [hpNotX] using hSourceCol.2
  have hpNe : p ≠ x.level := Nat.ne_of_lt hpXLt
  have hTarget1 : Etgt (e p) (e x.level) = false := by
    rw [← hInduced p x.level hpNe]
    exact hSource1
  have hTarget2 : Etgt (e x.level) (e p) = false := by
    rw [← hInduced x.level p hpNe.symm]
    exact hSource2
  exact ⟨hpXLt, hSource1, hSource2, hTarget1, hTarget2⟩

/-- Independent-code application: if the ACTUAL fibre is rank-zero
large above a genuine zero-rank source type, its strictly future
coding witness also has rank zero and is nonadjacent to all
previously coded source vertices and their target images.

This is a LOCAL code-vertex choice, not a global history theorem. -/
theorem sourceCodingFibre_rank_zero_independent_code
    (ell cutoff : Nat)
    (Esrc Etgt : Nat → Nat → Bool)
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (v : HensonOneType ell Etgt)
    (u : HensonOneType ell Esrc)
    (hRankZero : rank u = 0)
    (hLarge : RankLargeness.Large rank
      (sourceCodingFibre (E := Esrc) Etgt e v)
      0 u)
    (past : Finset Nat)
    (hPastOldZero : ∀ p ∈ past, p < u.level →
      p ∉ u.neighbours) :
    ∃ x : HensonOneType ell Esrc,
      u ≤ x ∧
      x ∈ sourceCodingFibre (E := Esrc) Etgt e v ∧
      rank x = 0 ∧
      cutoff < e x.level ∧
      (∀ p ∈ past,
        p < x.level ∧
        Esrc p x.level = false ∧
        Esrc x.level p = false ∧
        Etgt (e p) (e x.level) = false ∧
        Etgt (e x.level) (e p) = false) := by
  have hLarge' :
      RankLargeness.Large rank
        (sourceCodingFibre (E := Esrc) Etgt e v)
        (rank u) u := by
    simpa only [hRankZero] using hLarge
  obtain ⟨x, hux, hxFibre, hFuture, hRankLe, hPast⟩ :=
    sourceCodingFibre_large_actual_future_zero_past
      ell cutoff Esrc Etgt e he hInduced
      v u hLarge' past hPastOldZero
  have hRankX : rank x = 0 := by
    omega
  exact ⟨x, hux, hxFibre, hRankX, hFuture, hPast⟩

end Kk.HensonOneType
