import Kk.OrderedTopMarkedSupport
import Kk.NumericHFullSelectedColumn
import Mathlib.Tactic

/-!
# Track A: every numerical-H prefix coordinate, and exact gap-to-top zeros

English mathematical proof and hostile audit FIRST:
  docs/numeric_prefix_gap_zero_english_audit.md

No numbered prefix coordinate is omitted: it is either an odd dummy,
or the actual real numerical-H copy at a bounded generation t <= k.
Odd dummy ordinary-L bits vanish, and original complete gap-to-selected
nonedges lift to both directed numerical-H L bits at selected top copies.

The entire numeric prefix is exactly P union Q union its genuine
set-theoretic complement G. This does NOT assume, prove, or hide
a compatible global resolved-copy schedule or integer-age reference
semantics; the needed original-graph zero certificates stay explicit.
-/

namespace Kk

open SuccessorTree.V10

/-- Exhaustive exact numerical-H coordinate classification:
every natural-number coordinate is either an odd dummy or a genuine
real-generation copy with generation at most k. This also holds k=0. -/
theorem numericCoordinate_odd_or_real (k z : Nat) :
    (∃ a : Nat, z = 2 * a + 1) ∨
      (∃ i t : Nat, t ≤ k ∧ z = hPosition k i t) := by
  have hDiv : z % 2 + 2 * (z / 2) = z := Nat.mod_add_div z 2
  by_cases hz : z % 2 = 1
  · left
    refine ⟨z / 2, ?_⟩
    omega
  · right
    have hMod : z % 2 < 2 := Nat.mod_lt z (by omega)
    have hz0 : z % 2 = 0 := by omega
    have hEven : z = 2 * (z / 2) := by omega
    let i : Nat := (z / 2) / (k + 1)
    let t : Nat := (z / 2) % (k + 1)
    have hRem : t < k + 1 := by
      dsimp [t]
      exact Nat.mod_lt _ (by omega)
    have hEuclid :
        (z / 2) % (k + 1) +
          (k + 1) * ((z / 2) / (k + 1)) = z / 2 :=
      Nat.mod_add_div (z / 2) (k + 1)
    refine ⟨i, t, by omega, ?_⟩
    calc
      z = 2 * (z / 2) := hEven
      _ = 2 * ((z / 2) % (k + 1) +
          (k + 1) * ((z / 2) / (k + 1))) := by rw [hEuclid]
      _ = hPosition k i t := by
        dsimp [hPosition, i, t]
        ring

/-- Every odd dummy coordinate has zero ordinary-L crossing bits in
both directions to every selected top position, even when the dummy
has auxiliary H+ E incidence. This is the literal finite H graph-L. -/
theorem finiteNumericH_odd_dummy_to_top_zero
    (E : Nat → Nat → Bool) (k M a j : Nat) :
    (finiteNumericHL (normalizedGraphModel E) k M).binary
        (2 * a + 1) (hPosition k j k) (0 : Fin 1) = false ∧
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k j k) (2 * a + 1) (0 : Fin 1) = false := by
  change hNumericBinary (normalizedGraphModel E).binary k
      (2 * a + 1) (hPosition k j k) (0 : Fin 1) = false ∧
    hNumericBinary (normalizedGraphModel E).binary k
      (hPosition k j k) (2 * a + 1) (0 : Fin 1) = false
  exact ⟨hNumericBinary_odd_left_false
      (normalizedGraphModel E).binary k a (hPosition k j k) (0 : Fin 1),
    hNumericBinary_odd_right_false
      (normalizedGraphModel E).binary k (hPosition k j k) a (0 : Fin 1)⟩

/-- An absent original E-edge from an earlier real gap original to a
later selected original remains zero at every bounded earlier
generation and the selected top generation, in BOTH L directions. -/
theorem finiteNumericH_real_gap_to_top_zero
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k M i t j : Nat)
    (ht : t ≤ k) (hij : i < j) (hE : E i j = false) :
    (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k i t) (hPosition k j k) (0 : Fin 1) = false ∧
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k j k) (hPosition k i t) (0 : Fin 1) = false := by
  have hForward :
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k i t) (hPosition k j k) (0 : Fin 1) = E i j := by
    change hNumericBinary (normalizedGraphModel E).binary k
        (hPosition k i t) (hPosition k j k) (0 : Fin 1) = E i j
    exact numericH_older_generation_to_top_exact
      (normalizedGraphModel E).binary k i j t (0 : Fin 1) hij ht
  have hReverse :
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k j k) (hPosition k i t) (0 : Fin 1) = E i j := by
    have hSwap := henson_finiteNumericH_binary_symmetric
      E hSym k M (hPosition k j k) (hPosition k i t)
    exact hSwap.trans hForward
  exact ⟨hForward.trans hE, hReverse.trans hE⟩

/-- A NUMERICAL prefix before the start of every selected original,
together with complete ORIGINAL gap-to-selected zero columns for all
real gap copies, forces BOTH physical numerical L gap-to-top zeros.

The real/dummy coordinate classification is derived, not assumed.
Only the original complete-neighbourhood certificate remains an input
for Track B to actually construct. -/
theorem finiteNumericH_all_gap_to_marked_top_zero
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k M m : Nat) (G S : Finset Nat)
    (hWithin : ∀ z ∈ G, z < m)
    (hFuture : ∀ j ∈ S, m ≤ hPosition k j 0)
    (hOriginalZeros : ∀ i t : Nat,
      t ≤ k → hPosition k i t ∈ G →
      ∀ j ∈ S, E i j = false) :
    ∀ z ∈ G, ∀ w ∈ numericHTopPool k S,
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        z w (0 : Fin 1) = false ∧
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        w z (0 : Fin 1) = false := by
  classical
  intro z hz w hw
  obtain ⟨j, hj, hwj⟩ := Finset.mem_image.mp hw
  rcases numericCoordinate_odd_or_real k z with ⟨a, ha⟩ |
    ⟨i, t, ht, hReal⟩
  · rw [ha, ←hwj]
    exact finiteNumericH_odd_dummy_to_top_zero E k M a j
  · have hBefore : i < j := by
      have hLt : hPosition k i t < hPosition k j 0 := by
        rw [← hReal]
        exact lt_of_lt_of_le (hWithin z hz) (hFuture j hj)
      rcases hPosition_before k i t j 0 ht (by omega) hLt with
        hlt | ⟨_, hImpossible⟩
      · exact hlt
      · omega
    have hRealG : hPosition k i t ∈ G := hReal ▸ hz
    have hZero := hOriginalZeros i t ht hRealG j hj
    rw [hReal, ←hwj]
    exact finiteNumericH_real_gap_to_top_zero
      E hSym k M i t j ht hBefore hZero

/-- Exact finite pool of ALL omitted numeric prefix coordinates. -/
def numericPrefixGapPool (m : Nat) (P Q : Finset Nat) : Finset Nat :=
  Finset.range m \ (P ∪ Q)

theorem numericPrefixGapPool_subset_range
    (m : Nat) (P Q : Finset Nat) :
    numericPrefixGapPool m P Q ⊆ Finset.range m := by
  intro z hz
  exact (Finset.mem_sdiff.mp hz).1

/-- Set-theoretically exact prefix partition: once P and Q are
actual subsets of [0,m), their complement G accounts for EVERY
remaining numeric position, including odd dummies and real gaps. -/
theorem numericPrefix_union_gap_exact
    (m : Nat) (P Q : Finset Nat)
    (hP : P ⊆ Finset.range m)
    (hQ : Q ⊆ Finset.range m) :
    (P ∪ Q) ∪ numericPrefixGapPool m P Q = Finset.range m := by
  classical
  ext z
  constructor
  · intro hz
    rcases Finset.mem_union.mp hz with hPQ | hG
    · rcases Finset.mem_union.mp hPQ with hPz | hQz
      · exact hP hPz
      · exact hQ hQz
    · exact (Finset.mem_sdiff.mp hG).1
  · intro hz
    by_cases hPQ : z ∈ P ∪ Q
    · exact Finset.mem_union.mpr (Or.inl hPQ)
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_sdiff.mpr ⟨hz, hPQ⟩))

/-- The designated numeric cut after a reserved original's pivot copy
is still before generation 0 of EVERY later selected original. -/
theorem orderedReserved_numeric_cut_before_all_selected
    (k r a g : Nat) (q : Nat → Nat) (S : Finset Nat)
    (ha : a < r) (hg : g ≤ k)
    (hLater : ∀ b, b < r → ∀ j ∈ S, q b < j) :
    ∀ j ∈ S,
      hPosition k (q a) g + 1 ≤ hPosition k j 0 := by
  intro j hj
  have hOrder : q a < j := hLater a ha j hj
  have hLt : hPosition k (q a) g < hPosition k j 0 :=
    hPosition_lt_of_block_lt k (q a) j g 0 hg hOrder
  omega

#print axioms Kk.numericCoordinate_odd_or_real
#print axioms Kk.finiteNumericH_odd_dummy_to_top_zero
#print axioms Kk.finiteNumericH_real_gap_to_top_zero
#print axioms Kk.finiteNumericH_all_gap_to_marked_top_zero
#print axioms Kk.numericPrefixGapPool_subset_range
#print axioms Kk.numericPrefix_union_gap_exact
#print axioms Kk.orderedReserved_numeric_cut_before_all_selected

end Kk
