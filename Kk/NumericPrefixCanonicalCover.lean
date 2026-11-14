import Kk.NumericPrefixWholeAge
import Kk.FiniteOldColumnAge
import Kk.FiniteSupportCoverProfile
import Kk.FiniteCliqueEmbeddingTransport
import Mathlib.Tactic

/-!
# Track A: exact whole numerical-H prefix -> canonical integer-age cover

English proof and adversarial audit committed FIRST:
  docs/numeric_prefix_canonical_cover_english_audit.md

This module composes the independently kernel-checked all-coordinate
numeric-prefix gluing, complete typed old-column reference age and
all-support raw/canonical cover-budget theorems.

Crucially the initial graph age is COMPUTED from the old reference
table's actual common-neighbour clique capacities, not assumed via a
single selected-support maximum. All required physical original gap
zeros, simultaneous reserved support columns, and past safety remain
explicit. The exact age-cover corollary adds the genuine pointwise
reference-age = upper hypothesis, not an unchecked identification.

This is a finite per-compatible-future ordinary-L theorem. It does
not realize a fixed physical all-pattern front or prove the recursive
resolved copy, auxiliary H+ E/B3, inverse-source orbit or BRDs.
-/

namespace Kk

open SuccessorTree.V10

/-- Exact directed clique capacity is unchanged if all off-diagonal
Boolean L atoms agree on one finite set, in BOTH orientations.
The proof transports capacities along the identity induced map. -/
theorem finiteDirectedCliqueCapacity_eq_of_offDiagonal_agreement
    (A L : Nat → Nat → Bool) (Q : Finset Nat)
    (hAgree : ∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → A x y = L x y) :
    finiteDirectedCliqueCapacity L Q =
      finiteDirectedCliqueCapacity A Q := by
  classical
  have hInj : Set.InjOn (fun x : Nat => x) ↑Q := by
    intro x _ y _ h
    exact h
  have h := finiteDirectedCliqueCapacity_induced_image_eq
    A L Q (fun x : Nat => x) hInj hAgree
  simpa using h

/-- The COMPLETE actual numerical-H prefix, with all real copies and
odd dummy coordinates, has exactly the canonical raw-cover-block
labelled-clique continuation profile computed from the *actual*
old reference table A.

The reference raw age B_P(U) is the maximum common-old-neighbour
clique capacity bound ell-1-rho_P(U), canonicalized only after the
single reserved support budget is imposed. No positivity or genuine
age-cover assumption is needed: r<ell guarantees the necessary
truncated-Nat capacity guard, and all other relative physical
hypotheses are explicit.

Every selected original is later than every reserved original, all
crossing L atoms are exact in BOTH orientations, and the full
numerical prefix is safe. This is a per-finite-W theorem, not a
global surjectivity assertion for future names. -/
theorem finiteNumericH_whole_prefix_raw_canonical_block_iff
    (E A : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k M r a g ell d : Nat) (q : Nat → Nat)
    (ha : a < r) (hr : r ≤ k + 1) (hgk : g ≤ k)
    (hrEll : r < ell)
    (hOrder : ∀ b c, b < c → c < r → q b < q c)
    (hClique : ∀ b c, b < c → c < r → E (q b) (q c) = true)
    (S : Finset Nat)
    (hLater : ∀ b, b < r → ∀ j ∈ S, q b < j)
    (tau : Nat → Fin d) (T : IntegerGraphSupport d ell)
    (hUniform : ∀ b, b < r → ∀ j ∈ S,
      E (q b) j = decide (tau (hPosition k j k) ∈ T.1))
    (c : Nat → Fin d → Bool)
    (P : Finset Nat)
    (hP : ∀ p ∈ P, p < hPosition k (q a) g + 1)
    (hNoPQ : ∀ p ∈ P, ∀ u ∈ orderedReservedNumericPrefix k q a g,
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          p u (0 : Fin 1) = false)
    (hOriginalGapZeros : ∀ i t : Nat,
      t ≤ k →
      hPosition k i t ∈
        numericPrefixGapPool (hPosition k (q a) g + 1) P
          (orderedReservedNumericPrefix k q a g) →
      ∀ j ∈ S, E i j = false)
    (hPast : finitePoolCliqueCheck
      (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
        u v (0 : Fin 1))
      ell (Finset.range (hPosition k (q a) g + 1)) = false)
    (hOld : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' →
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          p p' (0 : Fin 1) = A p p')
    (hFuture : ∀ w ∈ numericHTopPool k S,
        ∀ w' ∈ numericHTopPool k S, w ≠ w' →
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          w w' (0 : Fin 1) = A w w')
    (hPhysicalColumns : ∀ p ∈ P, ∀ w ∈ numericHTopPool k S,
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          p w (0 : Fin 1) = c p (tau w) ∧
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          w p (0 : Fin 1) = c p (tau w))
    (hReferenceColumns : ∀ p ∈ P, ∀ w ∈ numericHTopPool k S,
        A p w = c p (tau w) ∧ A w p = c p (tau w)) :
    finitePoolCliqueCheck
      (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
        u v (0 : Fin 1))
      ell ((Finset.range (hPosition k (q a) g + 1)) ∪
        numericHTopPool k S) = false ↔
    finitePoolCliqueCheck A ell (numericHTopPool k S) = false ∧
      (∀ s : Finset Nat,
        s ⊆ numericHTopPool k S → IsDirectedCliqueOn A s →
        ∀ U : IntegerGraphSupport d ell,
          (s.filter (fun w => tau w ∈ U.1)).card ≤
            integerGraphAgeCanonical d ell
              (rawCliqueBlockBound ell
                (if g < a then a else a + 1)
                (finiteOldColumnRawBound A ell d P c) T) U) := by
  classical
  let W : Finset Nat := numericHTopPool k S
  let L : Nat → Nat → Bool :=
    fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
      u v (0 : Fin 1)
  let B : IntegerGraphSupport d ell → Nat :=
    finiteOldColumnRawBound A ell d P c
  let cap : Nat := if g < a then a else a + 1
  have hCapLe : cap ≤ r := by
    dsimp [cap]
    split_ifs <;> omega
  have hCapLt : cap < ell := by omega
  have hPSub : P ⊆ Finset.range (hPosition k (q a) g + 1) := by
    intro p hp
    exact Finset.mem_range.mpr (hP p hp)
  have hPDisjointW : Disjoint P W := by
    apply Finset.disjoint_left.mpr
    intro p hp hpW
    have hPositionP := hP p hp
    obtain ⟨j, hj, hjEq⟩ := Finset.mem_image.mp hpW
    have hEarlier : q a < j := hLater a ha j hj
    have hPositionLt :=
      hPosition_lt_of_block_lt k (q a) j g k hgk hEarlier
    omega
  have hPFreeL : finitePoolCliqueCheck L ell P = false := by
    apply (finitePoolCliqueCheck_false_iff_capacity_lt L ell P).2
    have hMonotone := finiteDirectedCliqueCapacity_mono
      L P (Finset.range (hPosition k (q a) g + 1)) hPSub
    have hBound :=
      (finitePoolCliqueCheck_false_iff_capacity_lt
        L ell (Finset.range (hPosition k (q a) g + 1))).1 hPast
    omega
  have hPFreeA : finitePoolCliqueCheck A ell P = false :=
    (finitePoolCliqueCheck_false_iff_reference
      L A ell P hOld).mp hPFreeL
  have hWhole := finiteNumericH_ordered_whole_prefix_marked_age_iff
    E A hSym k M r a g ell d q ha hr hgk hOrder hClique
    S hLater tau T.1 hUniform c P hP hNoPQ
    hOriginalGapZeros hPast hOld hFuture
    hPhysicalColumns hReferenceColumns
  have hRef := finiteOldFuture_free_iff_canonical_support
    A ell d P W tau c hPDisjointW hReferenceColumns hPFreeA
  have hWFilterSub :
      W.filter (fun w => tau w ∈ T.1) ⊆ W :=
    Finset.filter_subset _ _
  have hFutureCapEq :
      finiteDirectedCliqueCapacity L
        (markedSupportPool d W tau T.1) =
      finiteDirectedCliqueCapacity A
        (W.filter (fun w => tau w ∈ T.1)) := by
    have hExact := finiteDirectedCliqueCapacity_eq_of_offDiagonal_agreement
      A L (W.filter (fun w => tau w ∈ T.1))
      (by
        intro x hx y hy hxy
        exact (hFuture x (hWFilterSub hx) y (hWFilterSub hy) hxy).symm)
    simpa [markedSupportPool] using hExact
  constructor
  · intro hPhysicalFree
    obtain ⟨hOldFutureFree, hBudgetL⟩ := hWhole.mp hPhysicalFree
    obtain ⟨hWFree, hCanonBefore⟩ := hRef.mp hOldFutureFree
    have hRawBefore :
        ∀ s : Finset Nat, s ⊆ W → IsDirectedCliqueOn A s →
          ∀ U : IntegerGraphSupport d ell,
            (s.filter (fun w => tau w ∈ U.1)).card ≤ B U :=
      (finiteClique_all_constraints_integerCanonical_iff
        A W tau B hWFree).mp hCanonBefore
    have hBudgetA : cap +
        finiteDirectedCliqueCapacity A
          (W.filter (fun w => tau w ∈ T.1)) < ell := by
      rw [← hFutureCapEq]
      exact hBudgetL
    have hAfter :=
      (finiteClique_full_constraints_canonical_block_iff
        A W tau B T cap hCapLt hWFree).mp
        ⟨hRawBefore, hBudgetA⟩
    exact ⟨hWFree, hAfter⟩
  · rintro ⟨hWFree, hAfter⟩
    obtain ⟨hRawBefore, hBudgetA⟩ :=
      (finiteClique_full_constraints_canonical_block_iff
        A W tau B T cap hCapLt hWFree).mpr hAfter
    have hCanonBefore :
        ∀ s : Finset Nat, s ⊆ W → IsDirectedCliqueOn A s →
          ∀ U : IntegerGraphSupport d ell,
            (s.filter (fun w => tau w ∈ U.1)).card ≤
              integerGraphAgeCanonical d ell B U :=
      (finiteClique_all_constraints_integerCanonical_iff
        A W tau B hWFree).mpr hRawBefore
    have hOldFutureFree : finitePoolCliqueCheck A ell (P ∪ W) = false :=
      hRef.mpr ⟨hWFree, hCanonBefore⟩
    apply hWhole.mpr
    refine ⟨hOldFutureFree, ?_⟩
    rw [hFutureCapEq]
    exact hBudgetA

/-- When the canonicalized old reference table has the genuine upper
age of a cover, applying one raw support budget to the physical
prefix has EXACTLY the predicted upper/lower labelled clique profile.
This helper is independent of physical geometry and uses the full
joint integer-witness system, not equality of raw bound functions. -/
theorem finiteClique_canonical_cover_of_reference_eq
    (d ell r : Nat)
    (B lower upper : IntegerGraphSupport d ell → Nat)
    (T : IntegerGraphSupport d ell)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (hEll : ell = lower T + r + 1)
    (hAt : upper T = lower T + 1)
    (hReference : integerGraphAgeCanonical d ell B = upper)
    (cap : Nat) (hCap : cap ≤ r)
    (A : Nat → Nat → Bool)
    (W : Finset Nat) (tau : Nat → Fin d)
    (hWFree : finitePoolCliqueCheck A ell W = false) :
    (∀ s : Finset Nat, s ⊆ W → IsDirectedCliqueOn A s →
      ∀ U : IntegerGraphSupport d ell,
        (s.filter (fun w => tau w ∈ U.1)).card ≤
          integerGraphAgeCanonical d ell
            (rawCliqueBlockBound ell cap B T) U) ↔
    (∀ s : Finset Nat, s ⊆ W → IsDirectedCliqueOn A s →
      ∀ U : IntegerGraphSupport d ell,
        (s.filter (fun w => tau w ∈ U.1)).card ≤
          (if cap < r then upper else lower) U) := by
  have hLower := (hCover.lower_age.1 T).1
  have hCapLt : cap < ell := by omega
  have hBefore := finiteClique_all_constraints_integerCanonical_iff
    A W tau B hWFree
  rw [hReference] at hBefore
  have hBlock := finiteClique_full_constraints_canonical_block_iff
    A W tau B T cap hCapLt hWFree
  have hCoverBlock := finiteClique_full_constraints_cover_step_iff
    d ell r lower upper T hCover hEll hAt cap hCap A W tau hWFree
  constructor
  · intro h
    obtain ⟨hRaw, hBudget⟩ := hBlock.mpr h
    exact hCoverBlock.mp ⟨hBefore.mpr hRaw, hBudget⟩
  · intro h
    obtain ⟨hUpper, hBudget⟩ := hCoverBlock.mpr h
    exact hBlock.mp ⟨hBefore.mp hUpper, hBudget⟩

/-- Physical entire-prefix canonical cover effect for one finite
selected future W, under the EXPLICIT original stage obligations.

The exact reference-age invariant is pointwise across all nonempty
supports, NOT just the selected T-coordinate. No universal physical
future or global resolved-copy induction is claimed. -/
theorem finiteNumericH_whole_prefix_cover_step_iff
    (E A : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k M r a g ell d : Nat) (q : Nat → Nat)
    (ha : a < r) (hr : r ≤ k + 1) (hgk : g ≤ k)
    (hOrder : ∀ b c, b < c → c < r → q b < q c)
    (hClique : ∀ b c, b < c → c < r → E (q b) (q c) = true)
    (S : Finset Nat)
    (hLater : ∀ b, b < r → ∀ j ∈ S, q b < j)
    (tau : Nat → Fin d) (T : IntegerGraphSupport d ell)
    (hUniform : ∀ b, b < r → ∀ j ∈ S,
      E (q b) j = decide (tau (hPosition k j k) ∈ T.1))
    (c : Nat → Fin d → Bool)
    (P : Finset Nat)
    (hP : ∀ p ∈ P, p < hPosition k (q a) g + 1)
    (hNoPQ : ∀ p ∈ P, ∀ u ∈ orderedReservedNumericPrefix k q a g,
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          p u (0 : Fin 1) = false)
    (hOriginalGapZeros : ∀ i t : Nat,
      t ≤ k →
      hPosition k i t ∈
        numericPrefixGapPool (hPosition k (q a) g + 1) P
          (orderedReservedNumericPrefix k q a g) →
      ∀ j ∈ S, E i j = false)
    (hPast : finitePoolCliqueCheck
      (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
        u v (0 : Fin 1))
      ell (Finset.range (hPosition k (q a) g + 1)) = false)
    (hOld : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' →
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          p p' (0 : Fin 1) = A p p')
    (hFuture : ∀ w ∈ numericHTopPool k S,
        ∀ w' ∈ numericHTopPool k S, w ≠ w' →
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          w w' (0 : Fin 1) = A w w')
    (hPhysicalColumns : ∀ p ∈ P, ∀ w ∈ numericHTopPool k S,
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          p w (0 : Fin 1) = c p (tau w) ∧
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          w p (0 : Fin 1) = c p (tau w))
    (hReferenceColumns : ∀ p ∈ P, ∀ w ∈ numericHTopPool k S,
        A p w = c p (tau w) ∧ A w p = c p (tau w))
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (hEll : ell = lower T + r + 1)
    (hAt : upper T = lower T + 1)
    (hReferenceAge :
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound A ell d P c) = upper) :
    finitePoolCliqueCheck
      (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
        u v (0 : Fin 1))
      ell ((Finset.range (hPosition k (q a) g + 1)) ∪
        numericHTopPool k S) = false ↔
    finitePoolCliqueCheck A ell (numericHTopPool k S) = false ∧
      (∀ s : Finset Nat,
        s ⊆ numericHTopPool k S → IsDirectedCliqueOn A s →
        ∀ U : IntegerGraphSupport d ell,
          (s.filter (fun w => tau w ∈ U.1)).card ≤
            (if (if g < a then a else a + 1) < r
             then upper else lower) U) := by
  have hPositive : 1 ≤ lower T := (hCover.lower_age.1 T).1
  have hrEll : r < ell := by omega
  have hGeneral := finiteNumericH_whole_prefix_raw_canonical_block_iff
    E A hSym k M r a g ell d q ha hr hgk hrEll
    hOrder hClique S hLater tau T hUniform c P hP hNoPQ
    hOriginalGapZeros hPast hOld hFuture hPhysicalColumns
    hReferenceColumns
  have hCapLe : (if g < a then a else a + 1) ≤ r := by
    split_ifs <;> omega
  let W : Finset Nat := numericHTopPool k S
  have hProfiles (hWFree : finitePoolCliqueCheck A ell W = false) :=
    finiteClique_canonical_cover_of_reference_eq
      d ell r (finiteOldColumnRawBound A ell d P c)
      lower upper T hCover hEll hAt hReferenceAge
      (if g < a then a else a + 1) hCapLe
      A W tau hWFree
  constructor
  · intro hFree
    obtain ⟨hWFree, hRawProfile⟩ := hGeneral.mp hFree
    exact ⟨hWFree, (hProfiles hWFree).mp hRawProfile⟩
  · rintro ⟨hWFree, hCoverProfile⟩
    exact hGeneral.mpr
      ⟨hWFree, (hProfiles hWFree).mpr hCoverProfile⟩

/-- The reserved real-copy prefix reaches capacity r only on the
FINAL original a=r-1, at generation g>=a. It cannot reach r
during any earlier original or any lower generation. -/
theorem orderedReservedCapacity_reaches_full_iff
    (r a g : Nat) (ha : a < r) :
    (if g < a then a else a + 1) = r ↔
      a + 1 = r ∧ a ≤ g := by
  by_cases hg : g < a
  · have hne : a ≠ r := by omega
    have hnot : ¬ a ≤ g := by omega
    simp [hg, hne, hnot]
  · have hge : a ≤ g := by omega
    simp [hg, hge]

/-- The complement of the final event: the sharp reserved capacity is
strictly below the block size precisely before the last-original
threshold or at a generation lower than the current original rank. -/
theorem orderedReservedCapacity_before_full_iff
    (r a g : Nat) (ha : a < r) :
    (if g < a then a else a + 1) < r ↔
      a + 1 < r ∨ g < a := by
  by_cases hg : g < a
  · simp [hg, ha]
  · simp [hg]

/-- Replace the nested capacity threshold in a canonical-cover age
expression by the unique final physical original/generation event.
No assumption about an Henson schedule is used in this arithmetic
identity, and no new physical existence is inferred. -/
theorem orderedReservedCapacity_cover_age_normal_form
    {α : Type} (r a g : Nat) (ha : a < r)
    (lower upper : α → Nat) :
    (if (if g < a then a else a + 1) < r then upper else lower) =
      (if a + 1 = r ∧ a ≤ g then lower else upper) := by
  classical
  by_cases hFinal : a + 1 = r ∧ a ≤ g
  · have hEq : (if g < a then a else a + 1) = r :=
      (orderedReservedCapacity_reaches_full_iff r a g ha).2 hFinal
    have hNot : ¬ (if g < a then a else a + 1) < r := by omega
    simp [hFinal, hNot]
  · have hCapLe : (if g < a then a else a + 1) ≤ r := by
      split_ifs <;> omega
    have hCapNe : (if g < a then a else a + 1) ≠ r := by
      intro hEq
      exact hFinal
        ((orderedReservedCapacity_reaches_full_iff r a g ha).1 hEq)
    have hLt : (if g < a then a else a + 1) < r := by omega
    simp [hFinal, hLt]

#print axioms Kk.orderedReservedCapacity_reaches_full_iff
#print axioms Kk.orderedReservedCapacity_before_full_iff
#print axioms Kk.orderedReservedCapacity_cover_age_normal_form

#print axioms Kk.finiteDirectedCliqueCapacity_eq_of_offDiagonal_agreement
#print axioms Kk.finiteNumericH_whole_prefix_raw_canonical_block_iff
#print axioms Kk.finiteClique_canonical_cover_of_reference_eq
#print axioms Kk.finiteNumericH_whole_prefix_cover_step_iff

end Kk
