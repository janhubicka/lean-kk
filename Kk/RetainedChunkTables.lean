import Kk.RetainedPrefixSource
import Kk.HensonEncoding
import SuccessorTree.V10.HFinitePartial
import Mathlib.Tactic

/-!
# Concrete height-four retained coordinate tables

English proof and independent review were committed before implementation:
`docs/retained_chunk_matrix_english_20261124.md` and
`docs/audits/2026-11-24-retained-chunk-matrix-review-generation-zero.md`.

The common finite data are ordered retained base members and their ordinary
base table. Each auxiliary member uses four free slots and five real slots;
a coded member uses just the TOP free and real slots. The theorems allow any
common sequence of these tags, hence include both masks and all selected
prefixes. Actual base embeddings may have different omitted physical gaps.

We derive the complete ordinary and auxiliary E tables from those concrete
data. Equality of compressed tables or of inverse sources is not a premise.
Extracting the tags from the actual record and identifying their enumeration
with the exact AlgorithmRun level map remain separate application steps.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Free tags 0,1,2,3 stand for generations 1,2,3,4. Real tags have
their literal generation 0,1,2,3,4. Event-member indices remain distinct
even when two members have identical visible incidence patterns. -/
inductive K4RetainedSlot (B : Nat) where
  | anchor
  | free (member : Fin B) (generation : Fin 4)
  | real (member : Fin B) (generation : Fin 5)
  deriving DecidableEq

/-- Actual first missing E coordinate. TOP uses preceding generation 4,
so the four physical offsets are 1,3,5,9, including the TOP exception. -/
def k4RetainedFreeCoordinate (b : Nat) (r : Fin 4) : Nat :=
  hPosition 4 (b-1) (if r.val = 3 then 4 else r.val) + 1

/-- Physical realization of a common retained slot. -/
def k4RetainedSlotPosition {B : Nat} (base : Fin B → Nat) :
    K4RetainedSlot B → Nat
  | .anchor => 0
  | .free i r => k4RetainedFreeCoordinate (base i) r
  | .real i g => hPosition 4 (base i) g.val

/-- The abstract order of ALL slots, before restricting coded chunks to
their TOP free/real pair. Restriction preserves the order. -/
def k4RetainedSlotRank {B : Nat} : K4RetainedSlot B → Nat
  | .anchor => 0
  | .free i r => 1 + 9*i.val + r.val
  | .real i g => 1 + 9*i.val + 4 + g.val

private theorem retained_bool_eq_of_true_iff
    (a b : Bool) (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem retained_base_strictMono
    {B : Nat} (base : Fin B → Nat)
    (hGap : ∀ i j, i < j → base i + 2 ≤ base j) :
    StrictMono base := by
  intro i j hij
  have h := hGap i j hij
  omega

private theorem retained_base_lt_iff
    {B : Nat} (base : Fin B → Nat)
    (hGap : ∀ i j, i < j → base i + 2 ≤ base j)
    (i j : Fin B) : base i < base j ↔ i < j := by
  constructor
  · intro h
    by_contra hn
    have hji : j ≤ i := le_of_not_gt hn
    rcases lt_or_eq_of_le hji with hlt | heq
    · have hBack := hGap j i hlt
      omega
    · subst j
      omega
  · intro hij
    exact retained_base_strictMono base hGap hij

/-- A free slot is genuinely odd. This says nothing about its outgoing E. -/
theorem k4RetainedFreeCoordinate_odd (b : Nat) (r : Fin 4) :
    ∃ a : Nat, k4RetainedFreeCoordinate b r = 2*a+1 := by
  obtain ⟨a, ha⟩ :=
    hPosition_even 4 (b-1) (if r.val = 3 then 4 else r.val)
  exact ⟨a, congrArg (fun n : Nat => n+1) ha⟩

private theorem retained_free_bounds (b : Nat) (r : Fin 4) :
    10*(b-1)+1 ≤ k4RetainedFreeCoordinate b r ∧
      k4RetainedFreeCoordinate b r ≤ 10*(b-1)+9 := by
  have hr := r.isLt
  unfold k4RetainedFreeCoordinate hPosition
  split_ifs <;> omega

private theorem retained_free_lt_iff (b : Nat) (r s : Fin 4) :
    k4RetainedFreeCoordinate b r < k4RetainedFreeCoordinate b s ↔ r < s := by
  have hr := r.isLt
  have hs := s.isLt
  unfold k4RetainedFreeCoordinate hPosition
  split_ifs <;> change _ ↔ r.val < s.val <;> omega

/-- Complete combinatorial initial segment below one free slot. -/
def K4RetainedBeforeFree {B : Nat}
    (source : K4RetainedSlot B) (j : Fin B) (r : Fin 4) : Prop :=
  match source with
  | .anchor => True
  | .free i s => i < j ∨ (i = j ∧ s < r)
  | .real i _ => i < j

/-- Dummy-separated physical embeddings give the SAME strict initial
segment below every retained free coordinate. The anchor is included;
same-member free tags enter precisely at the strict generation inequality. -/
theorem k4RetainedSlot_before_free_iff
    {B : Nat} (base : Fin B → Nat)
    (hPositive : ∀ i, 0 < base i)
    (hGap : ∀ i j, i < j → base i + 2 ≤ base j)
    (source : K4RetainedSlot B) (j : Fin B) (r : Fin 4) :
    k4RetainedSlotPosition base source < k4RetainedFreeCoordinate (base j) r ↔
      K4RetainedBeforeFree source j r := by
  have hR := retained_free_bounds (base j) r
  have hJ := hPositive j
  cases source with
  | anchor =>
    change 0 < k4RetainedFreeCoordinate (base j) r ↔ True
    constructor
    · intro _
      trivial
    · intro _
      have hLower := hR.1
      omega
  | free i s =>
    change k4RetainedFreeCoordinate (base i) s <
        k4RetainedFreeCoordinate (base j) r ↔
      i < j ∨ (i = j ∧ s < r)
    have hS := retained_free_bounds (base i) s
    have hI := hPositive i
    rcases lt_trichotomy i j with hij | heq | hji
    · have hG := hGap i j hij
      have hLt : k4RetainedFreeCoordinate (base i) s <
          k4RetainedFreeCoordinate (base j) r := by omega
      exact ⟨fun _ => Or.inl hij, fun _ => hLt⟩
    · subst j
      simpa only [lt_self_iff_false, false_or, true_and] using
        retained_free_lt_iff (base i) s r
    · have hG := hGap j i hji
      have hNot : ¬ k4RetainedFreeCoordinate (base i) s <
          k4RetainedFreeCoordinate (base j) r := by omega
      constructor
      · exact fun h => False.elim (hNot h)
      · rintro (hij | ⟨heq, _⟩)
        · exact False.elim ((lt_asymm hji) hij)
        · subst j
          exact False.elim ((lt_irrefl i) hji)
  | real i g =>
    change hPosition 4 (base i) g.val <
      k4RetainedFreeCoordinate (base j) r ↔ i < j
    have hI := hPositive i
    have hg := g.isLt
    unfold hPosition
    constructor
    · intro h
      by_contra hn
      have hji : j ≤ i := le_of_not_gt hn
      rcases lt_or_eq_of_le hji with hlt | heq
      · have hG := hGap j i hlt
        omega
      · subst j
        omega
    · intro hij
      have hG := hGap i j hij
      omega

private theorem retained_exactE_initial_false
    (b g u : Nat) (hg : g ≤ 4) (hInitial : b = 0 ∨ g = 0) :
    exactHEBool 4 u (hPosition 4 b g) = false := by
  by_cases h : exactHEBool 4 u (hPosition 4 b g) = true
  · have hGen := (exactHEBool_at_real_iff 4 b g u hg).1 h
    exact False.elim
      ((generatedE_empty_of_initial 4 b g u (by decide) hInitial) hGen)
  · cases hb : exactHEBool 4 u (hPosition 4 b g) <;> simp_all

/-- Actual generation-zero originals have free level zero at height four.
This uses the exact finite numerical E relation, including target clipping. -/
theorem finiteNumericH_four_generation_zero_freeLevel
    {db du dd : Nat} (K : AgeTestModel db du dd) (N b : Nat) :
    (finiteNumericH K 4 N).freeLevel (hPosition 4 b 0) = 0 := by
  let A := finiteNumericH K 4 N
  have hNot : ¬ 0 < A.freeLevel (hPosition 4 b 0) := by
    intro hPositive
    have hE : A.E 0 (hPosition 4 b 0) = true :=
      (A.E_iff_freeLevel 0 (hPosition 4 b 0)).2 hPositive
    have hExact := ((finiteNumericHE_true_iff 4 N 0 (hPosition 4 b 0)).1 hE).2
    rw [retained_exactE_initial_false b 0 0 (by decide) (Or.inr rfl)] at hExact
    cases hExact
  change A.freeLevel (hPosition 4 b 0) = 0
  omega

private theorem retained_exactE_positive_real_iff
    (b u : Nat) (hb : 0 < b) (r : Fin 4) :
    exactHEBool 4 u (hPosition 4 b (r.val+1)) = true ↔
      u < k4RetainedFreeCoordinate b r := by
  have hr := r.isLt
  rw [exactHEBool_at_real_iff 4 b (r.val+1) u (by omega)]
  by_cases hTop : r.val = 3
  · have hGen : r.val+1 = 4 := by omega
    rw [hGen]
    simpa only [k4RetainedFreeCoordinate, hTop, ite_true] using
      generatedE_top_iff 4 b u hb (by decide)
  · have hNonTop : r.val+1 < 4 := by omega
    have hColumn := generatedE_nonTop_iff
      4 b (r.val+1) u hb (by omega) hNonTop
    simpa only [k4RetainedFreeCoordinate, hTop, ite_false,
      nonTopFreeCut, Nat.add_sub_cancel] using hColumn

/-- Literal combinatorial E matrix, including empty odd/anchor/real-zero
columns. A positive target is identified by its own retained free tag. -/
def K4RetainedEAtom {B : Nat}
    (source target : K4RetainedSlot B) : Prop :=
  match target with
  | .anchor => False
  | .free _ _ => False
  | .real j g => ∃ r : Fin 4, g.val = r.val+1 ∧
      K4RetainedBeforeFree source j r

/-- The complete physical E table is determined by the slot tags and
their common member order. No ordinary edges or capacity ages occur. -/
theorem k4RetainedSlot_exactE_iff
    {B : Nat} (base : Fin B → Nat)
    (hPositive : ∀ i, 0 < base i)
    (hGap : ∀ i j, i < j → base i + 2 ≤ base j)
    (source target : K4RetainedSlot B) :
    exactHEBool 4 (k4RetainedSlotPosition base source)
        (k4RetainedSlotPosition base target) = true ↔
      K4RetainedEAtom source target := by
  cases target with
  | anchor =>
    change exactHEBool 4 (k4RetainedSlotPosition base source) 0 = true ↔ False
    have hZero := retained_exactE_initial_false
      0 0 (k4RetainedSlotPosition base source) (by decide) (Or.inl rfl)
    change exactHEBool 4 (k4RetainedSlotPosition base source) 0 = false at hZero
    rw [hZero]
    simp
  | free j r =>
    obtain ⟨a, ha⟩ := k4RetainedFreeCoordinate_odd (base j) r
    change exactHEBool 4 (k4RetainedSlotPosition base source)
      (k4RetainedFreeCoordinate (base j) r) = true ↔ False
    rw [ha, exactHEBool_odd_target_false]
    simp
  | real j g =>
    change exactHEBool 4 (k4RetainedSlotPosition base source)
        (hPosition 4 (base j) g.val) = true ↔
      ∃ r : Fin 4, g.val = r.val+1 ∧ K4RetainedBeforeFree source j r
    constructor
    · intro hE
      have hgPositive : 0 < g.val := by
        by_contra hn
        have hgZero : g.val = 0 := by omega
        rw [hgZero, retained_exactE_initial_false (base j) 0
          (k4RetainedSlotPosition base source) (by decide) (Or.inr rfl)] at hE
        cases hE
      let r : Fin 4 := ⟨g.val-1, by have hg := g.isLt; omega⟩
      have hGen : g.val = r.val+1 := by dsimp [r]; omega
      refine ⟨r, hGen, ?_⟩
      rw [hGen] at hE
      exact (k4RetainedSlot_before_free_iff base hPositive hGap source j r).1
        ((retained_exactE_positive_real_iff (base j)
          (k4RetainedSlotPosition base source) (hPositive j) r).1 hE)
    · rintro ⟨r, hGen, hBefore⟩
      rw [hGen]
      exact (retained_exactE_positive_real_iff (base j)
        (k4RetainedSlotPosition base source) (hPositive j) r).2
        ((k4RetainedSlot_before_free_iff base hPositive hGap source j r).2 hBefore)

/-- Finite-carrier restriction leaves the literal slot E table unchanged
when the target slot is inside that carrier. -/
theorem k4RetainedSlot_finiteE_iff
    {db du dd B : Nat} (K : AgeTestModel db du dd) (N : Nat)
    (base : Fin B → Nat)
    (hPositive : ∀ i, 0 < base i)
    (hGap : ∀ i j, i < j → base i + 2 ≤ base j)
    (source target : K4RetainedSlot B)
    (hInside : k4RetainedSlotPosition base target < N) :
    (finiteNumericH K 4 N).E
        (k4RetainedSlotPosition base source)
        (k4RetainedSlotPosition base target) = true ↔
      K4RetainedEAtom source target := by
  change finiteNumericHE 4 N
      (k4RetainedSlotPosition base source)
      (k4RetainedSlotPosition base target) = true ↔ _
  rw [finiteNumericHE_true_iff]
  constructor
  · intro h
    exact (k4RetainedSlot_exactE_iff base hPositive hGap source target).1 h.2
  · intro h
    exact ⟨hInside,
      (k4RetainedSlot_exactE_iff base hPositive hGap source target).2 h⟩

private theorem retained_real_binary_true_transfer
    {B : Nat} (E F : Nat → Nat → Bool)
    (baseF baseG : Fin B → Nat)
    (hOrder : ∀ i j, baseF i < baseF j → baseG i < baseG j)
    (hBase : ∀ i j, E (baseF i) (baseF j) = F (baseG i) (baseG j))
    (i j : Fin B) (g h : Fin 5)
    (hPositive : hNumericBinary (normalizedGraphModel E).binary 4
      (hPosition 4 (baseF i) g.val) (hPosition 4 (baseF j) h.val)
      (0 : Fin 1) = true) :
    hNumericBinary (normalizedGraphModel F).binary 4
      (hPosition 4 (baseG i) g.val) (hPosition 4 (baseG j) h.val)
      (0 : Fin 1) = true := by
  have hg : g.val ≤ 4 := by have h := g.isLt; omega
  have hh : h.val ≤ 4 := by have h := h.isLt; omega
  obtain ⟨u,v,q,m,huv,hq,hm,hGate,hDir⟩ :=
    (hNumericBinary_true_iff (normalizedGraphModel E).binary 4
      (hPosition 4 (baseF i) g.val) (hPosition 4 (baseF j) h.val)
      (0 : Fin 1)).1 hPositive
  apply (hNumericBinary_true_iff (normalizedGraphModel F).binary 4
    (hPosition 4 (baseG i) g.val) (hPosition 4 (baseG j) h.val)
    (0 : Fin 1)).2
  rcases hDir with ⟨hX,hY,hBit⟩ | ⟨hX,hY,hBit⟩
  · obtain ⟨hi,hgEq⟩ := hPosition_injective_bounded
      4 (baseF i) g.val u q hg hq hX
    obtain ⟨hj,hhEq⟩ := hPosition_injective_bounded
      4 (baseF j) h.val v m hh hm hY
    have hChron : baseF i < baseF j := by simpa only [hi,hj] using huv
    have hGate' : g.val < h.val ∨ (g.val = h.val ∧ h.val = 4) := by
      simpa only [hgEq,hhEq] using hGate
    have hSource : E (baseF i) (baseF j) = true := by
      change E u v = true at hBit
      simpa only [hi,hj] using hBit
    have hTarget : F (baseG i) (baseG j) = true :=
      (hBase i j).symm.trans hSource
    exact ⟨baseG i,baseG j,g.val,h.val,hOrder i j hChron,hg,hh,hGate',
      Or.inl ⟨rfl,rfl,hTarget⟩⟩
  · obtain ⟨hi,hgEq⟩ := hPosition_injective_bounded
      4 (baseF i) g.val v m hg hm hX
    obtain ⟨hj,hhEq⟩ := hPosition_injective_bounded
      4 (baseF j) h.val u q hh hq hY
    have hChron : baseF j < baseF i := by simpa only [hi,hj] using huv
    have hGate' : h.val < g.val ∨ (h.val = g.val ∧ g.val = 4) := by
      simpa only [hgEq,hhEq] using hGate
    have hSource : E (baseF i) (baseF j) = true := by
      change E v u = true at hBit
      simpa only [hi,hj] using hBit
    have hTarget : F (baseG i) (baseG j) = true :=
      (hBase i j).symm.trans hSource
    exact ⟨baseG j,baseG i,h.val,g.val,hOrder j i hChron,hh,hg,hGate',
      Or.inr ⟨rfl,rfl,hTarget⟩⟩

private theorem retained_binary_zero_left_false
    (E : Nat → Nat → Bool) (hZero : ∀ j, E 0 j = false) (y : Nat) :
    hNumericBinary (normalizedGraphModel E).binary 4 0 y (0 : Fin 1) = false := by
  by_cases h : hNumericBinary (normalizedGraphModel E).binary
      4 0 y (0 : Fin 1) = true
  · obtain ⟨i,j,q,m,hij,_hq,_hm,_hGate,hDir⟩ :=
      (hNumericBinary_true_iff (normalizedGraphModel E).binary
        4 0 y (0 : Fin 1)).1 h
    rcases hDir with ⟨hX,_hY,hBit⟩ | ⟨hX,_hY,_hBit⟩
    · have hi : i = 0 := by unfold hPosition at hX; omega
      change E i j = true at hBit
      rw [hi,hZero j] at hBit
      cases hBit
    · unfold hPosition at hX
      omega
  · cases hb : hNumericBinary (normalizedGraphModel E).binary
      4 0 y (0 : Fin 1) <;> simp_all

private theorem retained_binary_zero_right_false
    (E : Nat → Nat → Bool) (hZero : ∀ i, E i 0 = false) (x : Nat) :
    hNumericBinary (normalizedGraphModel E).binary 4 x 0 (0 : Fin 1) = false := by
  by_cases h : hNumericBinary (normalizedGraphModel E).binary
      4 x 0 (0 : Fin 1) = true
  · obtain ⟨i,j,q,m,hij,_hq,_hm,_hGate,hDir⟩ :=
      (hNumericBinary_true_iff (normalizedGraphModel E).binary
        4 x 0 (0 : Fin 1)).1 h
    rcases hDir with ⟨_hX,hY,_hBit⟩ | ⟨_hX,hY,hBit⟩
    · unfold hPosition at hY
      omega
    · have hi : i = 0 := by unfold hPosition at hY; omega
      change E j i = true at hBit
      rw [hi,hZero j] at hBit
      cases hBit
  · cases hb : hNumericBinary (normalizedGraphModel E).binary
      4 x 0 (0 : Fin 1) <;> simp_all

/-- All ordinary binary entries are fixed by the common directed
retained-base table and slot tags. The real anchor's two-direction
isolation is explicit; no symmetry assumption is needed by this result. -/
theorem k4RetainedSlot_ordinary_eq
    {B : Nat} (E F : Nat → Nat → Bool)
    (hZeroEL : ∀ j, E 0 j = false) (hZeroER : ∀ i, E i 0 = false)
    (hZeroFL : ∀ j, F 0 j = false) (hZeroFR : ∀ i, F i 0 = false)
    (baseF baseG : Fin B → Nat)
    (hGapF : ∀ i j, i < j → baseF i + 2 ≤ baseF j)
    (hGapG : ∀ i j, i < j → baseG i + 2 ≤ baseG j)
    (hBase : ∀ i j, E (baseF i) (baseF j) = F (baseG i) (baseG j))
    (source target : K4RetainedSlot B) :
    hNumericBinary (normalizedGraphModel E).binary 4
        (k4RetainedSlotPosition baseF source)
        (k4RetainedSlotPosition baseF target) (0 : Fin 1) =
      hNumericBinary (normalizedGraphModel F).binary 4
        (k4RetainedSlotPosition baseG source)
        (k4RetainedSlotPosition baseG target) (0 : Fin 1) := by
  cases source with
  | anchor =>
    exact (retained_binary_zero_left_false E hZeroEL _).trans
      (retained_binary_zero_left_false F hZeroFL _).symm
  | free i r =>
    obtain ⟨a, ha⟩ := k4RetainedFreeCoordinate_odd (baseF i) r
    obtain ⟨b, hb⟩ := k4RetainedFreeCoordinate_odd (baseG i) r
    change hNumericBinary (normalizedGraphModel E).binary 4
        (k4RetainedFreeCoordinate (baseF i) r)
        (k4RetainedSlotPosition baseF target) (0 : Fin 1) =
      hNumericBinary (normalizedGraphModel F).binary 4
        (k4RetainedFreeCoordinate (baseG i) r)
        (k4RetainedSlotPosition baseG target) (0 : Fin 1)
    rw [ha,hb,hNumericBinary_odd_left_false,hNumericBinary_odd_left_false]
  | real i g =>
    cases target with
    | anchor =>
      exact (retained_binary_zero_right_false E hZeroER _).trans
        (retained_binary_zero_right_false F hZeroFR _).symm
    | free j r =>
      obtain ⟨a, ha⟩ := k4RetainedFreeCoordinate_odd (baseF j) r
      obtain ⟨b, hb⟩ := k4RetainedFreeCoordinate_odd (baseG j) r
      change hNumericBinary (normalizedGraphModel E).binary 4
          (hPosition 4 (baseF i) g.val) (k4RetainedFreeCoordinate (baseF j) r)
          (0 : Fin 1) =
        hNumericBinary (normalizedGraphModel F).binary 4
          (hPosition 4 (baseG i) g.val) (k4RetainedFreeCoordinate (baseG j) r)
          (0 : Fin 1)
      rw [ha,hb,hNumericBinary_odd_right_false,hNumericBinary_odd_right_false]
    | real j h =>
      apply retained_bool_eq_of_true_iff
      constructor
      · exact retained_real_binary_true_transfer E F baseF baseG
          (fun i j hij => (retained_base_lt_iff baseG hGapG i j).2
            ((retained_base_lt_iff baseF hGapF i j).1 hij))
          hBase i j g h
      · exact retained_real_binary_true_transfer F E baseG baseF
          (fun i j hij => (retained_base_lt_iff baseF hGapF i j).2
            ((retained_base_lt_iff baseG hGapG i j).1 hij))
          (fun i j => (hBase i j).symm) i j g h

private theorem retained_numeric_diagonal_false
    (E : Nat → Nat → Bool) (hLoops : ∀ i, E i i = false)
    (x : Nat) (t : Fin 1) :
    hNumericSingleton (normalizedGraphModel E).diagonal 4 x t = false := by
  classical
  unfold hNumericSingleton
  split_ifs with hReal
  · change E (Classical.choose hReal) (Classical.choose hReal) = false
    exact hLoops _
  · rfl

/-- Pull back the actual finite numerical-H code along a given common
tag sequence. Both masks (whole auxiliary chunks or just coded TOP pairs)
and any initial segment are allowed; no coordinate comparison is assumed. -/
noncomputable def k4RetainedSlotCode
    {B M : Nat} (E : Nat → Nat → Bool) (N : Nat)
    (base : Fin B → Nat) (tags : Fin M → K4RetainedSlot B)
    (hInside : ∀ i, k4RetainedSlotPosition base (tags i) < N) :
    FinitePartialCode 1 0 1 :=
  (FinitePartialCode.ofEnumerated
    (finiteNumericH (normalizedGraphModel E) 4 N)).reindex M
      (fun i => ⟨k4RetainedSlotPosition base (tags i), hInside i⟩)

/-- Complete retained physical codes are equal in two actual finite
occurrences with the same directed retained-base incidences. This derives
all four table equalities, including every absent E and ordinary atom.

The common sequence can be empty or repeated; order and injectivity for
the intended retained enumeration are established separately. -/
theorem k4RetainedSlotCode_eq_of_base_table
    {B M : Nat} (E F : Nat → Nat → Bool)
    (hLoopsE : ∀ i, E i i = false) (hLoopsF : ∀ i, F i i = false)
    (hZeroEL : ∀ j, E 0 j = false) (hZeroER : ∀ i, E i 0 = false)
    (hZeroFL : ∀ j, F 0 j = false) (hZeroFR : ∀ i, F i 0 = false)
    (N₁ N₂ : Nat) (baseF baseG : Fin B → Nat)
    (hPositiveF : ∀ i, 0 < baseF i) (hPositiveG : ∀ i, 0 < baseG i)
    (hGapF : ∀ i j, i < j → baseF i + 2 ≤ baseF j)
    (hGapG : ∀ i j, i < j → baseG i + 2 ≤ baseG j)
    (hBase : ∀ i j, E (baseF i) (baseF j) = F (baseG i) (baseG j))
    (tags : Fin M → K4RetainedSlot B)
    (hInsideF : ∀ i, k4RetainedSlotPosition baseF (tags i) < N₁)
    (hInsideG : ∀ i, k4RetainedSlotPosition baseG (tags i) < N₂) :
    k4RetainedSlotCode E N₁ baseF tags hInsideF =
      k4RetainedSlotCode F N₂ baseG tags hInsideG := by
  unfold k4RetainedSlotCode FinitePartialCode.reindex FinitePartialCode.ofEnumerated
  congr 1
  · funext i j t
    have ht : t = (0 : Fin 1) := Subsingleton.elim _ _
    subst t
    exact k4RetainedSlot_ordinary_eq E F hZeroEL hZeroER hZeroFL hZeroFR
      baseF baseG hGapF hGapG hBase (tags i) (tags j)
  · funext i t
    exact Fin.elim0 t
  · funext i t
    exact (retained_numeric_diagonal_false E hLoopsE
      (k4RetainedSlotPosition baseF (tags i)) t).trans
      (retained_numeric_diagonal_false F hLoopsF
        (k4RetainedSlotPosition baseG (tags i)) t).symm
  · funext i j
    apply retained_bool_eq_of_true_iff
    exact (k4RetainedSlot_finiteE_iff (normalizedGraphModel E) N₁
      baseF hPositiveF hGapF (tags i) (tags j) (hInsideF j)).trans
      (k4RetainedSlot_finiteE_iff (normalizedGraphModel F) N₂
        baseG hPositiveG hGapG (tags i) (tags j) (hInsideG j)).symm

private theorem retained_free_before_same_real
    (b : Nat) (hb : 0 < b) (r : Fin 4) (g : Fin 5) :
    k4RetainedFreeCoordinate b r < hPosition 4 b g.val := by
  have hFree := retained_free_bounds b r
  unfold hPosition
  omega

/-- Different event-member/generation tags have different abstract ranks.
Repeated incidence templates do not identify their coordinates. -/
theorem k4RetainedSlotRank_injective (B : Nat) :
    Function.Injective (@k4RetainedSlotRank B) := by
  intro source target hEq
  cases source with
  | anchor =>
    cases target with
    | anchor => rfl
    | free j s => dsimp [k4RetainedSlotRank] at hEq; omega
    | real j h => dsimp [k4RetainedSlotRank] at hEq; omega
  | free i r =>
    have hr := r.isLt
    cases target with
    | anchor => dsimp [k4RetainedSlotRank] at hEq; omega
    | free j s =>
      have hs := s.isLt
      dsimp [k4RetainedSlotRank] at hEq
      have hi : i = j := Fin.ext (by omega)
      subst j
      have hg : r = s := Fin.ext (by omega)
      subst s
      rfl
    | real j h =>
      have hh := h.isLt
      dsimp [k4RetainedSlotRank] at hEq
      omega
  | real i g =>
    have hg := g.isLt
    cases target with
    | anchor => dsimp [k4RetainedSlotRank] at hEq; omega
    | free j s =>
      have hs := s.isLt
      dsimp [k4RetainedSlotRank] at hEq
      omega
    | real j h =>
      have hh := h.isLt
      dsimp [k4RetainedSlotRank] at hEq
      have hi : i = j := Fin.ext (by omega)
      subst j
      have hgen : g = h := Fin.ext (by omega)
      subst h
      rfl

/-- Dummy separation makes every retained coordinate occur in the exact
common slot order, regardless of the number of intervening omitted bases. -/
theorem k4RetainedSlotPosition_lt_of_rank_lt
    {B : Nat} (base : Fin B → Nat)
    (hPositive : ∀ i, 0 < base i)
    (hGap : ∀ i j, i < j → base i + 2 ≤ base j)
    (source target : K4RetainedSlot B)
    (hRank : k4RetainedSlotRank source < k4RetainedSlotRank target) :
    k4RetainedSlotPosition base source < k4RetainedSlotPosition base target := by
  cases source with
  | anchor =>
    cases target with
    | anchor => dsimp [k4RetainedSlotRank] at hRank; omega
    | free j s =>
      have hFree := retained_free_bounds (base j) s
      change 0 < k4RetainedFreeCoordinate (base j) s
      omega
    | real j h =>
      have hBase := hPositive j
      change 0 < hPosition 4 (base j) h.val
      unfold hPosition
      omega
  | free i r =>
    have hr := r.isLt
    cases target with
    | anchor => dsimp [k4RetainedSlotRank] at hRank; omega
    | free j s =>
      have hs := s.isLt
      have hij : i ≤ j := by
        change i.val ≤ j.val
        dsimp [k4RetainedSlotRank] at hRank
        omega
      apply (k4RetainedSlot_before_free_iff base hPositive hGap (.free i r) j s).2
      rcases lt_or_eq_of_le hij with hlt | heq
      · exact Or.inl hlt
      · subst j
        exact Or.inr ⟨rfl, by
          change r.val < s.val
          dsimp [k4RetainedSlotRank] at hRank
          omega⟩
    | real j h =>
      have hh := h.isLt
      have hij : i ≤ j := by
        change i.val ≤ j.val
        dsimp [k4RetainedSlotRank] at hRank
        omega
      rcases lt_or_eq_of_le hij with hlt | heq
      · have hFirst := (k4RetainedSlot_before_free_iff
          base hPositive hGap (.free i r) j (0 : Fin 4)).2 (Or.inl hlt)
        exact hFirst.trans (retained_free_before_same_real
          (base j) (hPositive j) (0 : Fin 4) h)
      · subst j
        exact retained_free_before_same_real (base i) (hPositive i) r h
  | real i g =>
    have hg := g.isLt
    cases target with
    | anchor => dsimp [k4RetainedSlotRank] at hRank; omega
    | free j s =>
      have hs := s.isLt
      have hij : i < j := by
        change i.val < j.val
        dsimp [k4RetainedSlotRank] at hRank
        omega
      exact (k4RetainedSlot_before_free_iff base hPositive hGap (.real i g) j s).2 hij
    | real j h =>
      have hh := h.isLt
      have hij : i ≤ j := by
        change i.val ≤ j.val
        dsimp [k4RetainedSlotRank] at hRank
        omega
      rcases lt_or_eq_of_le hij with hlt | heq
      · have hFirst := (k4RetainedSlot_before_free_iff
          base hPositive hGap (.real i g) j (0 : Fin 4)).2 hlt
        exact hFirst.trans (retained_free_before_same_real
          (base j) (hPositive j) (0 : Fin 4) h)
      · subst j
        change hPosition 4 (base i) g.val < hPosition 4 (base i) h.val
        dsimp [k4RetainedSlotRank] at hRank
        unfold hPosition
        omega

/-- The physical tagged coordinates are injective. In particular the
retained free slots cannot collide with a different member's real slots. -/
theorem k4RetainedSlotPosition_injective
    {B : Nat} (base : Fin B → Nat)
    (hPositive : ∀ i, 0 < base i)
    (hGap : ∀ i j, i < j → base i + 2 ≤ base j) :
    Function.Injective (k4RetainedSlotPosition base) := by
  intro source target hEq
  apply k4RetainedSlotRank_injective B
  by_contra hn
  rcases lt_or_gt_of_ne hn with hLt | hGt
  · have h := k4RetainedSlotPosition_lt_of_rank_lt
      base hPositive hGap source target hLt
    rw [hEq] at h
    exact (lt_irrefl _) h
  · have h := k4RetainedSlotPosition_lt_of_rank_lt
      base hPositive hGap target source hGt
    rw [hEq] at h
    exact (lt_irrefl _) h

/-- Any common slot sequence in increasing rank realizes the SAME strict
source order in every dummy-separated physical occurrence. -/
theorem k4RetainedSlotPosition_strictMono_of_rank
    {B M : Nat} (base : Fin B → Nat)
    (hPositive : ∀ i, 0 < base i)
    (hGap : ∀ i j, i < j → base i + 2 ≤ base j)
    (tags : Fin M → K4RetainedSlot B)
    (hOrder : StrictMono (fun i => k4RetainedSlotRank (tags i))) :
    StrictMono (fun i => k4RetainedSlotPosition base (tags i)) := by
  intro i j hij
  exact k4RetainedSlotPosition_lt_of_rank_lt
    base hPositive hGap (tags i) (tags j) (hOrder hij)

#print axioms Kk.k4RetainedFreeCoordinate_odd
#print axioms Kk.k4RetainedSlot_before_free_iff
#print axioms Kk.finiteNumericH_four_generation_zero_freeLevel
#print axioms Kk.k4RetainedSlot_exactE_iff
#print axioms Kk.k4RetainedSlot_finiteE_iff
#print axioms Kk.k4RetainedSlot_ordinary_eq
#print axioms Kk.k4RetainedSlotCode_eq_of_base_table
#print axioms Kk.k4RetainedSlotRank_injective
#print axioms Kk.k4RetainedSlotPosition_lt_of_rank_lt
#print axioms Kk.k4RetainedSlotPosition_injective
#print axioms Kk.k4RetainedSlotPosition_strictMono_of_rank

end Kk
