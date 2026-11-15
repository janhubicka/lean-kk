import Kk.FiniteUniformNumericTopAge
import Kk.FiniteCliqueEmbeddingTransport
import Kk.FiniteOldColumnAge
import Kk.IntegerAgeUniversalProperties
import Mathlib.Tactic

/-!
# KK Track A: complete numerical-H real-generation clique-capacity projection

English proof and adversarial audit committed FIRST:
  docs/full_real_generation_capacity_english_audit.md

The genuine numerical H binary L generator has positive real-real
edges ONLY between copies of DISTINCT originals, and in the actual
tuple direction it copies a positive original-graph E atom.
Thus projecting ANY mixed-generation numerical clique to its
original indices is INJECTIVE and yields an E clique.

Conversely, the TOP-generation copies are a fully induced copy
of the original finite graph. Hence the exact clique capacities
agree on the COMPLETE k+1 real-generation pool of ANY finite P.

Typed old columns pulled back from the original name give exactly
the same complete common-old-neighbourhood capacities at EVERY
nonempty support, hence the same raw and canonical integer ages.
No equality is asserted for an arbitrary PARTIAL reserved block
that omits top copies; its already-verified sharp pivot capacity
remains a separate theorem.

These are finite ordinary-L results, NOT a coherent infinite
resolved diary, full auxiliary Kpt E/B3 or a labelled orbit.
-/

namespace Kk

open SuccessorTree.V10

/-- COMPLETE numerical H real-copy pool: all originals i in P
at EVERY generation q=0,...,k. No odd dummy vertices. -/
def numericHCompleteRealPool (k : Nat) (P : Finset Nat) : Finset Nat :=
  (P.product (Finset.range (k+1))).image
    (fun x => hPosition k x.1 x.2)

/-- Exact membership in the complete real-generation pool. -/
theorem numericHCompleteRealPool_mem_iff
    (k : Nat) (P : Finset Nat) (z : Nat) :
    z ∈ numericHCompleteRealPool k P ↔
      ∃ i ∈ P, ∃ q : Nat, q ≤ k ∧ hPosition k i q = z := by
  classical
  constructor
  · intro hz
    obtain ⟨x,hx,hEq⟩ := Finset.mem_image.mp hz
    obtain ⟨hi,hq⟩ := Finset.mem_product.mp hx
    exact ⟨x.1,hi,x.2,by
      have hqLt := Finset.mem_range.mp hq
      omega,hEq⟩
  · rintro ⟨i,hi,q,hq,hEq⟩
    apply Finset.mem_image.mpr
    refine ⟨(i,q),?_,hEq⟩
    apply Finset.mem_product.mpr
    exact ⟨hi,Finset.mem_range.mpr (by omega)⟩

/-- A total original-name decoder for bounded real numeric
coordinates. On any non-real coordinate its default is irrelevant.
The original index is unique by the verified bounded iota
injectivity; it never renames the original Henson graph. -/
noncomputable def numericHRealOriginal (k z : Nat) : Nat := by
  classical
  exact if h : ∃ i : Nat, ∃ q : Nat, q ≤ k ∧ hPosition k i q = z then
    Classical.choose h
  else 0

/-- Every bounded real generation decodes to its EXACT original. -/
theorem numericHRealOriginal_at
    (k i q : Nat) (hq : q ≤ k) :
    numericHRealOriginal k (hPosition k i q) = i := by
  classical
  unfold numericHRealOriginal
  split_ifs with h
  · obtain ⟨q',hq',hEq⟩ := Classical.choose_spec h
    exact (hPosition_injective_bounded k
      (Classical.choose h) q' i q hq' hq hEq).1
  · exact False.elim (h ⟨i,q,hq,rfl⟩)

/-- Every POSITIVE finite numerical-H real-real L atom
projects to a positive original-graph E atom between
DISTINCT originals, in its exact directed tuple orientation.

This directly inspects both generator orientations in
HNumericCrossing and uses injectivity of bounded real
coordinates; no generation gate, symmetry or positivity
of the opposite directed tuple is assumed. -/
theorem finiteNumericH_real_positive_projects_original
    (E : Nat → Nat → Bool) (k M i j q m : Nat)
    (hq : q ≤ k) (hm : m ≤ k)
    (hEdge :
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k i q) (hPosition k j m)
        (0 : Fin 1) = true) :
    i ≠ j ∧ E i j = true := by
  change hNumericBinary (normalizedGraphModel E).binary k
    (hPosition k i q) (hPosition k j m) (0 : Fin 1) = true at hEdge
  obtain ⟨u,v,a,b,huv,ha,hb,hgate,hDir⟩ :=
    (hNumericBinary_true_iff (normalizedGraphModel E).binary
      k (hPosition k i q) (hPosition k j m)
      (0 : Fin 1)).mp hEdge
  rcases hDir with ⟨hx,hy,hBit⟩ | ⟨hx,hy,hBit⟩
  · have hi : i = u :=
      (hPosition_injective_bounded k i q u a hq ha hx).1
    have hj : j = v :=
      (hPosition_injective_bounded k j m v b hm hb hy).1
    have hBase : E u v = true := hBit
    constructor
    · intro hEq
      omega
    · simpa only [hi,hj] using hBase
  · have hi : i = v :=
      (hPosition_injective_bounded k i q v b hq hb hx).1
    have hj : j = u :=
      (hPosition_injective_bounded k j m u a hm ha hy).1
    have hBase : E v u = true := hBit
    constructor
    · intro hEq
      omega
    · simpa only [hi,hj] using hBase

/-- The original-image decoder of any real pool member
belongs to the underlying finite original P. -/
theorem numericHRealOriginal_mem_of_complete_pool
    (k : Nat) (P : Finset Nat) (z : Nat)
    (hz : z ∈ numericHCompleteRealPool k P) :
    numericHRealOriginal k z ∈ P := by
  obtain ⟨i,hi,q,hq,hEq⟩ :=
    (numericHCompleteRealPool_mem_iff k P z).mp hz
  have hDecode := numericHRealOriginal_at k i q hq
  rw [hEq] at hDecode
  rw [hDecode]
  exact hi

/-- A finite numerical-H L-clique in a complete real-copy pool
projects INJECTIVELY onto original indices. Two generations of
one original cannot coexist in one directed clique: positive
L atoms require distinct original source indices. -/
theorem finiteNumericH_real_clique_original_inj
    (E : Nat → Nat → Bool) (k M : Nat)
    (P s : Finset Nat)
    (hs : s ⊆ numericHCompleteRealPool k P)
    (hc : IsDirectedCliqueOn
      (fun x y => (finiteNumericHL (normalizedGraphModel E) k M).binary
        x y (0 : Fin 1)) s) :
    Set.InjOn (numericHRealOriginal k) ↑s := by
  intro x hx y hy hOrigEq
  by_contra hxy
  obtain ⟨i,hi,q,hq,hxEq⟩ :=
    (numericHCompleteRealPool_mem_iff k P x).mp (hs hx)
  obtain ⟨j,hj,m,hm,hyEq⟩ :=
    (numericHCompleteRealPool_mem_iff k P y).mp (hs hy)
  have hBit :
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k i q) (hPosition k j m)
        (0 : Fin 1) = true := by
    rw [hxEq,hyEq]
    exact hc x hx y hy hxy
  have hOrigNe := (finiteNumericH_real_positive_projects_original
    E k M i j q m hq hm hBit).1
  have hX := numericHRealOriginal_at k i q hq
  have hY := numericHRealOriginal_at k j m hm
  rw [hxEq] at hX
  rw [hyEq] at hY
  have hij : i = j := by
    calc
      i = numericHRealOriginal k x := hX.symm
      _ = numericHRealOriginal k y := hOrigEq
      _ = j := hY
  exact hOrigNe hij

/-- The original images of any bounded numerical-H real clique
form a directed original E-clique. Every ordered positive numeric
L bit projects to the matching ordered original atom. -/
theorem finiteNumericH_real_clique_original_image
    (E : Nat → Nat → Bool) (k M : Nat)
    (P s : Finset Nat)
    (hs : s ⊆ numericHCompleteRealPool k P)
    (hc : IsDirectedCliqueOn
      (fun x y => (finiteNumericHL (normalizedGraphModel E) k M).binary
        x y (0 : Fin 1)) s) :
    IsDirectedCliqueOn E (s.image (numericHRealOriginal k)) := by
  intro i hi j hj hij
  obtain ⟨x,hx,hxi⟩ := Finset.mem_image.mp hi
  obtain ⟨y,hy,hyj⟩ := Finset.mem_image.mp hj
  have hxy : x ≠ y := by
    intro heq
    subst y
    exact hij (hxi.symm.trans hyj)
  obtain ⟨i',hi',q,hq,hxEq⟩ :=
    (numericHCompleteRealPool_mem_iff k P x).mp (hs hx)
  obtain ⟨j',hj',m,hm,hyEq⟩ :=
    (numericHCompleteRealPool_mem_iff k P y).mp (hs hy)
  have hBit :
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k i' q) (hPosition k j' m) (0 : Fin 1) = true := by
    rw [hxEq,hyEq]
    exact hc x hx y hy hxy
  have hProjected := (finiteNumericH_real_positive_projects_original
    E k M i' j' q m hq hm hBit).2
  have hX := numericHRealOriginal_at k i' q hq
  have hY := numericHRealOriginal_at k j' m hm
  rw [hxEq] at hX
  rw [hyEq] at hY
  have hProjectedOriginal :
      E (numericHRealOriginal k x)
        (numericHRealOriginal k y) = true := by
    simpa only [hX,hY] using hProjected
  simpa only [hxi,hyj] using hProjectedOriginal

/-- The EXACT capacity of the COMPLETE real-generation pool
is the original E clique capacity. Unlike a partial reserved
prefix, the pool contains all TOP-generation copies and
therefore realizes every original clique at top.

Upper bound: every mixed-generation numerical clique projects
injectively to an E-clique. Lower bound: the verified full
top-generation induced embedding and capacity monotonicity. -/
theorem finiteNumericH_complete_real_capacity_eq_original
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k M : Nat) (P : Finset Nat) :
    finiteDirectedCliqueCapacity
      (fun x y => (finiteNumericHL (normalizedGraphModel E) k M).binary
        x y (0 : Fin 1))
      (numericHCompleteRealPool k P) =
    finiteDirectedCliqueCapacity E P := by
  classical
  let L : Nat → Nat → Bool :=
    fun x y => (finiteNumericHL (normalizedGraphModel E) k M).binary
      x y (0 : Fin 1)
  apply Nat.le_antisymm
  · obtain ⟨s,hs,hClique,hCard⟩ :=
      finiteDirectedCliqueCapacity_attained
        L (numericHCompleteRealPool k P)
    have hInj := finiteNumericH_real_clique_original_inj
      E k M P s hs hClique
    have hImageSub : s.image (numericHRealOriginal k) ⊆ P := by
      intro z hz
      obtain ⟨x,hx,hxz⟩ := Finset.mem_image.mp hz
      rw [←hxz]
      exact numericHRealOriginal_mem_of_complete_pool
        k P x (hs hx)
    have hImageClique := finiteNumericH_real_clique_original_image
      E k M P s hs hClique
    have hBound := directedClique_card_le_capacity E P
      (s.image (numericHRealOriginal k)) hImageSub hImageClique
    have hCardImage := Finset.card_image_iff.mpr hInj
    rw [hCardImage] at hBound
    change finiteDirectedCliqueCapacity L
      (numericHCompleteRealPool k P) ≤
      finiteDirectedCliqueCapacity E P
    omega
  · have hTopSub :
        numericHTopPool k P ⊆ numericHCompleteRealPool k P := by
      intro z hz
      obtain ⟨i,hi,hEq⟩ := Finset.mem_image.mp hz
      apply (numericHCompleteRealPool_mem_iff k P z).mpr
      exact ⟨i,hi,k,le_rfl,hEq⟩
    let top : Nat → Nat := fun i => hPosition k i k
    have hTopInj : Set.InjOn top ↑P := by
      intro i _ j _ hEq
      exact numericHTopPos_injective k hEq
    have hTopAtoms : ∀ i ∈ P, ∀ j ∈ P, i ≠ j →
        E i j = L (top i) (top j) := by
      intro i _ j _ hNe
      exact (finiteNumericH_top_exact_original_edge
        E hSym k M i j hNe).symm
    have hTopCap : finiteDirectedCliqueCapacity L
        (numericHTopPool k P) = finiteDirectedCliqueCapacity E P := by
      have h := finiteDirectedCliqueCapacity_induced_image_eq
        E L P top hTopInj hTopAtoms
      simpa only [L,top,numericHTopPool] using h
    have hMono := finiteDirectedCliqueCapacity_mono L
      (numericHTopPool k P) (numericHCompleteRealPool k P) hTopSub
    rw [hTopCap] at hMono
    exact hMono

/-- Complete typed old-column bit at a real generation:
pull the original's column back via its unique real-coordinate
decoder. The value on odd/non-real coordinates is irrelevant
when the old pool is the COMPLETE REAL pool. -/
noncomputable def numericHRealColumn
    {d : Nat} (k : Nat) (c : Nat → Fin d → Bool) :
    Nat → Fin d → Bool :=
  fun z t => c (numericHRealOriginal k z) t

/-- Exact old common-neighbourhood set identity at EVERY support:
select originals common to all sorts, then copy ALL generations.
There are no phantom common neighbours from repeated generations
of one original. This is equality of literal Nat-coordinate pools. -/
theorem finiteNumericH_complete_real_common_pool_eq
    {d ell : Nat}
    (k : Nat) (P : Finset Nat) (c : Nat → Fin d → Bool)
    (U : IntegerGraphSupport d ell) :
    oldSupportCommonNeighbourPool (numericHCompleteRealPool k P)
      (numericHRealColumn k c) U.1 =
    numericHCompleteRealPool k
      (oldSupportCommonNeighbourPool P c U.1) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨hzPool,hAll⟩ := Finset.mem_filter.mp hz
    obtain ⟨i,hi,q,hq,hEq⟩ :=
      (numericHCompleteRealPool_mem_iff k P z).mp hzPool
    apply (numericHCompleteRealPool_mem_iff k
      (oldSupportCommonNeighbourPool P c U.1) z).mpr
    refine ⟨i,Finset.mem_filter.mpr ⟨hi,?_⟩,q,hq,hEq⟩
    intro t ht
    have hBit := hAll t ht
    have hDecode : numericHRealOriginal k z = i := by
      rw [←hEq]
      exact numericHRealOriginal_at k i q hq
    simpa [numericHRealColumn,hDecode] using hBit
  · intro hz
    obtain ⟨i,hi,q,hq,hEq⟩ :=
      (numericHCompleteRealPool_mem_iff k
        (oldSupportCommonNeighbourPool P c U.1) z).mp hz
    obtain ⟨hiP,hAll⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨(numericHCompleteRealPool_mem_iff k P z).mpr
      ⟨i,hiP,q,hq,hEq⟩,?_⟩
    intro t ht
    have hDecode : numericHRealOriginal k z = i := by
      rw [←hEq]
      exact numericHRealOriginal_at k i q hq
    simpa [numericHRealColumn,hDecode] using hAll t ht

/-- THE COMPLETE full-real-generation numerical-H raw old age
is pointwise equal to the actual original old age, on ALL
nonempty admissible supports. No phantom numeric capacity is
created by copying an old original at multiple generations.
This does NOT apply to partial reserved prefixes. -/
theorem finiteNumericH_complete_real_raw_age_eq
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (ell d k M : Nat) (P : Finset Nat)
    (c : Nat → Fin d → Bool) :
    finiteOldColumnRawBound
      (fun x y => (finiteNumericHL (normalizedGraphModel E) k M).binary
        x y (0 : Fin 1))
      ell d (numericHCompleteRealPool k P)
      (numericHRealColumn k c) =
    finiteOldColumnRawBound E ell d P c := by
  funext U
  unfold finiteOldColumnRawBound
  rw [finiteNumericH_complete_real_common_pool_eq k P c U]
  exact congrArg (fun n : Nat => ell - 1 - n)
    (finiteNumericH_complete_real_capacity_eq_original
      E hSym k M (oldSupportCommonNeighbourPool P c U.1))

/-- Consequently the full real-copy numerical-H and original
canonical integer graph ages are IDENTICAL on all supports. -/
theorem finiteNumericH_complete_real_canonical_age_eq
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (ell d k M : Nat) (P : Finset Nat)
    (c : Nat → Fin d → Bool) :
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound
        (fun x y => (finiteNumericHL
          (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
        ell d (numericHCompleteRealPool k P)
        (numericHRealColumn k c)) =
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d P c) := by
  rw [finiteNumericH_complete_real_raw_age_eq
    E hSym ell d k M P c]

/-- One explicit finite numeric-H cutoff includes every generation
of every original in P. This is a genuine finite-carrier
statement, not merely an equality of total Boolean tables. -/
theorem finiteNumericH_complete_real_carrier
    (E : Nat → Nat → Bool) (k : Nat) (P : Finset Nat) :
    let M : Nat := (numericHCompleteRealPool k P).sup id + 1
    ∀ z ∈ numericHCompleteRealPool k P,
      z ∈ (finiteNumericHL (normalizedGraphModel E) k M).carrier := by
  classical
  change ∀ z ∈ numericHCompleteRealPool k P,
    z ∈ (finiteNumericHL (normalizedGraphModel E) k
      ((numericHCompleteRealPool k P).sup id + 1)).carrier
  intro z hz
  change z < (numericHCompleteRealPool k P).sup id + 1
  have hBound : z ≤ (numericHCompleteRealPool k P).sup id :=
    Finset.le_sup (f := id) hz
  omega

#print axioms Kk.numericHCompleteRealPool_mem_iff
#print axioms Kk.numericHRealOriginal_at
#print axioms Kk.finiteNumericH_real_positive_projects_original
#print axioms Kk.numericHRealOriginal_mem_of_complete_pool
#print axioms Kk.finiteNumericH_real_clique_original_inj
#print axioms Kk.finiteNumericH_real_clique_original_image
#print axioms Kk.finiteNumericH_complete_real_capacity_eq_original
#print axioms Kk.finiteNumericH_complete_real_common_pool_eq
#print axioms Kk.finiteNumericH_complete_real_raw_age_eq
#print axioms Kk.finiteNumericH_complete_real_canonical_age_eq
#print axioms Kk.finiteNumericH_complete_real_carrier

end Kk
