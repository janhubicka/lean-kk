import Kk.FiniteUniformHensonRealization
import Kk.NumericHTopSupportPool
import Kk.NumericHFullSelectedColumn
import Kk.FiniteCliqueEmbeddingTransport
import Mathlib.Tactic

/-!
# KK Track A: one finite numerical-H top pool realizes EVERY feasible relative profile

English proof and hostile audit were committed FIRST:
  docs/finite_uniform_numeric_top_english_audit.md

The genuine finite numerical-H ordinary binary L relation at top
generation k agrees with the original symmetric Henson E on
EVERY pair of distinct originals, both directions and including
all nonedges. This transports arbitrary finite directed clique
profiles and all supported counts through a single injective
top-position map, without any re-enumeration of original names.

We then apply the independently verified Track A theorem that ONE
finite Henson-original future f(W) over the entire identity old
prefix [0,b) realizes ALL B_P-feasible normalized clique vectors,
where B_P is computed from the actual old common-neighbour capacities.
One finite numeric H model, with a cutoff M large enough for old and
future top positions simultaneously, realizes EXACTLY the same
profiles in its selected top pool.

This is ordinary L only. The proof neither constructs an unbounded
resolved-copy diary nor proves Kpt auxiliary E, full parameter-closed
I1/I2/I3/B3 source data, inverse-labelled source orbits, or BRDs.
-/

namespace Kk

open SuccessorTree.V10

/-- Literal numerical H TOP-to-TOP binary L agrees with the
original graph on every ordered pair of DISTINCT original names.
The exceptional same-top-generation gate is open; both positive
and negative bits are transported, and original symmetry gives
the opposite orientation. No consecutiveness of original names. -/
theorem finiteNumericH_top_exact_original_edge
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k M i j : Nat) (hne : i ≠ j) :
    (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k i k) (hPosition k j k) (0 : Fin 1) = E i j := by
  rcases lt_trichotomy i j with hij | hij | hji
  · change hNumericBinary (normalizedGraphModel E).binary k
      (hPosition k i k) (hPosition k j k) (0 : Fin 1) = E i j
    exact numericH_older_generation_to_top_exact
      (normalizedGraphModel E).binary k i j k
      (0 : Fin 1) hij le_rfl
  · exact (hne hij).elim
  · have hSwap := henson_finiteNumericH_binary_symmetric
      E hSym k M (hPosition k i k) (hPosition k j k)
    have hForward :
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k j k) (hPosition k i k) (0 : Fin 1) = E j i := by
      change hNumericBinary (normalizedGraphModel E).binary k
        (hPosition k j k) (hPosition k i k) (0 : Fin 1) = E j i
      exact numericH_older_generation_to_top_exact
        (normalizedGraphModel E).binary k j i k
        (0 : Fin 1) hji le_rfl
    exact hSwap.trans (hForward.trans (hSym j i))

/-- Every original finite directed clique is exactly its induced
numerical-H TOP generation image, and conversely. The map is
globally injective and all ordered off-diagonal atoms agree. -/
theorem finiteNumericH_top_clique_iff_original
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k M : Nat) (s : Finset Nat) :
    IsDirectedCliqueOn E s ↔
      IsDirectedCliqueOn
        (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
          u v (0 : Fin 1))
        (numericHTopPool k s) := by
  classical
  let top : Nat → Nat := fun i => hPosition k i k
  let L : Nat → Nat → Bool :=
    fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
      u v (0 : Fin 1)
  have hInj : Set.InjOn top ↑s := by
    intro i _ j _ hEq
    exact numericHTopPos_injective k hEq
  have hAtoms : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      E i j = L (top i) (top j) := by
    intro i _ j _ hij
    exact (finiteNumericH_top_exact_original_edge
      E hSym k M i j hij).symm
  have h := finiteClique_iff_injective_image
    E L s s top (Finset.Subset.refl s) hInj hAtoms
  simpa only [L,top,numericHTopPool] using h

/-- The top-generation map preserves the supported cardinality of
EVERY finite set s and supported original pool C, with no assumption
that C is a clique or that C is a subset of s. -/
theorem finiteNumericH_top_supported_count_eq
    (k : Nat) (s C : Finset Nat) :
    ((numericHTopPool k s).filter
      (fun z => z ∈ numericHTopPool k C)).card =
      (s.filter (fun i => i ∈ C)).card := by
  classical
  have hFilter :
      (numericHTopPool k s).filter
        (fun z => z ∈ numericHTopPool k C) =
      numericHTopPool k (s.filter (fun i => i ∈ C)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzImage,hzSupport⟩ := Finset.mem_filter.mp hz
      obtain ⟨i,hi,hiz⟩ := Finset.mem_image.mp hzImage
      have hiSupport : i ∈ C := by
        apply (numericHTopPool_mem_iff k C i).mp
        simpa only [hiz] using hzSupport
      exact Finset.mem_image.mpr
        ⟨i,Finset.mem_filter.mpr ⟨hi,hiSupport⟩,hiz⟩
    · intro hz
      obtain ⟨i,hi,hiz⟩ := Finset.mem_image.mp hz
      obtain ⟨his,hiC⟩ := Finset.mem_filter.mp hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨i,his,hiz⟩,?_⟩
      have hiTopC := (numericHTopPool_mem_iff k C i).mpr hiC
      simpa only [hiz] using hiTopC
  rw [hFilter]
  unfold numericHTopPool
  exact Finset.card_image_of_injective _
    (numericHTopPos_injective k)

/-- Exact feasible-clique-vector iff transfers to ONE actual finite
numerical-H top pool for arbitrary finite support pools C(T).
Every original clique witness is mapped using the same injection,
and every numerical top clique pulls back to an original clique.
This is a complete ALL-support statement, not a chosen maximizer. -/
theorem finiteNumericH_top_profile_iff_original
    {d ell : Nat}
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k M : Nat) (S : Finset Nat)
    (C : IntegerGraphSupport d ell → Finset Nat)
    (B : IntegerGraphSupport d ell → Nat)
    (hProfile : ∀ v : IntegerCliqueWeights d ell,
      v ∈ feasibleIntegerCliqueVectors d ell B ↔
        ∃ s : Finset Nat, s ⊆ S ∧ IsDirectedCliqueOn E s ∧
          (∀ T : IntegerGraphSupport d ell,
            (s.filter (fun i => i ∈ C T)).card =
              integerCliqueOnSupport v T)) :
    ∀ v : IntegerCliqueWeights d ell,
      v ∈ feasibleIntegerCliqueVectors d ell B ↔
        ∃ t : Finset Nat,
          t ⊆ numericHTopPool k S ∧
          IsDirectedCliqueOn
            (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
              u v (0 : Fin 1)) t ∧
          (∀ T : IntegerGraphSupport d ell,
            (t.filter (fun z => z ∈ numericHTopPool k (C T))).card =
              integerCliqueOnSupport v T) := by
  classical
  intro v
  constructor
  · intro hv
    obtain ⟨s,hsS,hsClique,hsCounts⟩ := (hProfile v).mp hv
    refine ⟨numericHTopPool k s,
      numericHTopPool_mono k s S hsS,?_,?_⟩
    · exact (finiteNumericH_top_clique_iff_original
        E hSym k M s).mp hsClique
    · intro T
      exact (finiteNumericH_top_supported_count_eq k s (C T)).trans
        (hsCounts T)
  · rintro ⟨t,htTop,htClique,htCounts⟩
    let s : Finset Nat := S.filter (fun i => hPosition k i k ∈ t)
    have hsS : s ⊆ S := Finset.filter_subset _ _
    have hsImage : numericHTopPool k s = t := by
      exact finiteImage_pullback_image_eq S t
        (fun i => hPosition k i k) htTop
    have hsClique : IsDirectedCliqueOn E s := by
      apply (finiteNumericH_top_clique_iff_original E hSym k M s).mpr
      rw [hsImage]
      exact htClique
    apply (hProfile v).mpr
    refine ⟨s,hsS,hsClique,?_⟩
    intro T
    have hCount := finiteNumericH_top_supported_count_eq k s (C T)
    rw [hsImage] at hCount
    exact hCount.symm.trans (htCounts T)

/-- A single explicit numerical-H finite carrier bound includes the
top-generation coordinates of EVERY original in S, even for S=empty.
The numerical-H binary table is total on Nat, so this genuine
carrier-inclusion statement is needed for physical interpretations. -/
theorem finiteNumericH_top_carrier_of_sup_cut
    (E : Nat → Nat → Bool)
    (k : Nat) (S : Finset Nat) :
    let M : Nat := S.sup (fun i => hPosition k i k) + 1
    ∀ z ∈ numericHTopPool k S,
      z ∈ (finiteNumericHL (normalizedGraphModel E) k M).carrier := by
  classical
  intro z hz
  obtain ⟨i,hi,hiz⟩ := Finset.mem_image.mp hz
  have hBound : hPosition k i k ≤ S.sup (fun i => hPosition k i k) :=
    Finset.le_sup (f := fun i => hPosition k i k) hi
  change z < S.sup (fun i => hPosition k i k) + 1
  rw [← hiz]
  omega

/-- UNCONDITIONAL finite ordinary-L Henson-to-numerical-H top profile,
apart from the genuine ambient Henson avoidance and OnePointLeftDense
hypotheses. One SAME actual original f, one finite numerical cutoff M,
and one common finite numerical-H top pool realize ALL normalized
labelled-clique vectors allowed by the actual old-prefix raw bounds.

The finite carrier includes the top copies of EVERY old original and
EVERY selected future original. The original target's old prefix is
fixed pointwise, its induced edges and all skipped-original zeros
remain available, and the new numeric top graph agrees on ALL
off-diagonal directed L atoms.

This does NOT prove the infinite resolved-diary, the auxiliary
parameter-closed H+ E/B3 relation, or a common inverse-labelled
source orbit. -/
theorem henson_leftDense_realizes_all_finite_numericTop_profiles
    (d ell b k : Nat) (hell : 2 ≤ ell) (hd : 0 < d)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool) :
    let B := finiteOldColumnRawBound E ell d (Finset.range b) c
    let V := RelativeUniversalTaggedVertex d ell B
    let N := b + Fintype.card V
    let W : Finset Nat := finiteTaggedFuturePool (V := V) b
    let A : Nat → Nat → Bool := finiteTaggedOldFutureEdge b E
      (relativeUniversalTaggedEdge d ell B)
      (relativeUniversalTaggedSort d ell B) c
    let tau : Nat → Fin d := finiteTaggedFutureSort hd
      (relativeUniversalTaggedSort d ell B) b
    ∃ (f : Nat → Nat) (M : Nat),
      (∀ i, i < b → f i = i) ∧
      (∀ i j, i < N → j < N → i < j → f i < f j) ∧
      (∀ i j, i < N → j < N → i ≠ j →
        E (f i) (f j) = A i j) ∧
      (∀ m, b ≤ m → m < N → ∀ z, z < f m →
        z ∉ (Finset.range m).image f →
          E z (f m) = false ∧ E (f m) z = false) ∧
      (∀ x ∈ W, b ≤ f x) ∧
      (∀ i ∈ Finset.range b ∪ W.image f, hPosition k i k < M) ∧
      (∀ z ∈ numericHTopPool k (W.image f),
        z ∈ (finiteNumericHL (normalizedGraphModel E) k M).carrier) ∧
      (∀ v : IntegerCliqueWeights d ell,
        v ∈ feasibleIntegerCliqueVectors d ell B ↔
          ∃ t : Finset Nat,
            t ⊆ numericHTopPool k (W.image f) ∧
            IsDirectedCliqueOn
              (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
                u v (0 : Fin 1)) t ∧
            (∀ T : IntegerGraphSupport d ell,
              (t.filter (fun z =>
                z ∈ numericHTopPool k
                  ((W.filter (fun x => tau x ∈ T.1)).image f))).card =
                  integerCliqueOnSupport v T)) := by
  classical
  let B : IntegerGraphSupport d ell → Nat :=
    finiteOldColumnRawBound E ell d (Finset.range b) c
  let V := RelativeUniversalTaggedVertex d ell B
  let N : Nat := b + Fintype.card V
  let W : Finset Nat := finiteTaggedFuturePool (V := V) b
  let A : Nat → Nat → Bool := finiteTaggedOldFutureEdge b E
    (relativeUniversalTaggedEdge d ell B)
    (relativeUniversalTaggedSort d ell B) c
  let tau : Nat → Fin d := finiteTaggedFutureSort hd
    (relativeUniversalTaggedSort d ell B) b
  obtain ⟨f,hFix,hMono,hGraph,hGaps,hAfter,hProfile⟩ :=
    henson_leftDense_realizes_all_finite_relative_age_profiles
      d ell b hell hd E hAvoid hDense c
  let S : Finset Nat := W.image f
  let M : Nat :=
    (Finset.range b ∪ S).sup (fun i => hPosition k i k) + 1
  have hSym : ∀ i j, E i j = E j i :=
    hensonForbiddenFamily_symmetric ell hell E hAvoid
  have hBound : ∀ i ∈ Finset.range b ∪ S, hPosition k i k < M := by
    intro i hi
    have hLe : hPosition k i k ≤
        (Finset.range b ∪ S).sup (fun j => hPosition k j k) :=
      Finset.le_sup (f := fun j => hPosition k j k) hi
    exact Nat.lt_succ_of_le hLe
  have hTopCarrier : ∀ z ∈ numericHTopPool k S,
      z ∈ (finiteNumericHL (normalizedGraphModel E) k M).carrier := by
    intro z hz
    obtain ⟨i,hi,hiz⟩ := Finset.mem_image.mp hz
    change z < M
    rw [← hiz]
    exact hBound i (Finset.mem_union.mpr (Or.inr hi))
  have hOriginalProfile :
      ∀ v : IntegerCliqueWeights d ell,
        v ∈ feasibleIntegerCliqueVectors d ell B ↔
          ∃ s : Finset Nat,
            s ⊆ S ∧ IsDirectedCliqueOn E s ∧
            (∀ T : IntegerGraphSupport d ell,
              (s.filter (fun i =>
                i ∈ (W.filter (fun x => tau x ∈ T.1)).image f)).card =
                  integerCliqueOnSupport v T) := by
    intro v
    simpa only [pulledBackFiniteSortIn] using (hProfile v)
  have hTopProfile :
      ∀ v : IntegerCliqueWeights d ell,
        v ∈ feasibleIntegerCliqueVectors d ell B ↔
          ∃ t : Finset Nat,
            t ⊆ numericHTopPool k S ∧
            IsDirectedCliqueOn
              (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
                u v (0 : Fin 1)) t ∧
            (∀ T : IntegerGraphSupport d ell,
              (t.filter (fun z => z ∈ numericHTopPool k
                ((W.filter (fun x => tau x ∈ T.1)).image f))).card =
                  integerCliqueOnSupport v T) :=
    finiteNumericH_top_profile_iff_original E hSym k M S
      (fun T => (W.filter (fun x => tau x ∈ T.1)).image f)
      B hOriginalProfile
  exact ⟨f,M,hFix,hMono,hGraph,hGaps,hAfter,hBound,
    hTopCarrier,hTopProfile⟩

#print axioms Kk.finiteNumericH_top_exact_original_edge
#print axioms Kk.finiteNumericH_top_clique_iff_original
#print axioms Kk.finiteNumericH_top_supported_count_eq
#print axioms Kk.finiteNumericH_top_profile_iff_original
#print axioms Kk.finiteNumericH_top_carrier_of_sup_cut
#print axioms Kk.henson_leftDense_realizes_all_finite_numericTop_profiles

end Kk
