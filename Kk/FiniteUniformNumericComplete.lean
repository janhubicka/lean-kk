import Kk.FiniteUniformNumericTopAge
import Kk.FiniteUniformNumericColumns
import Mathlib.Tactic

/-!
# KK Track A: ONE f and M give the full finite numerical-H L profile AND columns

English proof and hostile audit committed FIRST:
  docs/finite_uniform_numeric_complete_english_audit.md

The common trap is existential: independent theorems providing
`exists f, profile f` and `exists f, columns f` do not themselves
give one f satisfying both.

We therefore select ONE f,M from the previously kernel-checked
FiniteUniformNumericTopAge theorem and then apply the GENERAL
old/gap generation-column theorems of FiniteUniformNumericColumns
to precisely those same chosen witnesses, without another
physical Henson extension call. This gives a single finite literal
numerical-H ordinary graph-L realization of every old column,
every omitted-original gap zero and every feasible labelled
clique profile, with carrier bounds for ALL tested real addresses.

The result is FINITE and graph L only. It does not prove an
infinite canonical resolved diary, full auxiliary Kpt E/parameter
closure/B3, common inverse-labelled source orbit or final BRDs.
-/

namespace Kk

open SuccessorTree.V10

/-- Strong uniform finite numerical-H ordinary-L realization.

For any fixed left-dense normalized Henson E, entire old prefix
[0,b), arbitrary complete typed columns c, ell>=2,d>0 and
numeric H height k, there are ONE physical old-fixing induced
embedding f and ONE genuine finite numerical carrier M such that:

* EVERY feasible normalized labelled clique weight vector has an
  actual clique inside one common selected top pool f(W) at
  numerical top generation k, with exact all-support counts,
  and no spurious normalized vector;
* EVERY old original at EVERY generation q<=k has exactly its
  prescribed c column to EVERY future top copy (both L arcs);
* EVERY omitted intermediate original at every generation q<=k
  has zero column to the later selected top copy (both L arcs);
* EVERY odd dummy binary-L column toward the top pool is zero;
* ALL old real generation addresses, omitted real gap generation
  addresses, and selected future top addresses are in [0,M).

The witness f,M used for ALL clauses is the SAME ONE, not two
unrelated existential choices. These conclusions concern only
ordinary L, not the auxiliary parameter-closed H+ source.
-/
theorem henson_leftDense_realizes_all_finite_numericH_L_columns_and_profiles
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
      (∀ w ∈ W, b ≤ f w) ∧
      (∀ i ∈ Finset.range b ∪ W.image f,
        hPosition k i k < M) ∧
      (∀ i, i < b → ∀ q, q ≤ k →
        hPosition k i q < M) ∧
      (∀ w ∈ W, ∀ z, z < f w → ∀ q, q ≤ k →
        hPosition k z q < M) ∧
      (∀ u ∈ numericHTopPool k (W.image f),
        u ∈ (finiteNumericHL (normalizedGraphModel E) k M).carrier) ∧
      (∀ v : IntegerCliqueWeights d ell,
        v ∈ feasibleIntegerCliqueVectors d ell B ↔
          ∃ t : Finset Nat,
            t ⊆ numericHTopPool k (W.image f) ∧
            IsDirectedCliqueOn
              (fun x y =>
                (finiteNumericHL (normalizedGraphModel E) k M).binary
                  x y (0 : Fin 1)) t ∧
            (∀ T : IntegerGraphSupport d ell,
              (t.filter (fun z =>
                z ∈ numericHTopPool k
                  ((W.filter (fun x => tau x ∈ T.1)).image f))).card =
                  integerCliqueOnSupport v T)) ∧
      (∀ i, i < b → ∀ w ∈ W, ∀ q, q ≤ k →
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k i q) (hPosition k (f w) k)
            (0 : Fin 1) = c i (tau w) ∧
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k (f w) k) (hPosition k i q)
            (0 : Fin 1) = c i (tau w)) ∧
      (∀ w ∈ W, ∀ z, z < f w →
        z ∉ (Finset.range w).image f →
        ∀ q, q ≤ k →
          (finiteNumericHL (normalizedGraphModel E) k M).binary
            (hPosition k z q) (hPosition k (f w) k)
              (0 : Fin 1) = false ∧
          (finiteNumericHL (normalizedGraphModel E) k M).binary
            (hPosition k (f w) k) (hPosition k z q)
              (0 : Fin 1) = false) ∧
      (∀ w ∈ W, ∀ a : Nat,
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (2*a+1) (hPosition k (f w) k)
            (0 : Fin 1) = false ∧
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k (f w) k) (2*a+1)
            (0 : Fin 1) = false) := by
  classical
  let B : IntegerGraphSupport d ell → Nat :=
    finiteOldColumnRawBound E ell d (Finset.range b) c
  let V := RelativeUniversalTaggedVertex d ell B
  let N : Nat := b + Fintype.card V
  let W : Finset Nat := finiteTaggedFuturePool (V := V) b
  let R : V → V → Bool := relativeUniversalTaggedEdge d ell B
  let sort : V → Fin d := relativeUniversalTaggedSort d ell B
  let A : Nat → Nat → Bool := finiteTaggedOldFutureEdge b E R sort c
  let tau : Nat → Fin d := finiteTaggedFutureSort hd sort b
  obtain ⟨f,M,hFix,hMono,hGraph,hGap,hAfter,hCut,hTopCarrier,hProfile⟩ :=
    henson_leftDense_realizes_all_finite_numericTop_profiles
      d ell b k hell hd E hAvoid hDense c
  have hSym : ∀ i j, E i j = E j i :=
    hensonForbiddenFamily_symmetric ell hell E hAvoid
  have hFuture : ∀ w ∈ W, b ≤ w ∧ w < N := by
    intro w hw
    exact (finiteTaggedFuturePool_mem_iff (V := V) b w).mp hw
  have hBN : b ≤ N := by
    dsimp [N]
    omega
  have hAColumn : ∀ i, i < b → ∀ w ∈ W,
      A i w = c i (tau w) := by
    intro i hi w hw
    obtain ⟨v,hv,hvw⟩ := Finset.mem_image.mp hw
    subst w
    change finiteTaggedOldFutureEdge b E R sort c i
        (finiteTaggedIndex b v) =
      c i (finiteTaggedFutureSort hd sort b
        (finiteTaggedIndex b v))
    rw [finiteTaggedFutureSort_index]
    exact finiteTaggedEdge_old_future b E R sort c i v hi
  have hOldNumeric :=
    finiteNumericH_pinned_old_generation_column_both
      E A hSym k M b N d hBN f W tau c
      hFix hGraph hFuture hAfter hAColumn
  have hGapNumeric :=
    finiteNumericH_pinned_gap_generation_zero_both
      E hSym k M b N f W hFuture hGap
  have hOdd : ∀ w ∈ W, ∀ a : Nat,
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (2*a+1) (hPosition k (f w) k) (0 : Fin 1) = false ∧
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k (f w) k) (2*a+1) (0 : Fin 1) = false := by
    intro w hw a
    exact finiteNumericH_odd_dummy_to_top_zero E k M a (f w)
  have hOldCarrier : ∀ i, i < b → ∀ q, q ≤ k →
      hPosition k i q < M := by
    intro i hi q hq
    have hTop := hCut i
      (Finset.mem_union.mpr
        (Or.inl (Finset.mem_range.mpr hi)))
    unfold hPosition at *
    omega
  have hGapCarrier : ∀ w ∈ W, ∀ z, z < f w →
      ∀ q, q ≤ k → hPosition k z q < M := by
    intro w hw z hz q hq
    have hTop : hPosition k (f w) k < M :=
      hCut (f w)
        (Finset.mem_union.mpr
          (Or.inr (Finset.mem_image.mpr ⟨w,hw,rfl⟩)))
    have hBefore : hPosition k z q < hPosition k (f w) k :=
      hPosition_lt_of_block_lt k z (f w) q k hq hz
    omega
  exact ⟨f,M,hFix,hMono,hGraph,hGap,hAfter,hCut,
    hOldCarrier,hGapCarrier,hTopCarrier,hProfile,
    hOldNumeric,hGapNumeric,hOdd⟩

#print axioms Kk.henson_leftDense_realizes_all_finite_numericH_L_columns_and_profiles

end Kk
