import Kk.SupportBlockGapAge
import Kk.FiniteUniformNumericComplete
import Kk.HensonLeftDensityAge
import Mathlib.Tactic

/-!
# KK Track A: actual isolated reserved clique followed by one finite universal top front

English proof and 18-point adversarial audit committed FIRST:
  docs/physical_isolated_support_stage_english_audit.md

For one fixed normalized left-dense Henson original graph E,
the original old prefix [0,b), and a genuine reserved original
pool Q⊆[b,F), prescribe complete new-to-future columns:
- old p<b: the original arbitrary c(p,t) in BOTH directions;
- reserved q∈Q: exactly decide(t∈T), including outside-support zeros;
- every genuine original gap p∈[b,F)\Q: zero for ALL types.

The complete old-prefix raw age of [0,F) for these columns is
PROVED equal to that of the isolated P∪Q pool; no gap original
is silently deleted. The already kernel-checked same-f,M finite
Henson/numeric-H theorem applied once at F then supplies a common
selected future with exactly the raw-aged feasible normalized
clique vectors and the exact complete old/reserved/gap L columns.

The final theorem also USES the verified left-density reserved
clique constructor to produce a genuine Q of arbitrary r<ell
in the same E. No relative existence axiom or consecutive
original re-enumeration is introduced.

This is finite ordinary L only; no infinite resolved diary,
full auxiliary H+ Kpt E/B3 source or common labelled orbit.
-/

namespace Kk

open SuccessorTree.V10

/-- A precise finite physical positive support-T stage, in a
fixed actual Henson enumeration E. The future numeric-H top pool
is common to ALL normalized clique weight vectors, and ONE f,M
supplies its profile, old/reserve/gap columns, and numeric carrier
bounds simultaneously. Q may be a nonconsecutive reserved pool.
No claim of an infinite coherent stage schedule is embedded. -/
def HasUniformPositiveSupportStage
    (E : Nat → Nat → Bool)
    (d ell b F k : Nat)
    (c : Nat → Fin d → Bool)
    (Q : Finset Nat) (T : IntegerGraphSupport d ell) : Prop :=
  let B := finiteOldColumnRawBound E ell d
    (Finset.range b ∪ Q) (supportBlockOldColumn Q T.1 c)
  let V := RelativeUniversalTaggedVertex d ell B
  let N := F + Fintype.card V
  let W : Finset Nat := finiteTaggedFuturePool (V := V) F
  let A : Nat → Nat → Bool := finiteTaggedOldFutureEdge F E
    (relativeUniversalTaggedEdge d ell B)
    (relativeUniversalTaggedSort d ell B)
    (supportBlockGappedColumn b Q T.1 c)
  let tau : Nat → Fin d := finiteTaggedFutureSort (by
    have : 0 < d := by
      rcases T.2.1 with ⟨t,_⟩
      exact Nat.pos_of_ne_zero (by
        intro hz
        subst d
        exact (Fin.elim0 t))
    exact this)
    (relativeUniversalTaggedSort d ell B) F
  ∃ (f : Nat → Nat) (M : Nat),
    (∀ i, i < F → f i = i) ∧
    (∀ i j, i < N → j < N → i < j → f i < f j) ∧
    (∀ i j, i < N → j < N → i ≠ j →
      E (f i) (f j) = A i j) ∧
    (∀ w ∈ W, F ≤ f w) ∧
    (∀ i ∈ Finset.range F ∪ W.image f,
      hPosition k i k < M) ∧
    (∀ v : IntegerCliqueWeights d ell,
      v ∈ feasibleIntegerCliqueVectors d ell B ↔
        ∃ s : Finset Nat,
          s ⊆ numericHTopPool k (W.image f) ∧
          IsDirectedCliqueOn
            (fun x y => (finiteNumericHL
              (normalizedGraphModel E) k M).binary x y (0 : Fin 1)) s ∧
          (∀ U : IntegerGraphSupport d ell,
            (s.filter (fun z =>
              z ∈ numericHTopPool k
                ((W.filter (fun x => tau x ∈ U.1)).image f))).card =
              integerCliqueOnSupport v U)) ∧
    (∀ i, i < b → ∀ w ∈ W, ∀ q, q ≤ k →
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k i q) (hPosition k (f w) k) (0 : Fin 1) =
          c i (tau w) ∧
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k (f w) k) (hPosition k i q) (0 : Fin 1) =
          c i (tau w)) ∧
    (∀ i ∈ Q, ∀ w ∈ W, ∀ q, q ≤ k →
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k i q) (hPosition k (f w) k) (0 : Fin 1) =
          decide (tau w ∈ T.1) ∧
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k (f w) k) (hPosition k i q) (0 : Fin 1) =
          decide (tau w ∈ T.1)) ∧
    (∀ i, b ≤ i → i < F → i ∉ Q →
      ∀ w ∈ W, ∀ q, q ≤ k →
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k i q) (hPosition k (f w) k) (0 : Fin 1) =
            false ∧
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k (f w) k) (hPosition k i q) (0 : Fin 1) =
            false) ∧
    (∀ w ∈ W, ∀ z, z < f w →
      z ∉ (Finset.range w).image f →
      ∀ q, q ≤ k →
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k z q) (hPosition k (f w) k) (0 : Fin 1) =
            false ∧
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k (f w) k) (hPosition k z q) (0 : Fin 1) =
            false) ∧
    (∀ w ∈ W, ∀ a : Nat,
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (2*a+1) (hPosition k (f w) k) (0 : Fin 1) = false ∧
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k (f w) k) (2*a+1) (0 : Fin 1) = false)

/-- With an ACTUAL reserved pool Q inside [b,F), the whole numeric
universal future can be chosen after F in the unchanged E, with
all old/reserved/gap original columns EXACT and every all-support
normalized feasible clique vector present in the SAME top pool.

The raw bound used by the future is derived from P∪Q, not
postulated. The complete intervening original gap contributions
are discharged by the proved pool identity in SupportBlockGapAge.
This theorem does not require Q itself to be a clique or
P-Q isolation; those are supplied by the genuine Henson reserved
constructor when the stage is specialized below. -/
theorem henson_leftDense_uniform_finite_stage_after_support_block
    (E : Nat → Nat → Bool)
    (d ell b F k : Nat)
    (hell : 2 ≤ ell) (hd : 0 < d) (hBF : b ≤ F)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool)
    (Q : Finset Nat)
    (hQWithin : ∀ q ∈ Q, b ≤ q ∧ q < F)
    (T : IntegerGraphSupport d ell) :
    HasUniformPositiveSupportStage E d ell b F k c Q T := by
  classical
  let C : Nat → Fin d → Bool :=
    supportBlockGappedColumn b Q T.1 c
  let B : IntegerGraphSupport d ell → Nat :=
    finiteOldColumnRawBound E ell d (Finset.range b ∪ Q)
      (supportBlockOldColumn Q T.1 c)
  let V := RelativeUniversalTaggedVertex d ell B
  let N : Nat := F + Fintype.card V
  let W : Finset Nat := finiteTaggedFuturePool (V := V) F
  let sort : V → Fin d := relativeUniversalTaggedSort d ell B
  let R : V → V → Bool := relativeUniversalTaggedEdge d ell B
  let A : Nat → Nat → Bool := finiteTaggedOldFutureEdge F E R sort C
  let tau : Nat → Fin d := finiteTaggedFutureSort hd sort F
  have hRaw :
      finiteOldColumnRawBound E ell d (Finset.range F) C = B :=
    supportBlockGappedRawBound_eq E ell d b F hBF Q hQWithin T c
  have hMain :=
    henson_leftDense_realizes_all_finite_numericH_L_columns_and_profiles
      d ell F k hell hd E hAvoid hDense C
  rw [hRaw] at hMain
  obtain ⟨f,M,hFix,hMono,hGraph,hGap,hAfter,hCut,
      hOldCarrier,hGapCarrier,hTopCarrier,hProfile,
      hColumns,hGapNumeric,hDummy⟩ := hMain
  have hOldCol : ∀ i, i < b → ∀ w ∈ W, ∀ q, q ≤ k →
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k i q) (hPosition k (f w) k) (0 : Fin 1) =
          c i (tau w) ∧
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k (f w) k) (hPosition k i q) (0 : Fin 1) =
          c i (tau w) := by
    intro i hi w hw q hq
    have hNotQ : i ∉ Q := by
      intro hQ
      have hAfterQ := (hQWithin i hQ).1
      omega
    have hC : C i (tau w) = c i (tau w) := by
      simp [C,supportBlockGappedColumn, supportBlockOldColumn,
        delayedOldColumn, hNotQ, hi]
    obtain ⟨hForward,hReverse⟩ :=
      hColumns i (by omega) w hw q hq
    exact ⟨hForward.trans hC, hReverse.trans hC⟩
  have hReservedCol : ∀ i ∈ Q, ∀ w ∈ W, ∀ q, q ≤ k →
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k i q) (hPosition k (f w) k) (0 : Fin 1) =
          decide (tau w ∈ T.1) ∧
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k (f w) k) (hPosition k i q) (0 : Fin 1) =
          decide (tau w ∈ T.1) := by
    intro i hi w hw q hq
    have hC : C i (tau w) = decide (tau w ∈ T.1) := by
      simp [C,supportBlockGappedColumn,
        supportBlockOldColumn, hi]
    obtain ⟨hForward,hReverse⟩ :=
      hColumns i (hQWithin i hi).2 w hw q hq
    exact ⟨hForward.trans hC,hReverse.trans hC⟩
  have hGapCol : ∀ i, b ≤ i → i < F → i ∉ Q →
      ∀ w ∈ W, ∀ q, q ≤ k →
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k i q) (hPosition k (f w) k) (0 : Fin 1) =
            false ∧
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k (f w) k) (hPosition k i q) (0 : Fin 1) =
            false := by
    intro i hi hiF hNotQ w hw q hq
    have hNotOld : ¬ i < b := by omega
    have hC : C i (tau w) = false := by
      simp [C,supportBlockGappedColumn,
        supportBlockOldColumn,delayedOldColumn,hNotQ,hNotOld]
    obtain ⟨hForward,hReverse⟩ :=
      hColumns i hiF w hw q hq
    exact ⟨hForward.trans hC,hReverse.trans hC⟩
  change HasUniformPositiveSupportStage E d ell b F k c Q T
  unfold HasUniformPositiveSupportStage
  refine ⟨f,M,hFix,hMono,hGraph,hAfter,hCut,hProfile,
    hOldCol,hReservedCol,hGapCol,hGapNumeric,hDummy⟩

/-- A GENUINE finite positive-link stage exists in the unchanged
left-dense Henson original graph: first choose an actual isolated
reserved clique Q of size r<ell, then set a cutoff F after its
nonconsecutive indices and ALL intervening original gaps.
The preceding theorem supplies a single later finite universal
top future with exactly the complete old, reserved and gap L
columns and the actual P∪Q raw-clique-age profile.

For r=ell-1 the raw feasible family correctly excludes a
future singleton joined to all r vertices; no illegal positive
extension is fabricated. To force that singleton in a diary
one needs r<ell-1 and an explicit singleton safety certificate.

This is one FINITE stage, not a coherent infinite diary. -/
theorem henson_leftDense_exists_uniform_finite_support_stage
    (d ell b k r : Nat)
    (hell : 2 ≤ ell) (hd : 0 < d) (hr : r < ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool)
    (T : IntegerGraphSupport d ell) :
    ∃ (Q : Finset Nat) (F : Nat),
      Q.card = r ∧
      (∀ q ∈ Q, b ≤ q ∧ q < F) ∧
      IsDirectedCliqueOn E Q ∧
      (∀ p, p < b → ∀ q ∈ Q,
        E p q = false ∧ E q p = false) ∧
      HasUniformPositiveSupportStage E d ell b F k c Q T := by
  classical
  obtain ⟨Q,hCard,hAfter,hClique,hIso⟩ :=
    henson_leftDense_exists_reserved_originals
      ell hell E hAvoid hDense b r hr
  let F : Nat := max b (Q.sup (fun q : Nat => q) + 1)
  have hBF : b ≤ F := by dsimp [F]; omega
  have hQWithin : ∀ q ∈ Q, b ≤ q ∧ q < F := by
    intro q hq
    have hSup : q ≤ Q.sup (fun j : Nat => j) :=
      Finset.le_sup (f := fun j : Nat => j) hq
    refine ⟨hAfter q hq,?_⟩
    dsimp [F]
    omega
  have hOldIso :
      ∀ p, p < b → ∀ q ∈ Q,
        E p q = false ∧ E q p = false := by
    intro p hp q hq
    have hpNotQ : p ∉ Q := by
      intro hpQ
      have hAfterP := hAfter p hpQ
      omega
    have hpq : p < q := lt_of_lt_of_le hp (hAfter q hq)
    exact hIso q hq p hpq hpNotQ
  refine ⟨Q,F,hCard,hQWithin,hClique,hOldIso,?_⟩
  exact henson_leftDense_uniform_finite_stage_after_support_block
    E d ell b F k hell hd hBF hAvoid hDense c Q hQWithin T

#print axioms Kk.henson_leftDense_uniform_finite_stage_after_support_block
#print axioms Kk.henson_leftDense_exists_uniform_finite_support_stage

end Kk
