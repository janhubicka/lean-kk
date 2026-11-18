import Kk.TrackFPrivateSortedGraphFeasibility
import Kk.TrackFPrivateRankZeroRawTransfer
import Kk.TrackFRankZeroFiniteGraphRealization
import Mathlib.Tactic

/-!
# Track F: arbitrary-rank finite SOURCE graph richness from private rank-zero coding fibres

English proof and adversarial audit committed BEFORE Lean:
docs/track_f_allrank_actual_source_richness_english_audit.md

The previous finite sorted graph realization #355 is used ONLY at rank zero.
For every requested B vertex, the verified private descendant theorem #358
first constructs a separate rank-zero large source type, even when the
same positive-rank old source sort occurs many times. Its fresh markers are
disjoint. The separately verified private raw-age transfer #364 supplies all mixed
and singleton constraints, and the private-clique transfer #362 gives
finite B-feasibility without repeating marker bookkeeping.

The output is a genuine induced chronological SOURCE graph realization
using ACTUAL original coding nodes, with original old-source columns.
This is NOT target mixed-profile synchronization or diary unavoidability.
-/

namespace Kk

/-- MAIN TRACK F FINITE SOURCE RICHNESS (all original singleton ranks).

Given an arbitrary finite family of genuine chronological Henson source
one-types sharing one old prefix m, with ACTUAL coding-node fibres
rank-large at the respective genuine source ranks, every finite
source-RAW-feasible labelled graph B has a genuinely chronological
induced realization in those original source fibres.

Unlike the rank-zero theorem, the original roots may have different
ranks and an arbitrary label may occur repeatedly. We use one private
rank-zero descendant per requested vertex, with disjoint new markers,
and then the physical rank-zero graph realization theorem.

This is conditional only on rank-large actual source fibres, not on
an already assumed diary characterization or target universality.
-/
theorem trackFAllRanks_realizes_all_feasible_sorted_source_graph
    (d ell m N : Nat)
    (E B : Nat → Nat → Bool)
    (u : Fin d → HensonOneType ell E)
    (σ : Nat → Fin d)
    (S : Fin d → Set (HensonOneType ell E))
    (hRootLevel : ∀ i : Fin d, (u i).level = m)
    (hLarge : ∀ i : Fin d,
      RankLargeness.Large HensonOneType.rank (S i)
        (HensonOneType.rank (u i)) (u i))
    (hActual : ∀ i : Fin d, ∀ x : HensonOneType ell E,
      x ∈ S i → HensonOneType.IsCodingNode x)
    (hSymB : ∀ i j : Nat, B i j = B j i)
    (hGlobal : ∀ C : Finset Nat,
      C ⊆ Finset.range N → C.Nonempty →
      IsDirectedCliqueOn B C →
      C.card ≤ trackFCommonRawAge d ell m E
        (fun i => (u i).neighbours) (C.image σ)) :
    ∃ f : Nat → Nat,
      (∀ i j : Nat, i < j → j < N → f i < f j) ∧
      (∀ i : Nat, i < N → m ≤ f i) ∧
      (∀ i : Nat, i < N → ∃ t : HensonOneType ell E,
        t.level = f i ∧ t ∈ S (σ i)) ∧
      (∀ i : Nat, i < N → ∀ p : Nat, p < m →
        E p (f i) = decide (p ∈ (u (σ i)).neighbours)) ∧
      (∀ i : Nat, i < N → ∀ j : Nat, j < N →
        i ≠ j → E (f i) (f j) = B i j) := by
  classical
  let π : Fin (N + 1) → Fin d := fun i => σ i.val
  let τ : Nat → Fin (N + 1) :=
    fun i => ⟨i % (N + 1), Nat.mod_lt _ (Nat.succ_pos N)⟩
  let U : Fin d → Finset Nat := fun i => (u i).neighbours
  have hParent : ∀ a : Nat, a < N → π (τ a) = σ a := by
    intro a ha
    change σ (a % (N + 1)) = σ a
    rw [Nat.mod_eq_of_lt (by omega)]
  have hτInj : Set.InjOn τ
      (↑(Finset.range N) : Set Nat) := by
    intro a ha b hb hab
    have haN : a < N := Finset.mem_range.mp ha
    have hbN : b < N := Finset.mem_range.mp hb
    have hv := congrArg Fin.val hab
    change a % (N + 1) = b % (N + 1) at hv
    rw [Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at hv
    exact hv
  obtain ⟨H, G, hG, hRawMixed, hRawOne⟩ :=
    trackFPrivate_rank_zero_raw_transfer
      d (N + 1) ell m E u S π hRootLevel hLarge
  have hmH : m ≤ H := by
    let k : Fin (N + 1) := ⟨0, Nat.succ_pos N⟩
    calc
      m = (u (π k)).level := (hRootLevel (π k)).symm
      _ ≤ (G k).level := (hG k).2.1.1
      _ = H := (hG k).1
  have hBelowG :
      ∀ i : Fin (N + 1), ∀ x,
        x ∈ (G i).neighbours → x < H := by
    intro i x hx
    have hBound := (G i).below x hx
    rw [(hG i).1] at hBound
    exact hBound
  have hGlobalPrivate :
      ∀ C : Finset Nat,
        C ⊆ Finset.range N → C.Nonempty →
        IsDirectedCliqueOn B C →
        C.card ≤ trackFCommonRawAge (N + 1) ell H E
          (fun i => (G i).neighbours) (C.image τ) :=
    trackFPrivateSort_all_cliques_feasible
      d (N + 1) N B σ τ π
      (fun T => trackFCommonRawAge d ell m E U T)
      (fun T => trackFCommonRawAge (N + 1) ell H E
        (fun i => (G i).neighbours) T)
      hτInj hParent hRawOne hRawMixed hGlobal
  obtain ⟨f, hOrdered, hAfterH, hCoding, hColumnH, hInduced⟩ :=
    trackFRankZero_realizes_all_feasible_sorted_graph
      (N + 1) ell H N E B
      (fun i => (G i).neighbours) τ
      (fun i => S (π i)) G
      (fun i => (hG i).1)
      (fun _ => rfl)
      (fun i => (hG i).2.2.1)
      (fun i => (hG i).2.2.2)
      (fun i x hx => hActual (π i) x hx)
      hBelowG hSymB hGlobalPrivate
  refine ⟨f, hOrdered, ?_, ?_, ?_, hInduced⟩
  · intro i hi
    exact hmH.trans (hAfterH i hi)
  · intro i hi
    obtain ⟨t, htLevel, htSet⟩ := hCoding i hi
    refine ⟨t, htLevel, ?_⟩
    simpa only [hParent i hi] using htSet
  · intro i hi p hp
    have hpH : p < H := lt_of_lt_of_le hp hmH
    have hColumn := hColumnH i hi p hpH
    have hExt : u (π (τ i)) ≤ G (τ i) :=
      (hG (τ i)).2.1
    have hpRoot : p < (u (π (τ i))).level := by
      rw [hRootLevel (π (τ i))]
      exact hp
    have hBits :
        (p ∈ (G (τ i)).neighbours) ↔
        (p ∈ (u (σ i)).neighbours) := by
      simpa only [hParent i hi] using
        (hExt.2 p hpRoot).symm
    have hDecide :
        decide (p ∈ (G (τ i)).neighbours) =
        decide (p ∈ (u (σ i)).neighbours) := by
      by_cases hOldBit : p ∈ (u (σ i)).neighbours
      · have hNewBit : p ∈ (G (τ i)).neighbours :=
          hBits.mpr hOldBit
        simp [hOldBit, hNewBit]
      · have hNewBit : p ∉ (G (τ i)).neighbours :=
          fun hx => hOldBit (hBits.mp hx)
        simp [hOldBit, hNewBit]
    exact hColumn.trans hDecide

end Kk
