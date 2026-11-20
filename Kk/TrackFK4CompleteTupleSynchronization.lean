import Kk.TrackFK4SimultaneousCompatibleFront
import Kk.TrackFPairwiseTargetSeparation
import Kk.TrackFPrivateMarkerFullRawProfile
import Mathlib.Tactic

/-!
# Track F: full finite K4 tuple synchronization (ordinary graph-age data)

Audited English proof written first in
docs/track_f_k4_complete_tuple_synchronization_english_audit_20261120.md.

From individual rank-compatible ACTUAL source/target coding-node fibres
over DISTINCT same-level source one-types, construct, for any target
cutoff, an entirely simultaneous common-level compatible front with:
* all source ranks and target ranks unchanged,
* each target actual source coding fibre still large,
* private fresh source positive-neighbour markers,
* literal equality of EVERY nonempty source raw support bound,
* genuinely injective target finite type tuple,
* complete canonical finite sorted-graph class equality, uniformly
  for EVERY finite symmetric K4-free B and arbitrary repeated labels.

The proof combines merged, strict-gated #403, #407, #400, #399.
No chronology-preserving induced embedding, auxiliary Kpt E/parameter
history, diary occurrence or global BRD lower bound is asserted.
-/

namespace Kk

/-- Complete normalized integer-witness clique-feasibility test on
EVERY clique of B and EVERY admissible nonempty sort support.
Its supports include ones containing unused labels of a clique.
This is a finite graph-age predicate, NOT a target diary orbit. -/
def k4CanonicalSortedFiniteTest
    (d front N : Nat)
    (E B : Nat → Nat → Bool)
    (u : Fin d → HensonOneType 4 E)
    (σ : Nat → Fin d) : Prop :=
  ∀ C : Finset Nat,
    C ⊆ Finset.range N →
    IsDirectedCliqueOn B C →
    ∀ T : IntegerGraphSupport d 4,
      (C.filter (fun x => σ x ∈ T.1)).card ≤
        integerGraphAgeCanonical d 4
          (fun Q : IntegerGraphSupport d 4 =>
            trackFCommonRawAge d 4 front E
              (fun i => (u i).neighbours) Q.1) T

/-- THE K4 FINITE-TUPLE SYNCHRONIZATION THEOREM.

Initial source types must be distinct genuine one-types of ONE common
source old level m, but assigned target types may begin at different
levels and may coincide. Each initial SOURCE→TARGET pair has equal
genuine singleton rank and a recursively rank-large ACTUAL source
coding-node target fibre. The induced map e need not preserve
chronological source order.

For any K, construct a single target level H≥K, a common source
level M, source refinements and target refinements such that:
1. source ranks/target ranks still agree with original ranks;
2. target original coding-node fibres remain rank-large;
3. new source positive-neighbour markers are private to their sorts;
4. every nonempty source raw support is literally unchanged;
5. target prefix types are pairwise distinct;
6. all complete finite K4 canonical sorted-graph feasibility
   tests are equivalent, uniformly for all finite symmetric K4-free B.

The old prefix images e([0,m)) alone need to fit below H. There
is NO target cutoff condition on images of freshly added markers.
The theorem does not realize each diary or show unavoidability. -/
theorem k4_sync_complete_tuple_canonical_class
    (d m cutoff : Nat)
    (Esrc Etgt : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily 4 (by decide) →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (u : Fin d → HensonOneType 4 Esrc)
    (v : Fin d → HensonOneType 4 Etgt)
    (hOldLevel : ∀ i, (u i).level = m)
    (hOldInj : Function.Injective u)
    (hRank : ∀ i, HensonOneType.rank (v i) =
      HensonOneType.rank (u i))
    (hLarge : ∀ i,
      RankLargeness.Large HensonOneType.rank
        (HensonOneType.sourceCodingFibre (E := Esrc) Etgt e (v i))
        (HensonOneType.rank (u i)) (u i)) :
    ∃ H M : Nat,
    ∃ uNew : Fin d → HensonOneType 4 Esrc,
    ∃ vNew : Fin d → HensonOneType 4 Etgt,
      cutoff ≤ H ∧
      (∀ i : Fin d,
        (uNew i).level = M ∧
        u i ≤ uNew i ∧
        HensonOneType.rank (uNew i) = HensonOneType.rank (u i)) ∧
      (∀ i : Fin d,
        v i ≤ vNew i ∧
        (vNew i).level = H ∧
        HensonOneType.rank (vNew i) = HensonOneType.rank (u i) ∧
        RankLargeness.Large HensonOneType.rank
          (HensonOneType.sourceCodingFibre (E := Esrc) Etgt e (vNew i))
          (HensonOneType.rank (uNew i)) (uNew i)) ∧
      Function.Injective vNew ∧
      (∀ i j : Fin d, i ≠ j →
        ∀ x : Nat, m ≤ x →
          ¬ (x ∈ (uNew i).neighbours ∧
             x ∈ (uNew j).neighbours)) ∧
      (∀ S : Finset (Fin d), S.Nonempty →
        trackFCommonRawAge d 4 m Esrc
          (fun i => (u i).neighbours) S =
        trackFCommonRawAge d 4 M Esrc
          (fun i => (uNew i).neighbours) S) ∧
      (∀ N : Nat, ∀ B : Nat → Nat → Bool, ∀ σ : Nat → Fin d,
        (∀ i j, B i j = B j i) →
        finitePoolCliqueCheck B 4 (Finset.range N) = false →
        (k4CanonicalSortedFiniteTest d m N Esrc B u σ ↔
         k4CanonicalSortedFiniteTest d H N Etgt B vNew σ)) := by
  classical
  let H : Nat :=
    max cutoff
      (max
        ((Finset.univ : Finset (Fin d)).sup
          (fun i => (v i).level))
        (((Finset.range m).sup (fun a => e a)) + 1))
  have hCutoff : cutoff ≤ H := le_max_left _ _
  have hVBelow : ∀ i, (v i).level ≤ H := by
    intro i
    have hSup : (v i).level ≤
        (Finset.univ : Finset (Fin d)).sup
          (fun j => (v j).level) :=
      Finset.le_sup
        (f := fun j : Fin d => (v j).level)
        (Finset.mem_univ i)
    exact hSup.trans ((le_max_left _ _).trans (le_max_right _ _))
  have hImageOld : ∀ a, a < m → e a < H := by
    intro a ha
    have hSup : e a ≤
        (Finset.range m).sup (fun t => e t) :=
      Finset.le_sup
        (f := fun t => e t) (Finset.mem_range.mpr ha)
    have hBound :
        (Finset.range m).sup (fun t => e t) + 1 ≤ H :=
      (le_max_right _ _).trans (le_max_right _ _)
    omega
  obtain ⟨M, uNew, vNew, hValid, hFresh⟩ :=
    HensonOneType.k4_private_exact_target_common_source_front
      d H Esrc Etgt hAvoid e he hInduced
      u v hVBelow hRank hLarge
  have hSourceLevel : ∀ i, (uNew i).level = M := by
    intro i
    rcases hValid i with ⟨hLevel, _, _, _, _, _, _⟩
    exact hLevel
  have hRefine : ∀ i, u i ≤ uNew i := by
    intro i
    rcases hValid i with ⟨_, hRoot, _, _, _, _, _⟩
    exact hRoot
  have hSameRank : ∀ i,
      HensonOneType.rank (u i) = HensonOneType.rank (uNew i) := by
    intro i
    rcases hValid i with ⟨_, _, _, _, hRankNew, _, _⟩
    exact hRankNew.symm
  have hVRefine : ∀ i, v i ≤ vNew i := by
    intro i
    rcases hValid i with ⟨_, _, hOldV, _, _, _, _⟩
    exact hOldV
  have hTargetLevel : ∀ i, (vNew i).level = H := by
    intro i
    rcases hValid i with ⟨_, _, _, hLevel, _, _, _⟩
    exact hLevel
  have hTargetRank : ∀ i,
      HensonOneType.rank (vNew i) = HensonOneType.rank (u i) := by
    intro i
    rcases hValid i with ⟨_, _, _, _, _, hrank, _⟩
    exact hrank
  have hNewLarge : ∀ i,
      RankLargeness.Large HensonOneType.rank
        (HensonOneType.sourceCodingFibre (E := Esrc) Etgt e (vNew i))
        (HensonOneType.rank (uNew i)) (uNew i) := by
    intro i
    rcases hValid i with ⟨_, _, _, _, hrank, _, hlarg⟩
    simpa only [hrank] using hlarg
  have hPrivate : ∀ i j : Fin d, i ≠ j →
      ∀ x : Nat, m ≤ x →
        ¬ (x ∈ (uNew i).neighbours ∧
           x ∈ (uNew j).neighbours) := by
    intro i j hij x hmx hBoth
    have hOldNotI : x ∉ (u i).neighbours := by
      intro hx
      have hxOld : x < (u i).level := (u i).below x hx
      rw [hOldLevel i] at hxOld
      omega
    have hOldNotJ : x ∉ (u j).neighbours := by
      intro hx
      have hxOld : x < (u j).level := (u j).below x hx
      rw [hOldLevel j] at hxOld
      omega
    have hFreshI :
        x ∈ (uNew i).neighbours \ (u i).neighbours :=
      Finset.mem_sdiff.mpr ⟨hBoth.1, hOldNotI⟩
    have hFreshJ :
        x ∈ (uNew j).neighbours \ (u j).neighbours :=
      Finset.mem_sdiff.mpr ⟨hBoth.2, hOldNotJ⟩
    exact (Finset.disjoint_left.mp (hFresh i j hij))
      hFreshI hFreshJ
  have hRawSame :
      ∀ S : Finset (Fin d), S.Nonempty →
        trackFCommonRawAge d 4 m Esrc
          (fun i => (u i).neighbours) S =
        trackFCommonRawAge d 4 M Esrc
          (fun i => (uNew i).neighbours) S :=
    trackFCommonRawAge_eq_of_same_rank_private_markers
      d 4 m M Esrc u uNew hOldLevel hSourceLevel
      hRefine hSameRank hPrivate
  have hTargetInj : Function.Injective vNew :=
    HensonOneType.target_finite_family_injective_of_distinct_source_roots
      d 4 m H Esrc Etgt e hInduced
      u uNew vNew hOldLevel hOldInj hTargetLevel
      hRefine hImageOld hNewLarge
  have hImageBelowOriginal :
      ∀ i c, c ∈ (u i).neighbours → e c < H := by
    intro i c hc
    have hcm : c < m := by
      have hlt := (u i).below c hc
      simpa only [hOldLevel i] using hlt
    exact hImageOld c hcm
  have hCanonicalIff :
      ∀ N : Nat, ∀ B : Nat → Nat → Bool, ∀ σ : Nat → Fin d,
        (∀ i j, B i j = B j i) →
        finitePoolCliqueCheck B 4 (Finset.range N) = false →
        (k4CanonicalSortedFiniteTest d m N Esrc B u σ ↔
         k4CanonicalSortedFiniteTest d H N Etgt B vNew σ) := by
    intro N B σ hSymB hBFree
    exact trackFOriginalRefined_canonical_iff_of_private_markers
      d 4 m M H N (by decide)
      Esrc Etgt B hAvoid e he hInduced
      u uNew vNew σ
      hOldLevel hSourceLevel hTargetLevel
      hRefine hSameRank hPrivate
      hImageBelowOriginal hNewLarge hSymB hBFree
  refine ⟨H, M, uNew, vNew, hCutoff, ?_, ?_,
    hTargetInj, hPrivate, hRawSame, hCanonicalIff⟩
  · intro i
    exact ⟨hSourceLevel i, hRefine i, (hSameRank i).symm⟩
  · intro i
    exact ⟨hVRefine i, hTargetLevel i, hTargetRank i,
      hNewLarge i⟩

end Kk
