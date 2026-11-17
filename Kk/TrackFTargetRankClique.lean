import Kk.TrackFRealHensonRankDrop
import Kk.FiniteCliqueIntegerWitness
import Mathlib.Tactic

/-!
# Track F: genuine target-rank lower bound from a future clique

The English proof and adversarial scope audit were committed first:
docs/track_f_target_rank_clique_english_audit.md

All vertices and edges are ACTUAL ordinary graph data. A future
clique of size k completely joined to the old-neighbour set P
forces the target singleton type rank to be at least k. No
abstract diary lower-bound theorem or source-fibre richness
is assumed.

The global Henson variant derives the finite full-pool
K_ell-free certificate from normalized forbidden-family avoidance.
The preservation of such a clique under an induced embedding and
the existence of that clique in a rank-large source fibre remain
separate obligations.
-/

namespace Kk

/-- A clique W of actual future original vertices, each adjacent in
BOTH directed orientations to the entire target old-neighbour set P,
forces the target singleton rank to be at least |W|.

The old set P itself need not be a clique: the proof uses an
ATTAINED maximum clique C⊆P. Complete directed adjacency between
C and W makes C∪W a clique, so K_ell-freeness gives
cap_E(P)+|W| < ell. -/
theorem finiteHensonTypeRank_ge_futureClique
    (ell front : Nat)
    (E : Nat → Nat → Bool)
    (P W : Finset Nat)
    (hP : ∀ x ∈ P, x < front)
    (hW : ∀ x ∈ W, front ≤ x)
    (hWClique : IsDirectedCliqueOn E W)
    (hJoin : ∀ p ∈ P, ∀ w ∈ W,
      E p w = true ∧ E w p = true)
    (hFree : finitePoolCliqueCheck E ell (P ∪ W) = false) :
    W.card ≤ finiteHensonTypeRank ell E P := by
  classical
  obtain ⟨C, hCP, hCClique, hCcard⟩ :=
    finiteDirectedCliqueCapacity_attained E P
  have hDisjoint : Disjoint C W := by
    apply Finset.disjoint_left.mpr
    intro x hxC hxW
    have hxOld : x < front := hP x (hCP hxC)
    have hxNew : front ≤ x := hW x hxW
    omega
  have hSub : C ∪ W ⊆ P ∪ W := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxC | hxW
    · exact Finset.mem_union.mpr (Or.inl (hCP hxC))
    · exact Finset.mem_union.mpr (Or.inr hxW)
  have hClique : IsDirectedCliqueOn E (C ∪ W) := by
    intro x hx y hy hxy
    rcases Finset.mem_union.mp hx with hxC | hxW
    · rcases Finset.mem_union.mp hy with hyC | hyW
      · exact hCClique x hxC y hyC hxy
      · exact (hJoin x (hCP hxC) y hyW).1
    · rcases Finset.mem_union.mp hy with hyC | hyW
      · exact (hJoin y (hCP hyC) x hxW).2
      · exact hWClique x hxW y hyW hxy
  have hSmall :
      (C ∪ W).card < ell :=
    finiteClique_card_lt_of_pool_cliqueFree
      E ell (P ∪ W) (C ∪ W) hFree hSub hClique
  have hCard :
      (C ∪ W).card = C.card + W.card :=
    Finset.card_union_of_disjoint hDisjoint
  unfold finiteHensonTypeRank
  omega

/-- In an ACTUAL normalized K_ell-free Henson graph the global
forbidden-family predicate discharges the finite-pool exclusion.
No standalone finite-pool safety axiom needs to be supplied.

This still assumes W is an actual clique of future vertices and
all of its vertices share the displayed old-neighbour set P.
It does NOT derive those premises from abstract rank-largeness. -/
theorem henson_targetRank_ge_futureClique
    (ell front : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (P W : Finset Nat)
    (hP : ∀ x ∈ P, x < front)
    (hW : ∀ x ∈ W, front ≤ x)
    (hWClique : IsDirectedCliqueOn E W)
    (hJoin : ∀ p ∈ P, ∀ w ∈ W,
      E p w = true ∧ E w p = true) :
    W.card ≤ finiteHensonTypeRank ell E P := by
  classical
  let Q : Finset Nat := P ∪ W
  let N : Nat := Q.sup id + 1
  have hBound : ∀ x ∈ Q, x < N := by
    intro x hx
    have hMax : x ≤ Q.sup id :=
      Finset.le_sup (f := id) hx
    dsimp [N]
    omega
  have hNoClique : ¬ HasCliqueBelow E N ell :=
    hensonForbiddenFamily_no_prefix_cliques
      ell hell E hAvoid N
  have hFree : finitePoolCliqueCheck E ell (P ∪ W) = false := by
    apply (finitePoolCliqueCheck_false_iff E ell (P ∪ W)).2
    rintro ⟨s, hsSub, hsCard, hsClique⟩
    apply hNoClique
    exact ⟨s, hsCard, (fun x hx => hBound x (hsSub hx)), hsClique⟩
  exact finiteHensonTypeRank_ge_futureClique
    ell front E P W hP hW hWClique hJoin hFree

end Kk
