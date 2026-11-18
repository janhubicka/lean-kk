import Kk.TrackFRankZeroPrescribedPast
import Kk.TrackFMultiSortRawIsolation
import Kk.FiniteCliqueIntegerWitness
import Mathlib.Tactic

/-!
# Track F: genuine one-point graph age safety from sorted clique constraints

English-first proof and twelve hostile checks:
docs/track_f_one_point_gluing_safety_english_audit.md

Given actual old source Henson neighbourhoods U_i on one prefix m,
a finite set past of already chosen later ACTUAL originals with
correct old-prefix edge columns for their source sort labels, and
a set positive ⊆ past of originals which the next sort-j coding
vertex must see, the true raw support inequality for EVERY
directed clique D ⊆ positive implies U_j ∪ positive is
K_(ell-1)-free. The proof is a genuine old/new clique
decomposition and uses actual directed old-source edges.

Composing this safety proof with the previously verified rank-zero
dense original-coding-vertex theorem yields one actual vertex with
all desired positive and negative edges to the past.

This proves the ONE-VERTEX base step from a finite gluing
feasibility invariant; it does NOT yet construct an arbitrary
finite sorted graph jointly across several coding fibres.
-/

namespace Kk

/-- Exact local source graph-age safety for the next sorted point.

All source old neighbour sets U_i live before m. Every already
selected coding original c in past lives at or beyond m and has
its complete FORWARD old edge column equal to U_(sort c).
The proposed new vertex of sort j sees exactly positive ⊆ past.

For every actual directed clique D ⊆ positive, require that
the new vertex joined to D obey the true old RAW source support
bound on insert j (D.image sort). Then its full proposed old
neighbourhood U_j ∪ positive is genuinely K_(ell-1)-free.

The assumption checks EVERY clique D ⊆ positive, not merely
positive itself (which need not be a clique). Neither a full
diary characterization nor a new Henson axiom is assumed. -/
theorem trackFOnePointPool_safe_of_sorted_clique_inequalities
    (d ell m : Nat) (E : Nat → Nat → Bool)
    (U : Fin d → Finset Nat)
    (hOld : ∀ i x, x ∈ U i → x < m)
    (past positive : Finset Nat)
    (hPast : ∀ c ∈ past, m ≤ c)
    (hPositive : positive ⊆ past)
    (sort : Nat → Fin d)
    (hColumn : ∀ c ∈ past, ∀ p, p < m →
      E p c = decide (p ∈ U (sort c)))
    (j : Fin d)
    (hFeasible : ∀ D : Finset Nat, D ⊆ positive →
      IsDirectedCliqueOn E D →
      D.card + 1 ≤ trackFCommonRawAge d ell m E U
        (insert j (D.image sort))) :
    finitePoolCliqueCheck E (ell - 1)
      (U j ∪ positive) = false := by
  classical
  apply (finitePoolCliqueCheck_false_iff
    E (ell - 1) (U j ∪ positive)).2
  rintro ⟨s, hsPool, hsCard, hsClique⟩
  let C : Finset Nat := s ∩ U j
  let D : Finset Nat := s ∩ positive
  have hCSubS : C ⊆ s := by
    intro x hx
    exact (Finset.mem_inter.mp hx).1
  have hDSubS : D ⊆ s := by
    intro x hx
    exact (Finset.mem_inter.mp hx).1
  have hDSubPositive : D ⊆ positive := by
    intro x hx
    exact (Finset.mem_inter.mp hx).2
  have hCDDisjoint : Disjoint C D := by
    apply Finset.disjoint_left.mpr
    intro x hxC hxD
    have hxOld : x ∈ U j := (Finset.mem_inter.mp hxC).2
    have hxPos : x ∈ positive := (Finset.mem_inter.mp hxD).2
    have hxBefore : x < m := hOld j x hxOld
    have hxAfter : m ≤ x := hPast x (hPositive hxPos)
    omega
  have hUnion : C ∪ D = s := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hxC | hxD
      · exact hCSubS hxC
      · exact hDSubS hxD
    · intro hxS
      have hxPool : x ∈ U j ∪ positive := hsPool hxS
      rcases Finset.mem_union.mp hxPool with hxU | hxPos
      · exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_inter.mpr ⟨hxS, hxU⟩))
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_inter.mpr ⟨hxS, hxPos⟩))
  have hCardUnion : s.card = C.card + D.card := by
    have hCardCD := Finset.card_union_of_disjoint hCDDisjoint
    rw [hUnion] at hCardCD
    exact hCardCD
  have hCClique : IsDirectedCliqueOn E C := by
    intro x hx y hy hxy
    exact hsClique x (hCSubS hx) y (hCSubS hy) hxy
  have hDClique : IsDirectedCliqueOn E D := by
    intro x hx y hy hxy
    exact hsClique x (hDSubS hx) y (hDSubS hy) hxy
  let support : Finset (Fin d) := insert j (D.image sort)
  let P : Finset Nat := trackFCommonNeighbourPool d m U support
  have hCInCommon : C ⊆ P := by
    intro p hpC
    have hpU : p ∈ U j := (Finset.mem_inter.mp hpC).2
    have hpOld : p < m := hOld j p hpU
    change p ∈ (Finset.range m).filter
      (fun q => ∀ i ∈ support, q ∈ U i)
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hpOld, ?_⟩
    intro i hi
    change i ∈ insert j (D.image sort) at hi
    rcases Finset.mem_insert.mp hi with hEq | hImage
    · simpa only [hEq] using hpU
    · obtain ⟨c, hcD, hci⟩ := Finset.mem_image.mp hImage
      have hcS : c ∈ s := hDSubS hcD
      have hcPos : c ∈ positive := hDSubPositive hcD
      have hcPast : c ∈ past := hPositive hcPos
      have hcAfter : m ≤ c := hPast c hcPast
      have hpNe : p ≠ c := by omega
      have hpEdge : E p c = true :=
        hsClique p (hCSubS hpC) c hcS hpNe
      have hpBit : decide (p ∈ U (sort c)) = true :=
        (hColumn c hcPast p hpOld).symm.trans hpEdge
      have hpMember : p ∈ U (sort c) := by
        simpa only [decide_eq_true_eq] using hpBit
      exact hci ▸ hpMember
  have hCCap :
      C.card ≤ finiteDirectedCliqueCapacity E P :=
    directedClique_card_le_capacity
      E P C hCInCommon hCClique
  have hAge := hFeasible D hDSubPositive hDClique
  change D.card + 1 ≤
    ell - 1 - finiteDirectedCliqueCapacity E P at hAge
  omega

end Kk

namespace Kk.HensonOneType

/-- Actual new coding-vertex realization from the source sorted
clique feasibility invariant, WITHOUT an separately assumed
K_(ell-1)-free neighbourhood certificate.

The real one-point safety certificate is derived by the previous
theorem. The actual coding original is then chosen from a
rank-zero dense coding-node fibre using verified PR #340.
This is the single-vertex induction step for a prospective
finite sorted graph gluing, not the full joint induction. -/
theorem rank_zero_dense_actualCoding_realizes_feasible_past
    {ell : Nat} {E : Nat → Nat → Bool}
    (S : Set (HensonOneType ell E))
    (u : HensonOneType ell E)
    (hu : rank u = 0)
    (hLarge : RankLargeness.Large rank S 0 u)
    (hActual : ∀ x : HensonOneType ell E,
      x ∈ S → IsCodingNode x)
    (d : Nat)
    (U : Fin d → Finset Nat)
    (j : Fin d)
    (hRoot : U j = u.neighbours)
    (hOld : ∀ i x, x ∈ U i → x < u.level)
    (front : Nat) (hFront : u.level ≤ front)
    (past positive : Finset Nat)
    (hPast : ∀ c ∈ past, u.level ≤ c ∧ c < front)
    (hPositive : positive ⊆ past)
    (sort : Nat → Fin d)
    (hColumn : ∀ c ∈ past, ∀ p, p < u.level →
      E p c = decide (p ∈ U (sort c)))
    (hFeasible : ∀ D : Finset Nat, D ⊆ positive →
      IsDirectedCliqueOn E D →
      D.card + 1 ≤ trackFCommonRawAge d ell u.level E U
        (insert j (D.image sort))) :
    ∃ x : HensonOneType ell E,
      u ≤ x ∧ x ∈ S ∧ front ≤ x.level ∧ rank x = 0 ∧
      (∀ p ∈ past,
        E p x.level = decide (p ∈ positive) ∧
        E x.level p = decide (p ∈ positive)) := by
  have hPastLower : ∀ c ∈ past, u.level ≤ c := by
    intro c hc
    exact (hPast c hc).1
  have hSafeRoot :
      finitePoolCliqueCheck E (ell - 1)
        (U j ∪ positive) = false :=
    trackFOnePointPool_safe_of_sorted_clique_inequalities
      d ell u.level E U hOld past positive hPastLower
      hPositive sort hColumn j hFeasible
  have hSafe :
      finitePoolCliqueCheck E (ell - 1)
        (u.neighbours ∪ positive) = false := by
    simpa only [hRoot] using hSafeRoot
  exact rank_zero_dense_actualCoding_realizes_safe_past
    S u hu hLarge hActual front hFront past positive
    hPast hPositive hSafe

end Kk.HensonOneType
