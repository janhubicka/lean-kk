import Kk.TrackFRealHensonRankDrop
import Kk.RankLargenessPartition
import Mathlib.Tactic

/-!
# Track F: actual finite Henson one-types as a ranked extension preorder

English proof, scope audit, and counterexample guards were committed
before Lean in docs/track_f_actual_one_type_tree_english_audit.md.

The nodes retain the COMPLETE old neighbourhood of a hypothetical
new vertex in the original Henson graph, with the genuine finite
K_(ell-1)-free compatibility test. Neither diagram ages nor diary
counts are used. Real rank drops require explicitly displayed
Henson forbidden-family and OnePointLeftDense hypotheses.

The terminal result is only the one-type density/finite-avoidance
interface. Simultaneous multi-sort richness and BRD lower bounds
remain open.
-/

namespace Kk

/-- A genuine consistent one-point neighbourhood over the actual
chronological initial segment [0,level). -/
structure HensonOneType (ell : Nat) (E : Nat → Nat → Bool) where
  level : Nat
  neighbours : Finset Nat
  below : ∀ x ∈ neighbours, x < level
  safe : finitePoolCliqueCheck E (ell - 1) neighbours = false

namespace HensonOneType

variable {ell : Nat} {E : Nat → Nat → Bool}

/-- Chronological extension: ALL positive and negative bits below
the old level agree. This is stronger than merely extending the
positive neighbour set as an unordered finite subset. -/
def Extends (u v : HensonOneType ell E) : Prop :=
  u.level ≤ v.level ∧
    ∀ x : Nat, x < u.level →
      (x ∈ u.neighbours ↔ x ∈ v.neighbours)

instance : Preorder (HensonOneType ell E) where
  le := Extends
  lt u v := Extends u v ∧ ¬ Extends v u
  le_refl := by
    intro u
    exact ⟨le_refl _, fun _ _ => Iff.rfl⟩
  le_trans := by
    intro u v w huv hvw
    refine ⟨huv.1.trans hvw.1, ?_⟩
    intro x hx
    exact (huv.2 x hx).trans
      (hvw.2 x (lt_of_lt_of_le hx huv.1))

/-- Exact actual zero-based rank (one less than manuscript
singleton age), defined from the old graph's maximum clique. -/
def rank (u : HensonOneType ell E) : Nat :=
  finiteHensonTypeRank ell E u.neighbours - 1

/-- Rank is antitone along chronological extensions, with no
extra source-graph realization hypotheses. -/
theorem rank_antitone :
    Antitone (fun u : HensonOneType ell E => rank u) := by
  intro u v huv
  have hSub : u.neighbours ⊆ v.neighbours := by
    intro x hx
    exact (huv.2 x (u.below x hx)).mp hx
  have hCap := finiteHensonTypeRank_antitone
    ell E u.neighbours v.neighbours hSub
  dsimp [rank]
  omega

/-- Zero padding changes only the prefix length, retaining exactly
the original actual old-neighbour set and its validity certificate. -/
def zeroPad (u : HensonOneType ell E) (m : Nat)
    (hm : u.level ≤ m) : HensonOneType ell E where
  level := m
  neighbours := u.neighbours
  below := by
    intro x hx
    exact lt_of_lt_of_le (u.below x hx) hm
  safe := u.safe

theorem le_zeroPad (u : HensonOneType ell E) (m : Nat)
    (hm : u.level ≤ m) : u ≤ zeroPad u m hm := by
  exact ⟨hm, fun _ _ => Iff.rfl⟩

theorem rank_zeroPad (u : HensonOneType ell E) (m : Nat)
    (hm : u.level ≤ m) : rank (zeroPad u m hm) = rank u := rfl

/-- Finite sets are avoidable by an entire SAME-RANK cone in this
concrete finite-type tree. This is not true in arbitrary preorders.
The proof uses zero padding to exceed every forbidden node's height. -/
theorem finite_cone_escape (F : Finset (HensonOneType ell E))
    (u : HensonOneType ell E) :
    ∃ v : HensonOneType ell E,
      u ≤ v ∧ rank v = rank u ∧
        ∀ w : HensonOneType ell E, v ≤ w → w ∉ F := by
  classical
  let cap : Nat := F.sup (fun t => t.level)
  let m : Nat := max u.level (cap + 1)
  let v : HensonOneType ell E :=
    zeroPad u m (le_max_left _ _)
  refine ⟨v, le_zeroPad u m (le_max_left _ _),
    rank_zeroPad u m (le_max_left _ _), ?_⟩
  intro w hvw hwF
  have hCard : w.level ≤ cap :=
    Finset.le_sup (f := fun t : HensonOneType ell E => t.level) hwF
  have hTall : m ≤ w.level := hvw.1
  have hBound : cap + 1 ≤ m := le_max_right _ _
  omega

/-- A physical rank drop on a real Henson type: one actual later
original is added to the old neighbour set, via the exact clique
certificate and complete-column theorem in TrackFRealHensonRankDrop. -/
theorem real_rank_drop
    (ell : Nat) (hell : 3 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell (by omega) →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (n : Nat) (u : HensonOneType ell E)
    (hu : rank u = n + 1) :
    ∃ w : HensonOneType ell E, u ≤ w ∧ rank w = n := by
  have hSafeOld :
      finiteDirectedCliqueCapacity E u.neighbours < ell - 1 :=
    (finitePoolCliqueCheck_false_iff_capacity_lt
      E (ell - 1) u.neighbours).1 u.safe
  have hEnough :
      finiteDirectedCliqueCapacity E u.neighbours + 3 ≤ ell := by
    dsimp [rank, finiteHensonTypeRank] at hu
    omega
  obtain ⟨C, v, _hCU, _hClique, _hCcard, hv, _hColumn,
    hNewCap, hNewSafe, hNewRank⟩ :=
    henson_leftDense_exact_type_rank_drop
      ell hell E hAvoid hDense u.level u.neighbours
      u.below hEnough
  let w : HensonOneType ell E := {
    level := v + 1
    neighbours := insert v u.neighbours
    below := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hEq | hOld
      · omega
      · have hxlt := u.below x hOld
        omega
    safe := hNewSafe
  }
  refine ⟨w, ?_, ?_⟩
  · constructor
    · change u.level ≤ v + 1
      omega
    · intro x hx
      change (x ∈ u.neighbours ↔ x ∈ insert v u.neighbours)
      constructor
      · intro hxU
        exact Finset.mem_insert_of_mem hxU
      · intro hxNew
        rcases Finset.mem_insert.mp hxNew with hEq | hxU
        · have hxNe : x ≠ v := by omega
          exact False.elim (hxNe hEq)
        · exact hxU
  · change finiteHensonTypeRank ell E
      (insert v u.neighbours) - 1 = n
    have hOldZero : finiteHensonTypeRank ell E u.neighbours -
      1 = n + 1 := hu
    omega

/-- The actual Henson one-type tree satisfies the abstract rank-drop
premise, conditional only on the graph's two explicit source axioms. -/
theorem every_positive_rank_drops
    (ell : Nat) (hell : 3 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell (by omega) →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell) :
    ∀ n (u : HensonOneType ell E), rank u = n + 1 →
      ∃ w, u ≤ w ∧ rank w = n := by
  intro n u hu
  exact real_rank_drop ell hell E hAvoid hDense n u hu

/-- Density REALLY implies recursive rank-largeness in the
chronological Henson one-type preorder. The rank-drop hypothesis
is now derived from physical one-point graph extensions, rather
than assumed as an axiom of abstract diaries. -/
theorem density_implies_rank_large
    (ell : Nat) (hell : 3 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell (by omega) →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (S : Set (HensonOneType ell E)) (u : HensonOneType ell E)
    (hDenseS : RankLargeness.Large
      (fun t : HensonOneType ell E => rank t) S 0 u) :
    RankLargeness.Large
      (fun t : HensonOneType ell E => rank t) S (rank u) u := by
  exact RankLargeness.dense_implies_large
    (fun t : HensonOneType ell E => rank t)
    (every_positive_rank_drops ell hell E hAvoid hDense)
    S (rank u) u rfl hDenseS

/-- Finite deletion from a rank-large subset of ACTUAL one-types.
The finite set F need not be closed under extensions or represent a
diary. Its uniform cone escape is proved by zero padding, not by
assuming an arbitrary preorder has the property. -/
theorem large_difference_finite
    (S : Set (HensonOneType ell E))
    (F : Finset (HensonOneType ell E))
    (u : HensonOneType ell E)
    (hLarge : RankLargeness.Large
      (fun t : HensonOneType ell E => rank t)
      S (rank u) u) :
    ∃ v : HensonOneType ell E,
      u ≤ v ∧ rank v = rank u ∧
        RankLargeness.Large
          (fun t : HensonOneType ell E => rank t)
          (S \ (↑F : Set (HensonOneType ell E))) (rank u) v := by
  apply RankLargeness.large_difference_of_cone_escape
    (fun t : HensonOneType ell E => rank t)
    rank_antitone S (↑F : Set (HensonOneType ell E))
    (rank u) u rfl hLarge
  intro v huv hv
  obtain ⟨z, hvz, hzRank, hAvoid⟩ := finite_cone_escape F v
  exact ⟨z, hvz, hzRank.trans hv, by
    intro w hzw hwF
    exact hAvoid w hzw (by simpa using hwF)⟩

end HensonOneType
end Kk
