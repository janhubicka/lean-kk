import Kk.TrackFRealHensonTypeTree
import Kk.TrackFColouredRankLargeFan
import Mathlib.Tactic

/-!
# Track F: actual Henson coding vertices and root-compatible fibres

English-first proof and adversarial audit:
docs/track_f_actual_coding_fibre_english_audit.md

The underlying HensonOneType tree includes all consistent HYPOTHETICAL
finite types. IsCodingNode singles out the type attached to an
ACTUAL original vertex at its own chronological index.

Under normalized forbidden-family avoidance and OnePointLeftDense,
these actual coding nodes form a dense set in the finite type tree,
and hence are rank-large. The initial target-root fibre is exactly
this actual coding-node set for any image-index map e. Finite target
prefix colours are genuine pairs of directed old graph columns.

This does NOT prove a non-root target fibre is rank-large, rank
alignment under arbitrary induced embeddings, multi-sort richness,
or any BRD count.
-/

namespace Kk.HensonOneType

variable {ell : Nat} {E : Nat → Nat → Bool}

/-- A finite actual one-type is the CODING TYPE of its own original
vertex u.level, not merely an admissible hypothetical future type.
Both directed old columns and every zero/nonzero old bit must match. -/
def IsCodingNode (u : HensonOneType ell E) : Prop :=
  ∀ y : Nat, y < u.level →
    E y u.level = decide (y ∈ u.neighbours) ∧
    E u.level y = decide (y ∈ u.neighbours)

/-- The unique empty-prefix type, on the genuine finite one-type
tree. Its old-neighbourhood set is empty and valid for ell>=2. -/
def root (ell : Nat) (E : Nat → Nat → Bool)
    (hell : 2 ≤ ell) : HensonOneType ell E where
  level := 0
  neighbours := ∅
  below := by
    intro y hy
    simp at hy
  safe := by
    apply (finitePoolCliqueCheck_false_iff_capacity_lt
      E (ell - 1) (∅ : Finset Nat)).2
    rw [finiteDirectedCliqueCapacity_empty]
    omega

/-- The root has manuscript singleton age ell-1 and zero-based
Lean rank ell-2. This is a true physical clique-capacity value,
not an assumed initial diary rank. -/
theorem root_rank (ell : Nat) (E : Nat → Nat → Bool)
    (hell : 2 ≤ ell) :
    rank (root ell E hell) = ell - 2 := by
  change ell - 1 -
      finiteDirectedCliqueCapacity E (∅ : Finset Nat) - 1 = ell - 2
  rw [finiteDirectedCliqueCapacity_empty]
  omega

/-- Actual coding vertices are dense in the chronological type
tree of the explicitly left-dense normalized K_ell-free Henson
enumeration. The witness is a GENUINE original vertex x and
its exact full old-column node (x,U).

The given initial hypothetical type u is arbitrary. The
existential witness is obtained above every extension v>=u,
not merely at the root. -/
theorem codingNodes_dense
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (u : HensonOneType ell E) :
    RankLargeness.Large rank
      {w : HensonOneType ell E | IsCodingNode w} 0 u := by
  intro v _huv
  have hCap : finiteDirectedCliqueCapacity E v.neighbours < ell - 1 :=
    (finitePoolCliqueCheck_false_iff_capacity_lt
      E (ell - 1) v.neighbours).mp v.safe
  obtain ⟨x, hx, _hxBound, hColumn⟩ :=
    henson_leftDense_cofinal_exact_type
      ell hell E hAvoid hDense
      v.level v.level v.neighbours v.below hCap
  let w : HensonOneType ell E := {
    level := x
    neighbours := v.neighbours
    below := by
      intro y hy
      exact lt_of_lt_of_le (v.below y hy) hx
    safe := v.safe
  }
  refine ⟨w, ?_, ?_⟩
  · exact ⟨hx, fun _ _ => Iff.rfl⟩
  · intro y hy
    exact hColumn y hy

/-- The SET of actual original coding types is rank-large above
EVERY finite type under the explicit one-point left-density
enumeration condition. It is not the whole hypothetical tree. -/
theorem codingNodes_rank_large
    (ell : Nat) (hell : 3 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell (by omega) →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (u : HensonOneType ell E) :
    RankLargeness.Large rank
      {w : HensonOneType ell E | IsCodingNode w}
      (rank u) u := by
  exact density_implies_rank_large
    ell hell E hAvoid hDense
    {w : HensonOneType ell E | IsCodingNode w} u
    (codingNodes_dense ell (by omega) E hAvoid hDense u)

/-- Actual target-prefix colour for the image of the source coding
ORIGINAL u.level under a given index map e. The ordered colour
pair retains both orientations and is a finite type for finite H.

The function is defined on all hypothetical type nodes for
convenience; its target-embedding interpretation is valid only
when restricted to IsCodingNode and e maps source original indices. -/
def targetPrefixColour
    (Etgt : Nat → Nat → Bool) (e : Nat → Nat)
    (H : Nat) (u : HensonOneType ell E) :
    (Fin H → Bool) × (Fin H → Bool) :=
  (fun i => Etgt i.val (e u.level),
   fun i => Etgt (e u.level) i.val)

/-- The exact source coding-node fibre for an ACTUAL target-prefix
one-type v. The image original must lie beyond the target prefix;
its two directed old columns must match v. -/
def sourceCodingFibre
    (Etgt : Nat → Nat → Bool) (e : Nat → Nat)
    (v : HensonOneType ell Etgt) :
    Set (HensonOneType ell E) :=
  {u | IsCodingNode u ∧ v.level ≤ e u.level ∧
    ∀ y : Nat, y < v.level →
      Etgt y (e u.level) = decide (y ∈ v.neighbours) ∧
      Etgt (e u.level) y = decide (y ∈ v.neighbours)}

/-- The ROOT target-prefix has no old coordinates. Therefore for
any map e (not necessarily an embedding), its fibre is exactly
the ACTUAL source coding nodes; there is no hidden constraint. -/
theorem sourceCodingFibre_root
    (ell : Nat) (Esrc Etgt : Nat → Nat → Bool)
    (hell : 2 ≤ ell) (e : Nat → Nat) :
    sourceCodingFibre (E := Esrc) Etgt e (root ell Etgt hell) =
      {u : HensonOneType ell Esrc | IsCodingNode u} := by
  ext u
  constructor
  · intro hu
    exact hu.1
  · intro hu
    refine ⟨hu, Nat.zero_le _, ?_⟩
    intro y hy
    change y < 0 at hy
    omega

/-- Consequently the initial source-root / target-root fibre
is rank-large, assuming only normalized source Henson avoidance
and OnePointLeftDense of the SOURCE enumeration. This is the
precise verified BASE CASE of the pending compatibility proof;
it asserts nothing about non-root target fibres. -/
theorem sourceCodingFibre_root_rank_large
    (ell : Nat) (hell : 3 ≤ ell)
    (Esrc Etgt : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell (by omega) →
      bad.Avoids (normalizedGraphModel Esrc))
    (hDense : OnePointLeftDense Esrc ell)
    (e : Nat → Nat)
    (u : HensonOneType ell Esrc) :
    RankLargeness.Large rank
      (sourceCodingFibre (E := Esrc) Etgt e
        (root ell Etgt (by omega))) (rank u) u := by
  rw [sourceCodingFibre_root]
  exact codingNodes_rank_large ell hell Esrc hAvoid hDense u

end Kk.HensonOneType
