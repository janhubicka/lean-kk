import Kk.NumericHFinalPoolCrossing
import Mathlib.Tactic

/-!
# Track C: preservation of a REAL multi-root numerical H+ source pool

English proof and hostile audit preceded this Lean source:
  docs/track_c_exhaustive_run_index_english_audit.md

At one finite numerical H+ stage, the initial seeds may arise from
MULTIPLE ambient originals. The genuine Kpt meet/parameter closure
is still covered by their selected-positive stage pool.

If the next seeds are inherited from that full closure or are new
genuine-prefix seeds from an actual additional root pool, their
original-prefix invariant survives after extending the root pool.

This is an induction-step INTERFACE, not a proof that every proposed
resolved-copy schedule actually satisfies the new-seed hypothesis.
No arbitrary fake target, cross-structure extension or B3 conclusion.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Any set of genuine Kpt prefix seeds, indexed by an arbitrary
finite family of ORIGINAL numeric H+ names, has the correct concrete
ambient-prefix source invariant. The choice of original may vary
from seed to seed and is not assumed unique. -/
theorem finiteNumericH_multiRoot_seeds_in_original_pool
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (roots : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hEach : ∀ z ∈ X, ∃ v : Fin N,
      v ∈ roots ∧
      z ≤ (finiteNumericH K k N).kptOriginal family hAvoid v) :
    X ⊆ ambientPrefixPool family (finiteNumericH K k N)
      hAvoid (roots : Set (Fin N)) := by
  intro z hz
  obtain ⟨v,hv,hBelow⟩ := hEach z hz
  exact ⟨(finiteNumericH K k N).kptOriginal family hAvoid v,
    ⟨v,hv,rfl⟩,hBelow⟩

/-- The ACTUAL complete meet-and-selected-parameter closure of
multi-root seeds is covered by the stage pool formed from the
old root addresses and every selected positive-free-level address.

If the NEXT seed set consists of any existing closure nodes together
with prefixes of genuinely new physical root originals W, then the
source-pool invariant survives over the expanded pool
  ambientStagePool A U I union W.

The conclusion is about one and the SAME finite H+ ambient
structure. A recursive construction must still PROVE hNext for its
actual new seeds, and must verify physical realization of new roots
when moving to another ambient structure. -/
theorem finiteNumericH_multiRoot_nextSeed_pool_preserved
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U W : Set (Fin N))
    (I : Set Nat)
    (X Y : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid U)
    (hNext : Y ⊆
      (SMTree.Envelope.closure (admissibleKptSTree family) I X) ∪
      ambientPrefixPool family (finiteNumericH K k N) hAvoid W) :
    Y ⊆ ambientPrefixPool family (finiteNumericH K k N)
      hAvoid (ambientStagePool (finiteNumericH K k N) U I ∪ W) := by
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  have hStage :
      SMTree.Envelope.closure (admissibleKptSTree family) I X ⊆
        ambientPrefixPool family A hAvoid
          (ambientStagePool A U I) :=
    admissibleKpt_stage_closure_subset_pool
      family A hAvoid U I X hX
  have hOld :
      ambientPrefixPool family A hAvoid (ambientStagePool A U I) ⊆
        ambientPrefixPool family A hAvoid
          (ambientStagePool A U I ∪ W) :=
    ambientPrefixPool_mono family A hAvoid
      (by intro v hv; exact Or.inl hv)
  have hNew :
      ambientPrefixPool family A hAvoid W ⊆
        ambientPrefixPool family A hAvoid
          (ambientStagePool A U I ∪ W) :=
    ambientPrefixPool_mono family A hAvoid
      (by intro v hv; exact Or.inr hv)
  intro z hz
  rcases hNext hz with hzOld | hzNew
  · exact hOld (hStage hzOld)
  · exact hNew hzNew

#print axioms Kk.finiteNumericH_multiRoot_seeds_in_original_pool
#print axioms Kk.finiteNumericH_multiRoot_nextSeed_pool_preserved

end Kk
