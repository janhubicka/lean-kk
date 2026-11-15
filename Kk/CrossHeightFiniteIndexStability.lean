import Kk.CrossHeightOldRangeStability
import Kk.TwoFiniteIndexNewRootStability
import Mathlib.Tactic

/-!
# Track E: finite physical old/new Kpt indices under INCREASING TOP

Both actual AlgorithmRuns have distinct finite exhaustive true Kpt
source-node indices, possibly of DIFFERENT sizes, at different
scan tops. Given literal source seed inclusion and a REAL old-top
seed, it suffices to check just two one-sided NEW→OLD finite tests
for each cut strictly below oldTop:

  * each live new terminal node's level has a live old terminal;
  * each live new same-node full old+upper L+ crossing pair
    is realized by some live old source node.

Then the old selected-level skeleton equals the taller new run's
selected levels RESTRICTED to oldTop at every old-range stage.
No bijection of indices, selected-shadow graph-age shortcut,
functional I2 assumption, common source orbit or uniform BRD bound.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The FINITE old-range stability certificate for two true Kpt
AlgorithmRuns with different scan heights.

The tests are genuinely finite for actual numerical H+ runs by
Track C's exhaustive source theorem; their construction from a
given macrodiary still requires real source-cut normalization.
-/
theorem crossheight_runs_old_range_eq_of_two_finite_index_cover
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y) (oldTop newTop : Nat)
    (hTopLe : oldTop ≤ newTop)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = oldTop)
    (RunX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (RunY : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y newTop)
    (nodeX : Fin P → AdmissibleKptNode family)
    (nodeY : Fin Q → AdmissibleKptNode family)
    (liveX : Nat → Fin P → Bool)
    (liveY : Nat → Fin Q → Bool)
    (hExactX : ∀ cut : Nat, cut < oldTop →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (RunX.I (cut+1)) X ↔
        ∃ i : Fin P, nodeX i = z ∧ liveX cut i = true)
    (hExactY : ∀ cut : Nat, cut < oldTop →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (RunY.I (cut+1)) Y ↔
        ∃ j : Fin Q, nodeY j = z ∧ liveY cut j = true)
    (hTermCover : ∀ cut : Nat, cut < oldTop →
      ∀ j : Fin Q, liveY cut j = true →
        LevelTree.lev (nodeY j) = cut →
        ∃ i : Fin P, liveX cut i = true ∧
          LevelTree.lev (nodeX i) = cut)
    (hPairCover : ∀ cut : Nat, cut < oldTop →
      ∀ j : Fin Q, liveY cut j = true →
        ∀ T : PartialTypeWithE cut db du dd,
          ∀ U : PartialTypeWithE (cut+1) db du dd,
            kptFullOldAtCut (nodeY j) cut =
              some (⟨cut,T⟩ : RawPartialTypeNode db du dd) →
            kptFullUpperAtCut (nodeY j) cut =
              some (⟨cut+1,U⟩ : RawPartialTypeNode db du dd) →
            ∃ i : Fin P, liveX cut i = true ∧
              kptFullOldAtCut (nodeX i) cut =
                some (⟨cut,T⟩ : RawPartialTypeNode db du dd) ∧
              kptFullUpperAtCut (nodeX i) cut =
                some (⟨cut+1,U⟩ : RawPartialTypeNode db du dd)) :
    ∀ i : Nat, i ≤ oldTop →
      RunX.I i = {q : Nat | q ∈ RunY.I i ∧ q ≤ oldTop} := by
  apply crossheight_runs_all_old_range_levels_eq_of_no_novelty
    family X Y hXY oldTop newTop hTopLe hTopSeed RunX RunY
  intro cut hCut
  constructor
  · rintro ⟨z,hZY,hLev⟩
    obtain ⟨j,hNode,hLive⟩ := (hExactY cut hCut z).mp hZY
    obtain ⟨i,hOldLive,hOldLevel⟩ :=
      hTermCover cut hCut j hLive (by simpa only [hNode] using hLev)
    exact ⟨nodeX i, (hExactX cut hCut (nodeX i)).mpr
      ⟨i,rfl,hOldLive⟩, hOldLevel⟩
  · intro p hp
    have hNewIndexed :
        p ∈ IndexedPhysicalCrossing family nodeY liveY cut := by
      rw [indexed_physical_crossing_eq_full_closure_relation
        family nodeY liveY
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RunY.I (cut+1)) Y) cut (hExactY cut hCut)]
      exact hp
    obtain ⟨j,hLive,hOldRaw,hUpperRaw⟩ := hNewIndexed
    obtain ⟨i,hOldLive,hOldType,hUpperType⟩ :=
      hPairCover cut hCut j hLive p.1 p.2 hOldRaw hUpperRaw
    have hOldIndexed :
        p ∈ IndexedPhysicalCrossing family nodeX liveX cut :=
      ⟨i,hOldLive,hOldType,hUpperType⟩
    rw [indexed_physical_crossing_eq_full_closure_relation
      family nodeX liveX
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (RunX.I (cut+1)) X) cut (hExactX cut hCut)] at hOldIndexed
    exact hOldIndexed

end Kk
