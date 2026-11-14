import Kk.NoNewRootEventCriterion
import Kk.IndexedPhysicalCrossing
import Mathlib.Tactic

/-!
# Track E: two actual FINITE Kpt source indices certify inert root growth

Two genuine same-horizon Kpt AlgorithmRuns on X ⊆ Y may have
distinct finite exhaustive Kpt node indices and activity masks.

If every LIVE new terminal source is covered by some LIVE old
terminal source at the SAME cut and every LIVE new complete
old/upper dependent L+ crossing has a matching LIVE old index
with the SAME exact pair, then the actual selected levels of the
two runs are EQUAL at every stage.

The finite coverage conditions are ONE-SIDED new→old: the reverse
direction follows from literal Kpt seed inclusion and genuine
closure/AlgorithmRun monotonicity (proved earlier in Track E).

Different index sizes, duplicates, actual I2 forks and all E bits
are permitted. No selected-front shadow or infinite age witness
is substituted for a complete Kpt source.

English-first proof and hostile audit:
  docs/track_e_monotone_seed_growth_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- For TWO genuine physical Kpt source indices (possibly of
different finite cardinalities) the full stagewise selected-level
skeleton agrees, provided every LIVE new source event has a
matching LIVE old physical source witness.

Terminal index matching preserves the actual Boolean I1 decision.
Full pair matching preserves the real old/upper L+ crossing
RELATION (not merely its upper ordinary-L reduct) and therefore
the genuine Kpt monoid I2/I3 decision at that cut.

There is no name bijection, no required equality of the two
entire closures, no no-I2 assumption, and no artificially added
E on the finite L-only corrected B3 age witnesses.

This proves ONLY selected-level equality, not equality of
the chosen monoid maps or a common labelled inverse-source orbit. -/
theorem two_actual_Kpt_runs_levels_eq_of_two_finite_index_cover
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y) (top : Nat)
    (RunX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (RunY : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y top)
    (nodeX : Fin P → AdmissibleKptNode family)
    (nodeY : Fin Q → AdmissibleKptNode family)
    (liveX : Nat → Fin P → Bool)
    (liveY : Nat → Fin Q → Bool)
    (hExactX : ∀ cut : Nat, cut < top →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (RunX.I (cut+1)) X ↔
        ∃ i : Fin P, nodeX i = z ∧ liveX cut i = true)
    (hExactY : ∀ cut : Nat, cut < top →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (RunY.I (cut+1)) Y ↔
        ∃ j : Fin Q, nodeY j = z ∧ liveY cut j = true)
    (hTermCover : ∀ cut : Nat, cut < top →
      ∀ j : Fin Q, liveY cut j = true →
        LevelTree.lev (nodeY j) = cut →
        ∃ i : Fin P, liveX cut i = true ∧
          LevelTree.lev (nodeX i) = cut)
    (hPairCover : ∀ cut : Nat, cut < top →
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
    ∀ i : Nat, i ≤ top → RunX.I i = RunY.I i := by
  apply two_actual_Kpt_runs_levels_eq_of_finite_indexed_quiet_source
    family X Y hXY top RunX RunY
    nodeY liveY hExactY
  · intro cut hCut j hLive hLev
    obtain ⟨i,hOldLive,hOldLevel⟩ :=
      hTermCover cut hCut j hLive hLev
    refine ⟨nodeX i,?_,hOldLevel⟩
    exact (hExactX cut hCut (nodeX i)).mpr
      ⟨i,rfl,hOldLive⟩
  · intro cut hCut j hLive T U hOldRaw hUpperRaw
    obtain ⟨i,hOldLive,hOldType,hUpperType⟩ :=
      hPairCover cut hCut j hLive T U hOldRaw hUpperRaw
    have hOldIndexed :
        (T,U) ∈ IndexedPhysicalCrossing family nodeX liveX cut :=
      ⟨i,hOldLive,hOldType,hUpperType⟩
    have hEq :=
      indexed_physical_crossing_eq_full_closure_relation
        family nodeX liveX
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RunX.I (cut+1)) X) cut (hExactX cut hCut)
    rw [hEq] at hOldIndexed
    exact hOldIndexed

end Kk
