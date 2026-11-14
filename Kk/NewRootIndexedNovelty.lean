import Kk.NewSourceEventWitness
import Kk.IndexedPhysicalCrossing
import Kk.NumericHExhaustiveRunIndex
import Mathlib.Tactic

/-!
# Track E: FINITE true-Kpt-index witness for each newly selected cut

This refines the genuine monotonic seed-growth theorem, not a
selected-front diary approximation.

At a cut selected by a larger actual AlgorithmRun but skipped by
the smaller one, the verified full-closure source novelty theorem
yields either a NEW terminal Kpt node or a NEW complete old/upper
dependent-L+ crossing pair.

Track C's ACTUAL numerical H+ exhaustive-source theorem constructs
one finite Finset of ALL final closure nodes and an exact per-cut
Boolean live mask. The novelty event is therefore witnessed by
a live finite node INDEX, with BOTH old/upper Option records from
the SAME node. This includes auxiliary E and genuine I2 forks.

No source-size-uniform bound, resolved diary normalization, or
common labelled monoid inverse orbit is claimed.

English-first proof / hostile audit:
  docs/track_e_monotone_seed_growth_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A finite, actual Kpt-source certificate that something genuinely
NEW occurs at cut. The first case retains an active terminal
source node, the second an active node whose SAME old/upper full
L+ ancestors yield a crossing absent from the smaller closure.

The complete old Kpt source is explicit; no fake E or selected
graph-shadow data are substituted. -/
def IndexedNewSourceCutWitness
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {Params : Type}
    (node : Params → AdmissibleKptNode family)
    (live : Nat → Params → Bool)
    (oldSource : Set (AdmissibleKptNode family))
    (cut : Nat) : Prop :=
  (∃ j : Params, live cut j = true ∧
    node j ∉ oldSource ∧ LevelTree.lev (node j) = cut) ∨
  (∃ j : Params, live cut j = true ∧
    ∃ T : PartialTypeWithE cut db du dd,
      ∃ U : PartialTypeWithE (cut+1) db du dd,
        kptFullOldAtCut (node j) cut =
          some (⟨cut,T⟩ : RawPartialTypeNode db du dd) ∧
        kptFullUpperAtCut (node j) cut =
          some (⟨cut+1,U⟩ : RawPartialTypeNode db du dd) ∧
        (T,U) ∉ FullPhysicalClosureCrossing family oldSource cut)

/-- A pair of genuine actual Kpt AlgorithmRuns at the SAME top,
with X⊆Y, have a FINITE-INDEXABLE physical new-source witness
at every cut selected only by the enlarged run.

No arbitrary witness index is postulated: hExact asserts literal
surjectivity of a given source-node index onto the FULL actual
larger pre-cut closure, and the theorem constructs its live
witness using the genuine new-cut theorem and the exact indexed
crossing/physical crossing equality.

The two source run maps and the finite index domains need not
be equal or isomorphic. -/
theorem new_selected_Kpt_cut_has_indexed_physical_witness
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y) (top cut : Nat)
    (RunX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (RunY : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y top)
    (hCut : cut < top)
    (hNew : cut ∈ RunY.I cut)
    (hOld : cut ∉ RunX.I cut)
    {Params : Type}
    (node : Params → AdmissibleKptNode family)
    (live : Nat → Params → Bool)
    (hExact : ∀ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
        (RunY.I (cut+1)) Y ↔
      ∃ j : Params, node j = z ∧ live cut j = true) :
    IndexedNewSourceCutWitness family node live
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (RunX.I (cut+1)) X) cut := by
  let ZX : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (RunX.I (cut+1)) X
  let ZY : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (RunY.I (cut+1)) Y
  have hNovel :=
    new_selected_Kpt_cut_has_new_terminal_or_full_crossing
      family X Y hXY top cut RunX RunY hCut hNew hOld
  change (∃ z : AdmissibleKptNode family,
      z ∈ ZY ∧ z ∉ ZX ∧ LevelTree.lev z = cut) ∨
    (∃ p : PartialTypeWithE cut db du dd ×
        PartialTypeWithE (cut+1) db du dd,
      p ∈ FullPhysicalClosureCrossing family ZY cut ∧
      p ∉ FullPhysicalClosureCrossing family ZX cut) at hNovel
  rcases hNovel with ⟨z,hZ,hAbsent,hLevel⟩ | ⟨p,hNewPair,hAbsent⟩
  · obtain ⟨j,hNode,hLive⟩ := (hExact z).mp hZ
    left
    refine ⟨j,hLive,?_,?_⟩
    · simpa only [hNode] using hAbsent
    · simpa only [hNode] using hLevel
  · have hSourceEq :=
      indexed_physical_crossing_eq_full_closure_relation
        family node live ZY cut hExact
    have hPairIndexed :
        p ∈ IndexedPhysicalCrossing family node live cut := by
      rw [hSourceEq]
      exact hNewPair
    obtain ⟨j,hLive,hOldRaw,hUpperRaw⟩ := hPairIndexed
    right
    exact ⟨j,hLive,p.1,p.2,hOldRaw,hUpperRaw,hAbsent⟩

/-- The physical finite numerical-H+ new-run version CONSTRUCTS
the complete finite Kpt source universe and exact live Boolean
mask from the true AlgorithmRun and its ACTUAL original-prefix
representation. No finite source enumeration is assumed.

For two same-horizon runs over X⊆Y, the NEW run must be
represented by a genuine finite physical H+ source pool. Every
extra selected cut then has an active, finite-index witness:
new terminal Kpt source or new full dependent L+ crossing pair.

A separate new-root stage can feed this theorem through Track C's
physically verified source-construction/avoidance hypotheses.
This theorem does NOT infer such a stage exists from the diary. -/
theorem finiteNumericH_actual_extra_cut_has_finite_source_witness
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (originalPool : Set (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid originalPool)
    (top cut : Nat)
    (RunX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (RunY : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y top)
    (hCut : cut < top)
    (hNew : cut ∈ RunY.I cut)
    (hOld : cut ∉ RunX.I cut) :
    ∃ params : Finset (AdmissibleKptNode family),
      ∃ live : Nat → Fin params.card → Bool,
        (∀ z : AdmissibleKptNode family,
          z ∈ params ↔
          z ∈ SMTree.Envelope.closure
            (admissibleKptSTree family) (RunY.I 0) Y) ∧
        IndexedNewSourceCutWitness family
          (fun j : Fin params.card =>
            (params.equivFin.symm j).val)
          live
          (SMTree.Envelope.closure (admissibleKptSTree family)
            (RunX.I (cut+1)) X) cut := by
  classical
  obtain ⟨params,live,hParams,_hInjective,_hPresent,hCover⟩ :=
    finiteNumericH_actualRun_uniform_exhaustive_source_index
      family K k N hAvoid originalPool Y hY top RunY
  refine ⟨params,live,hParams,?_⟩
  exact new_selected_Kpt_cut_has_indexed_physical_witness
    family X Y hXY top cut RunX RunY hCut hNew hOld
    (fun j : Fin params.card => (params.equivFin.symm j).val)
    live (hCover cut hCut)

end Kk
