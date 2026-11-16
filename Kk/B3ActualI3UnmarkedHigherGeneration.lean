import Kk.B3ActualI3UnmarkedSameClique
import Kk.ActualRunStructuralOrLowerReal
import Kk.PhysicalLowerRealCutNeighbour
import Mathlib.Tactic

/-!
# Track D: an omitted HIGHER-generation physical original in the SAME I3 clique

English proof and 18 hostile checks were committed BEFORE Lean:
docs/audits/2026-11-16-track-d-unmarked-higher-generation-same-clique-english.md

A true finite Henson AlgorithmRun's positive selected nonstructural (I3)
cut is at a real generation g<k. If a genuinely represented, nonempty
and corrected-B3-good marked source is provided, one upper vertex in ONE
forbidden L-only clique has an actual FULL, unmarked, cut-eligible,
positively cut-adjacent physical original name, with its COMPLETE next-L
type absent from the marked CHOSEN outputs. This SAME original is a
LATER base j>idx at a STRICTLY HIGHER generation m>g, with
E(idx,j)=true in the actual base graph.

No auxiliary E is assigned to the arbitrary L-only forbidden-clique
witness. This is a necessary one-run I3 obstruction, not a general
selected-front graph-age-loss bridge or common labelled inverse orbit.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

namespace HensonCutOccurrence

/-- A refinement of HasUnmarkedMissingSameCliqueCore that places
the SAME omitted physical full source name on a strictly later BASE
and strictly higher numeric generation than the tested real cut.

We keep the original bounded clique, same ordinary-L lower socle,
cut-deletion avoidance, cut vertex, same-clique future-vertex coverage,
FULL selected original name, physical free eligibility, positive
physical cut edge, COMPLETE next-cut L type, and its ABSENCE from
actually chosen marked outputs. There is no graph-age projection. -/
def HasUnmarkedHigherGenerationSameCliqueCore
    {ell cut : Nat} {hell : 2 ≤ ell}
    (P : HensonCutOccurrence ell cut hell)
    (Marked : Fin P.M → Prop)
    (g idx : Nat) : Prop :=
  ∃ (V : AgeTestModel 1 0 1) (e : Fin ell → Nat),
    V.BoundedCarrier ∧
    SameInitialL V P.ambient.L cut ∧
    (∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (V.withoutVertex cut)) ∧
    V.Realizes (cliquePattern ell) e ∧
    (∃ a : Fin ell, e a = cut) ∧
    (∀ x, x ∈ V.carrier → cut < x →
      ∃ a : Fin ell, e a = x) ∧
    (∃ a : Fin ell, cut < e a ∧
      ∃ v : Fin P.M,
        P.Full v ∧ ¬ Marked v ∧
        cut+1 ≤ P.ambient.freeLevel (P.original v).val ∧
        P.ambient.L.binary cut (P.original v).val (0 : Fin 1) = true ∧
        RelationalPrefixType.ofAgeModel V (cut+1) (e a) =
          RelationalPrefixType.ofAgeModel P.ambient.L
            (cut+1) (P.original v).val ∧
        ¬ (selectedStagePoolPrescribedData P.ambient cut
          P.original Marked).PrescribedUpperLType
            ((P.ambient.partialTypeAt (cut+1) (P.original v).val).lReduct) ∧
        ∃ j m : Nat, idx < j ∧ g < m ∧ m ≤ P.k ∧
          (P.original v).val = hPosition P.k j m ∧ P.E idx j = true)

end HensonCutOccurrence

/-- A genuine nonstructural selected (I3) cut of one actual finite
Henson AlgorithmRun, together with a represented cut-eligible B3-good
marked source, forces one missing SAME-CLIQUE chosen L-type witnessed
by an unmarked physical original in a LATER BASE and strictly HIGHER
NUMERICAL GENERATION than the physical cut.

The actual cut generation g<k is DERIVED, not assumed. Full actual
closure is computed at Run.I (cut+1); the fixed final original-name
universe is maintained at Run.I 0. The missing name can still be an
auxiliary generated Kpt parameter, not an active selected diary branch.

This does not prove the marked source is good for arbitrary diary
occurrences, nor that all such name omissions are impossible. -/
theorem henson_actualRun_I3_good_marked_has_unmarked_higher_same_clique
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N : Nat)
    (U : Finset (Fin N))
    (hAvoidA : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (X : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (hX : X ⊆ ambientPrefixPool
      (hensonForbiddenFamily ell hell)
      (finiteNumericH (normalizedGraphModel E) k N)
      hAvoidA (U : Set (Fin N)))
    (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell)) X top)
    (hTop : ∃ x ∈ X, LevelTree.lev x = top)
    (cut : Nat) (hPos : 0 < cut)
    (hBelow : cut < top) (hCut : cut < N)
    (hSelected : cut ∈ Run.I 0)
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (cut+1)) X ∧
      LevelTree.lev z = cut)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      a ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (cut+1)) X ∧
      ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        b ∈ SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily ell hell))
          (Run.I (cut+1)) X ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :
    let P := actualHensonRunCutOccurrence
      ell hell k hK E hLoops hSym hClique
      N U hAvoidA X top Run cut hCut hNoI2
    ∀ (Marked : Fin P.M → Prop),
      (∀ v : Fin P.M, Marked v →
        closureSelectedOriginal (hensonForbiddenFamily ell hell)
          P.ambient P.hAvoid P.original P.Z cut v) →
      (∃ w : Fin P.M,
        Marked w ∧ cut+1 ≤ P.ambient.freeLevel (P.original w).val) →
      (selectedStagePoolPrescribedData P.ambient cut
        P.original Marked).CorrectedB3 (hensonForbiddenFamily ell hell) →
      ∃ g idx : Nat, g < k ∧ cut = hPosition k idx g ∧
        P.HasUnmarkedHigherGenerationSameCliqueCore Marked g idx := by
  classical
  intro P Marked hRepresented hMarkedWitness hMarkedGood
  obtain ⟨g,idx,hg,hGen⟩ :=
    henson_actualRun_nonstructural_selected_has_lower_real_cut
      ell hell k hK E hLoops hSym hClique
      N U hAvoidA X hX top Run hTop
      cut hPos hBelow hCut hSelected hNoI1 hNoI2
  have hOld : P.HasUnmarkedMissingSameCliqueCore Marked :=
    henson_actualRun_I3_good_marked_has_unmarked_inside_same_clique
      ell hell k hK E hLoops hSym hClique
      N U hAvoidA X hX top Run hTop
      cut hPos hBelow hCut hSelected hNoI1 hNoI2
      Marked hRepresented hMarkedWitness hMarkedGood
  obtain ⟨V,e,hFinite,hSocle,hDelete,hCopy,hAt,hFuture,
      a,hAbove,v,hFull,hNotMarked,hFree,hPositive,hType,hNotType⟩ := hOld
  have hRealCut : hPosition k idx g < N := by
    rw [← hGen]
    exact hCut
  have hRealFree :
      hPosition k idx g + 1 ≤
        (finiteNumericH (normalizedGraphModel E) k N).freeLevel
          (P.original v).val := by
    change hPosition k idx g + 1 ≤
      P.ambient.freeLevel (P.original v).val
    rw [← hGen]
    exact hFree
  have hRealEdge :
      (finiteNumericHL (normalizedGraphModel E) k N).binary
        (hPosition k idx g) (P.original v).val (0 : Fin 1) = true := by
    change P.ambient.L.binary (hPosition k idx g)
      (P.original v).val (0 : Fin 1) = true
    rw [← hGen]
    exact hPositive
  have hHigher :
      ∃ j m : Nat, idx < j ∧ g < m ∧ m ≤ P.k ∧
        (P.original v).val = hPosition P.k j m ∧ P.E idx j = true := by
    exact finiteNumericH_eligible_lower_cut_neighbour_is_higher
      E k N idx g hg hRealCut (P.original v) hRealFree hRealEdge
  exact ⟨g,idx,hg,hGen,
    V,e,hFinite,hSocle,hDelete,hCopy,hAt,hFuture,
    a,hAbove,v,hFull,hNotMarked,hFree,hPositive,hType,hNotType,hHigher⟩

#print axioms henson_actualRun_I3_good_marked_has_unmarked_higher_same_clique

end Kk
