import Kk.B3UnmarkedInsideSameCore
import Kk.B3ActualI3PhysicalCore
import Mathlib.Tactic

/-!
# Track D: TRUE nonstructural I3 has one omitted physical name IN its clique

The checked successor-tree actual-run I3 theorem gives failed FULL
corrected B3 of the genuine pre-cut closure. Track D's complete
actual-run physical-core iff identifies that entire source, not an
arbitrary represented subpool. The stacked missing-unmarked-same-core
lemma now shows that IF a genuinely represented B3-good Marked source
is provided, a chosen upper vertex of ONE offending forbidden clique
has an actual FULL-selected and UNMARKED physical name, preserving its
complete next-cut L type and cut eligibility.

English-first proof and 15 hostile checks:
docs/audits/2026-11-14-track-d-actual-i3-unmarked-same-clique-english.md

It does NOT identify marked sources with selected active diary branches,
or prove selected-front graph-age loss or a common labelled orbit.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The precise SAME-clique genuinely unmarked physical original
certificate, relative to one physical HensonCutOccurrence P and
one represented B3-good Marked source.

All future vertices in the L-only witness lie in the ONE
forbidden clique. The unmarked name is a true cut-neighbour
in P's actual complete physical original pool and its whole
next-cut directed L type is absent from CHOSEN marked outputs. -/
def HensonCutOccurrence.HasUnmarkedMissingSameCliqueCore
    {ell cut : Nat} {hell : 2 ≤ ell}
    (P : HensonCutOccurrence ell cut hell)
    (Marked : Fin P.M → Prop) : Prop :=
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
            ((P.ambient.partialTypeAt (cut+1) (P.original v).val).lReduct))

/-- In a genuine selected positive nonstructural I3 event of ONE
finite Henson AlgorithmRun, with full (I1)/(I2) obstructions
excluded in its complete pre-cut closure, any genuinely
represented, nonempty, B3-good marked source omits a real
full-source physical cut-neighbour INSIDE the same forbidden
clique certifying the actual full B3 failure.

The missing name may be an auxiliary parameter. This is NOT
a selected-front age-loss theorem. -/
theorem henson_actualRun_I3_good_marked_has_unmarked_inside_same_clique
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
      P.HasUnmarkedMissingSameCliqueCore Marked := by
  classical
  intro P Marked hRepresented hMarkedWitness hMarkedGood
  obtain ⟨w,hw,hFree⟩ := hMarkedWitness
  have hPhysical :
      HensonPhysicalCutStarBadCore
        ell hell P.k P.N cut P.M P.E P.original P.Full :=
    henson_actualRun_nonstructural_I3_has_exact_physical_core
      ell hell k hK E hLoops hSym hClique
      N U hAvoidA X hX top Run hTop
      cut hPos hBelow hCut hSelected hNoI1 hNoI2
  have hRunFull :=
    henson_actualRun_complete_fullB3_failure_iff_physical_bad_core
      ell hell k hK E hLoops hSym hClique
      N U hAvoidA X hX top Run cut hCut hBelow hNoI2
  have hFullFailure :
      ¬ P.fullProfile.CorrectedB3 (hensonForbiddenFamily ell hell) :=
    hRunFull.2.2.mpr hPhysical
  have hUnmarked :=
    henson_failed_fullB3_good_marked_has_unmarked_inside_same_core_of_noI2
      ell hell P.k P.hK P.E P.hLoops P.hSym P.hClique
      P.N cut P.M P.hCut P.original P.Full Marked
      P.hAvoid P.Z hRepresented P.hNoI2
      w hw hFree hFullFailure hMarkedGood
  exact hUnmarked

#print axioms henson_actualRun_I3_good_marked_has_unmarked_inside_same_clique

end Kk
