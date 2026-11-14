import Kk.B3ActualRunFullSourceCertification
import Kk.B3SameBaseOldSocle
import Kk.B3IndexedPhysicalCutStar
import Mathlib.Tactic

/-!
# Track B — compare TWO genuine finite Henson AlgorithmRuns by indexed cut-star

English proof and hostile audit PRECEDE this Lean module:
  docs/track_b_two_actual_runs_english_audit.md

The two actual AlgorithmRuns may have unrelated original-prefix seed
sets, different finite Henson truncation heights and distinct full
meet-and-parameter-closed Kpt sources. The same literal base E, k
and source-coordinate cut are SHARED parameters. Each true run's
full-source name exhaustiveness and finite active-node index are
DERIVED from its own true original-prefix seed invariant.

The only inter-run B3 comparison input is equality of their
intrinsic PHYSICAL cut-star complete upper ordinary-L spectra
(or the equivalent finite active-index projections). No equality
of selected diary F-states, full dependent L+ source orbits,
event-indexed E records or unbounded resolved diary is inferred.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- One REAL finite numerical-Henson AlgorithmRun at one common
SOURCE cut, over globally shared base E and generation k.

This record cannot be constructed from an arbitrary represented
subpool: X must have actual original-prefix seeds, the selected
levels come from an actual AlgorithmRun, and no-I2 is imposed on
the precise complete pre-cut closure at Run.I (cut+1). -/
structure HensonRunCutData
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (cut : Nat) where
  N : Nat
  U : Finset (Fin N)
  hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
    bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L
  X : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell))
  hX : X ⊆ ambientPrefixPool
    (hensonForbiddenFamily ell hell)
    (finiteNumericH (normalizedGraphModel E) k N)
    hAvoid (U : Set (Fin N))
  top : Nat
  run : SMTree.Envelope.AlgorithmRun
    (normalizedKptSMTree (hensonForbiddenFamily ell hell)) X top
  hCut : cut < N
  hBelow : cut < top
  hNoI2 : ¬ ∃ a : AdmissibleKptNode (hensonForbiddenFamily ell hell),
    a ∈ SMTree.Envelope.closure
      (admissibleKptSTree (hensonForbiddenFamily ell hell))
      (run.I (cut+1)) X ∧
    ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      b ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (run.I (cut+1)) X ∧
      SMTree.Envelope.SameComponent a b ∧
      LevelTree.lev (LevelTree.meet a b) = cut

namespace HensonRunCutData

variable
    {ell : Nat} {hell : 2 ≤ ell}
    {k : Nat} {hK : ell ≤ k+1}
    {E : Nat → Nat → Bool}
    {hLoops : ∀ i, E i i = false}
    {hSym : ∀ x y, E x y = E y x}
    {hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true)}
    {cut : Nat}

/-- Construct one genuinely FULL HensonCutOccurrence from its actual
numerical-H AlgorithmRun, using its own selected original-name pool,
complete closure and no-I2 certificate; NOT a fake labelled subpool. -/
noncomputable abbrev occurrence
    (P : HensonRunCutData ell hell k hK E hLoops hSym hClique cut) :
    HensonCutOccurrence ell cut hell :=
  actualHensonRunCutOccurrence
    ell hell k hK E hLoops hSym hClique
    P.N P.U P.hAvoid P.X P.top P.run cut P.hCut P.hNoI2

/-- At one REAL run, both previously missing source-completeness
conditions are DERIVED: every selected Full name is exactly an
actual closure crossing, and every Kpt node in the true pre-cut
closure is below a maintained physical original.

No separate one-sided hRepresented or arbitrary hPool is assumed. -/
theorem occurrence_full_source_exhaustive
    (P : HensonRunCutData ell hell k hK E hLoops hSym hClique cut) :
    (∀ v : Fin P.occurrence.M,
      P.occurrence.Full v ↔
        closureSelectedOriginal (hensonForbiddenFamily ell hell)
          P.occurrence.ambient P.occurrence.hAvoid
          P.occurrence.original P.occurrence.Z cut v) ∧
    (∀ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      z ∈ P.occurrence.Z →
        ∃ v : Fin P.occurrence.M,
          z ≤ P.occurrence.ambient.kptOriginal
            (hensonForbiddenFamily ell hell)
            P.occurrence.hAvoid (P.occurrence.original v)) := by
  constructor
  · exact actualHensonRunCutOccurrence_fullExact
      ell hell k hK E hLoops hSym hClique
      P.N P.U P.hAvoid P.X P.top P.run
      cut P.hCut P.hNoI2
  · exact actualHensonRunCutOccurrence_poolExhaustive
      ell hell k hK E hLoops hSym hClique
      P.N P.U P.hAvoid P.X P.hX P.top P.run
      cut P.hCut P.hBelow P.hNoI2

/-- Two ACTUAL physical finite numerical-Henson AlgorithmRuns over
one literal base E and generation k, at the SAME source-coordinate
cut, agree on FULL corrected (B3) whenever their INTRINSIC
positive-cut complete upper ordinary-L spectra agree.

The actual full name predicates and original-pool exhaustiveness,
and the old complete ordinary-L prefix alignment are DERIVED
from the run data and same base E/k. Different X, U, N, top,
actual closure sets, active Kpt indexes and monoid choices remain
permitted. This does NOT prove that a refined diary gives hSpectrum. -/
theorem two_runs_full_B3_iff_of_intrinsic_spectra
    (P Q : HensonRunCutData ell hell k hK E hLoops hSym hClique cut)
    (hSpectrum : ∀ R : RelationalPrefixType (cut+1) 1 0 1,
      PhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
        P.occurrence.Z cut R ↔
      PhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
        Q.occurrence.Z cut R) :
    P.occurrence.fullProfile.CorrectedB3
      (hensonForbiddenFamily ell hell) ↔
    Q.occurrence.fullProfile.CorrectedB3
      (hensonForbiddenFamily ell hell) := by
  obtain ⟨hNamesP,hPoolP⟩ := occurrence_full_source_exhaustive P
  obtain ⟨hNamesQ,hPoolQ⟩ := occurrence_full_source_exhaustive Q
  exact HensonCutOccurrence.full_B3_iff_same_base_intrinsic_cutStar
    P.occurrence Q.occurrence rfl rfl
    hNamesP hPoolP hNamesQ hPoolQ hSpectrum

/-- For TWO genuine finite AlgorithmRuns over the same base E/k and
source cut, construct TWO independently exhaustive FINITE actual Kpt
node indexes with exact per-cut live masks. If their projected
complete upper ordinary-L cut-star profiles agree at this cut,
the FULL corrected (B3) tests agree.

The finite index types may have DIFFERENT cardinalities and contain
generated parameters/meets as well as original seeds. Indexed
projection equality is the sole cross-run B3-specific premise;
we do NOT infer it from the proposed diary's selected graph-age F. -/
theorem two_runs_finite_indexed_cutStar_controls_full_B3
    (P Q : HensonRunCutData ell hell k hK E hLoops hSym hClique cut) :
    ∃ paramsP : Finset (AdmissibleKptNode (hensonForbiddenFamily ell hell)),
      ∃ liveP : Nat → Fin paramsP.card → Bool,
      ∃ paramsQ : Finset (AdmissibleKptNode (hensonForbiddenFamily ell hell)),
      ∃ liveQ : Nat → Fin paramsQ.card → Bool,
        (∀ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
          z ∈ paramsP ↔
            z ∈ SMTree.Envelope.closure
              (admissibleKptSTree (hensonForbiddenFamily ell hell))
                (P.run.I 0) P.X) ∧
        (∀ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
          z ∈ paramsQ ↔
            z ∈ SMTree.Envelope.closure
              (admissibleKptSTree (hensonForbiddenFamily ell hell))
                (Q.run.I 0) Q.X) ∧
        (∀ R : RelationalPrefixType (cut+1) 1 0 1,
          IndexedPhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
            (fun j : Fin paramsP.card => (paramsP.equivFin.symm j).val)
            liveP cut R ↔
          PhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
            P.occurrence.Z cut R) ∧
        (∀ R : RelationalPrefixType (cut+1) 1 0 1,
          IndexedPhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
            (fun j : Fin paramsQ.card => (paramsQ.equivFin.symm j).val)
            liveQ cut R ↔
          PhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
            Q.occurrence.Z cut R) ∧
        ((∀ R : RelationalPrefixType (cut+1) 1 0 1,
          IndexedPhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
            (fun j : Fin paramsP.card => (paramsP.equivFin.symm j).val)
            liveP cut R ↔
          IndexedPhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
            (fun j : Fin paramsQ.card => (paramsQ.equivFin.symm j).val)
            liveQ cut R) →
          (P.occurrence.fullProfile.CorrectedB3
             (hensonForbiddenFamily ell hell) ↔
           Q.occurrence.fullProfile.CorrectedB3
             (hensonForbiddenFamily ell hell))) := by
  classical
  let family := hensonForbiddenFamily ell hell
  let K : AgeTestModel 1 0 1 := normalizedGraphModel E
  obtain ⟨paramsP,liveP,hParamsP,hCutsP⟩ :=
    numericH_actual_run_all_cuts_indexed_cutStar
      family K k P.N P.hAvoid
      (P.U : Set (Fin P.N)) P.X P.hX P.top P.run
  obtain ⟨paramsQ,liveQ,hParamsQ,hCutsQ⟩ :=
    numericH_actual_run_all_cuts_indexed_cutStar
      family K k Q.N Q.hAvoid
      (Q.U : Set (Fin Q.N)) Q.X Q.hX Q.top Q.run
  refine ⟨paramsP,liveP,paramsQ,liveQ,
    hParamsP,hParamsQ,?_,?_,?_⟩
  · intro R
    exact hCutsP cut P.hBelow R
  · intro R
    exact hCutsQ cut Q.hBelow R
  · intro hProjected
    apply two_runs_full_B3_iff_of_intrinsic_spectra P Q
    intro R
    exact (hCutsP cut P.hBelow R).symm.trans
      ((hProjected R).trans (hCutsQ cut Q.hBelow R))

end HensonRunCutData

#print axioms Kk.HensonRunCutData.occurrence_full_source_exhaustive
#print axioms Kk.HensonRunCutData.two_runs_full_B3_iff_of_intrinsic_spectra
#print axioms Kk.HensonRunCutData.two_runs_finite_indexed_cutStar_controls_full_B3

end Kk
