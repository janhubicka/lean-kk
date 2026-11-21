import Kk.TrackEOldSocleOriginalMaxFrontier
import Kk.TrackEOneBareRootEvenRealNoNovelty
import Kk.TrackGBoringOnlyNoNoveltyRunTransfer
import Mathlib.Tactic

/-!
# Track E E80: synchronized Kpt run from maximal old-socle tests

English-first proof and 24 hostile adversarial cases:
docs/track_e_partitioned_max_old_socle_whole_run_english_audit_20261121.md

At allowed OLD-BORING positive even-real zero-column cuts, E79 turns
ONE maximal genuine complete OLD Kpt prefix match per active physical
original into ALL lower-cut original-prefix witnesses. E77 then
automatically rules out both seed and generated I1 terminals and
matches each complete upper L+/E crossing pair.

All OTHER old-boring cut classes remain explicit physical no-novelty
hypotheses. G365 constructs an ACTUAL new AlgorithmRun preserving
LITERALLY the old selected-level function I and entire monoid
map function F. No pre-existing Y-run, selected graph-age shadow,
auxiliary Kpt source enumeration, uniform diary carrier or global
BRD is assumed or derived.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A physical source cut is positively EVEN REAL and has the
genuine ZERO ordinary-L star on EVERY eligible original in the
true old-run selected stage pool. This is stronger than a zero
column restricted to selected-front/marked coding originals.

The definition does not assert that any cut of the actual resolved
diary satisfies the condition. -/
def KptActualPositiveEvenRealZeroStage
    (family : List (NormalizedForbidden 1 0 1))
    (E : Nat → Nat → Bool) (k N : Nat)
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (cut : Nat) : Prop :=
  ∃ idx g : Nat,
    cut = hPosition k idx g ∧
    0 < cut ∧
    (∀ v : Fin N,
      v ∈ hStageOriginals (normalizedGraphModel E) k N U
        (R.I (cut+1)) →
      cut+1 ≤ (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val →
      (finiteNumericH (normalizedGraphModel E) k N).L.binary
        cut v.val (0 : Fin 1) = false)

/-- E79 plus E77: one old-boring Allowed cut becomes PHYSICALLY
quiet using only one highest-cut complete old Kpt prefix witness
per physical original and the full zero-stage geometry.

The new initial seed set is exactly X ∪ {ONE actual original}.
The old X may contain legitimate dependent Kpt seeds. E76/E77
derive the no-initial-seed and no-generated-I1 obligations.
No new run occurs in any hypothesis. -/
theorem finiteNumericH_old_boring_allowed_zero_stage_quiet_of_original_max
    (family : List (NormalizedForbidden 1 0 1))
    (E : Nat → Nat → Bool)
    (hGraphSym : ∀ i j, E i j = E j i)
    (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family
      (finiteNumericH (normalizedGraphModel E) k N)
      hAvoid (U : Set (Fin N)))
    (newV : Fin N) (hNewInU : newV ∈ U)
    (hBare : Y = X ∪
      ({(finiteNumericH (normalizedGraphModel E) k N).kptOriginal family hAvoid newV} :
        Set (AdmissibleKptNode family)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (Allowed : Set Nat)
    (hMax : ∀ v : Fin N,
      ∀ (hNonempty :
        (kpt_actual_original_socle_allowed_cuts
          family (normalizedGraphModel E) k N
          hAvoid U X Y top R Allowed v).Nonempty),
      KptActualOldSocleCoveredAt family X top R
        ((finiteNumericH (normalizedGraphModel E) k N).kptOriginal family hAvoid v)
        ((kpt_actual_original_socle_allowed_cuts
          family (normalizedGraphModel E) k N
          hAvoid U X Y top R Allowed v).max' hNonempty))
    (cut : Nat)
    (hCut : cut < top)
    (hAllowed : cut ∈ Allowed)
    (hBoring : ¬ SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family)
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X) cut)
    (hZero : KptActualPositiveEvenRealZeroStage
      family E k N U X top R cut) :
    NewRootNoNoveltyAtCut family
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X)
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y) cut := by
  obtain ⟨idx,g,hReal,hPos,hZeroStage⟩ := hZero
  have hOriginalPrefix :
      KptCandidateOriginalOldPrefixCovered
        family (normalizedGraphModel E) k N
        hAvoid U X Y top R cut := by
    intro v hStage hRep
    have hSocle : KptActualOldSocleCoveredAt family X top R
        ((finiteNumericH (normalizedGraphModel E) k N).kptOriginal family hAvoid v)
        cut :=
      kpt_actual_original_socle_covered_of_all_allowed_max
        family (normalizedGraphModel E) k N hAvoid
        U X Y top R Allowed hMax v cut
        hCut hAllowed hBoring hStage hRep
    exact hSocle
  exact finiteNumericH_old_boring_one_bare_root_even_real_noNovelty
    family E hGraphSym k N hAvoid
    U X Y hX newV hNewInU hBare top R
    cut idx g hReal hPos hCut hBoring
    hZeroStage hOriginalPrefix

/-- E80: ACTUALLY CONSTRUCT a genuine synchronized Y-run with the
same selected-level function I and ENTIRE monoid-valued function F
from one OLD AlgorithmRun R on X and physically exact certificates.

At every Allowed cut below top the full stage is positive even-real
and has ZERO ordinary-L columns; E79 supplies every old-Kpt prefix
from one maximal test per ACTUAL physical original. Other genuine
old-boring cuts are explicitly required quiet -- including odd/fake,
nonzero or K4 E/q2 microevents when they are not in Allowed.

This is a conditional FINITE-stage run construction, NOT a proof
that the canonical resolved-Q diary supplies the certificates,
that N is diary-uniform or that labelled inverse-source orbits
or big Ramsey degrees have been characterized. -/
theorem finiteNumericH_one_bare_root_run_of_partitioned_original_max
    (family : List (NormalizedForbidden 1 0 1))
    (E : Nat → Nat → Bool)
    (hGraphSym : ∀ i j, E i j = E j i)
    (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family
      (finiteNumericH (normalizedGraphModel E) k N)
      hAvoid (U : Set (Fin N)))
    (newV : Fin N) (hNewInU : newV ∈ U)
    (hBare : Y = X ∪
      ({(finiteNumericH (normalizedGraphModel E) k N).kptOriginal family hAvoid newV} :
        Set (AdmissibleKptNode family)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (Allowed : Set Nat)
    (hAllowedZero : ∀ cut : Nat, cut < top → cut ∈ Allowed →
      KptActualPositiveEvenRealZeroStage family E k N
        U X top R cut)
    (hMax : ∀ v : Fin N,
      ∀ (hNonempty :
        (kpt_actual_original_socle_allowed_cuts
          family (normalizedGraphModel E) k N
          hAvoid U X Y top R Allowed v).Nonempty),
      KptActualOldSocleCoveredAt family X top R
        ((finiteNumericH (normalizedGraphModel E) k N).kptOriginal family hAvoid v)
        ((kpt_actual_original_socle_allowed_cuts
          family (normalizedGraphModel E) k N
          hAvoid U X Y top R Allowed v).max' hNonempty))
    (hOtherQuiet : ∀ cut : Nat, cut < top → cut ∉ Allowed →
      ¬ SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family)
        (SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) X) cut →
      NewRootNoNoveltyAtCut family
        (SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) X)
        (SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) Y)
        cut) :
    ∃ RY : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family) Y top,
      RY.I = R.I ∧ RY.F = R.F := by
  have hXY : X ⊆ Y := by
    rw [hBare]
    intro z hz
    exact Or.inl hz
  apply kpt_transport_actualRun_of_boring_only_noNovelty
    family X Y hXY top R
  intro cut hCut hBoring
  by_cases hAllowed : cut ∈ Allowed
  · exact finiteNumericH_old_boring_allowed_zero_stage_quiet_of_original_max
      family E hGraphSym k N hAvoid U X Y
      hX newV hNewInU hBare top R Allowed hMax
      cut hCut hAllowed hBoring (hAllowedZero cut hCut hAllowed)
  · exact hOtherQuiet cut hCut hAllowed hBoring

end Kk
