import Kk.TrackEPartitionedOriginalMaxWholeRun
import Kk.TrackEIsolatedDummyFullZeroStage
import Mathlib.Tactic

/-!
# Track E E82: genuine whole-run Kpt I/F from ISOLATED-Q dummy cut maxima

English-first proof and 20 hostile checks were committed BEFORE Lean:
docs/track_e_isolated_dummy_whole_run_original_max_english_audit_20261121.md

For genuine lower REAL H+ cuts at isolated original-Q bases,
merged E81 proves the complete ordinary L cut column is ZERO on
EVERY eligible physical original, without relying on the proposed
diary Plan or selected graph-age shadow.

Merged E80 then constructs a real new AlgorithmRun on the bare
old+ONE new original seed extension with EXACT SAME selected-level
function I and ENTIRE monoid-valued function F, assuming only one
maximal full OLD Kpt-prefix witness per active original at these
allowed cuts and explicit physical quietness at OTHER old-boring
cut classes. The required witnesses and other-cut quietness remain
genuinely open for the resolved-Q diary.

K4 q2/E microcuts are NOT silently treated as harmless.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A physically real lower-generation source cut c belongs to
an ACTUALLY isolated original-Q dummy base idx. The complete
origin graph E must have NO outward edges at that original base.

This cut class is deliberately more restrictive than arbitrary
old-boring, nonzero, odd/fake, or auxiliary Kpt source cuts. -/
def KptActualIsolatedDummyLowerCut
    (E : Nat → Nat → Bool)
    (k N : Nat) (cut : Nat) : Prop :=
  ∃ idx g : Nat,
    cut = hPosition k idx g ∧
    0 < cut ∧
    g < k ∧
    cut < N ∧
    (∀ j : Nat, E idx j = false)

/-- The EXACT isolated original-Q dummy condition eliminates
E80's zero-stage hypothesis at this source cut: all genuinely
eligible original coordinates in the complete original stage
have ordinary L(c,v)=0. No AlgorithmRun selected levels or
diary Plan invariants are used to prove the zero bit.

The old run is needed ONLY to name the true stage set R.I(c+1). -/
theorem kpt_actual_isolated_dummy_cut_has_full_zero_original_stage
    (family : List (NormalizedForbidden 1 0 1))
    (E : Nat → Nat → Bool)
    (k N : Nat) (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (cut : Nat)
    (hDummy : KptActualIsolatedDummyLowerCut E k N cut) :
    KptActualPositiveEvenRealZeroStage
      family E k N U X top R cut := by
  obtain ⟨idx,g,hReal,hPositive,hg,hCarrier,hIsolated⟩ := hDummy
  refine ⟨idx,g,hReal,hPositive,?_⟩
  subst cut
  exact finiteNumericH_isolated_base_full_stage_zero
    E k N idx g hg hCarrier hIsolated
    U (R.I (hPosition k idx g + 1))

/-- A GENUINE enlarged Kpt AlgorithmRun on a BARE physical new-root
seed family Y=X∪{Onew} exists with EXACT OLD I and TOTAL F,
where every Allowed old-range cut belongs to an ACTUALLY ISOLATED
original-Q dummy base at a positive lower real source position.

The numerical-H+ full ZERO ordinary-L column condition at all
Allowed cuts is now derived from the original-Q isolation via
E81, not assumed. E79's one maximal COMPLETE OLD Kpt-prefix
witness per physical original at eligible Allowed old-boring cuts
remains a real geometric premise. Every other old-boring cut is
explicitly required to satisfy full physical no-novelty.

No Y-run in the premises; no assumption that all source cuts
are dummy; no K4 microcut deletion, uniform diary carrier,
common labelled inverse-source orbit or sharp BRD follows. -/
theorem finiteNumericH_one_bare_root_run_of_isolated_dummy_original_max
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
    (hAllowedDummy : ∀ cut : Nat, cut < top → cut ∈ Allowed →
      KptActualIsolatedDummyLowerCut E k N cut)
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
  apply finiteNumericH_one_bare_root_run_of_partitioned_original_max
    family E hGraphSym k N hAvoid U X Y
    hX newV hNewInU hBare top R Allowed
  · intro cut hCut hAllowed
    exact kpt_actual_isolated_dummy_cut_has_full_zero_original_stage
      family E k N U X top R cut
      (hAllowedDummy cut hCut hAllowed)
  · exact hMax
  · exact hOtherQuiet

end Kk
