import Kk.TrackEIsolatedDummyOriginalMaxWholeRun
import Kk.TrackEOddSafeSourceNoNovelty
import Kk.TrackEOldSocleOriginalMaxFrontier
import Kk.TrackGBoringOnlyNoNoveltyRunTransfer
import Mathlib.Tactic

/-!
# Track E E84: ONE maximal OLD Kpt source-prefix test per original,
# covering two distinct safe physical numerical-H+ source cut classes

English FIRST and 24 adversarial checks:
docs/track_e_two_safe_cut_classes_whole_run_english_audit_20261121.md

Allowed OLD-BORING cuts are either:
(D) genuine positive lower-real source positions of ISOLATED
    original-Q dummy bases; E81 supplies zero ordinary-L there;
(O) genuine ODD numerical H+ source cuts with NO ACTUAL stage
    original ending its canonical auxiliary E-free level there;
    E83 proves full physical no-novelty using zero ordinary-L,
    no initial seed, no generated I1 and full old Kpt socles.

E79's SINGLE maximal complete OLD Kpt-prefix witness per actual
physical original is computed over the UNION of both allowed
classes -- not one maximum per class. All other old-boring cuts
remain explicit physical quietness hypotheses. Verified G365
then CONSTRUCTS a genuine new AlgorithmRun of exactly the same
I and entire monoid-valued F. No already existing new run,
diary-uniform carrier, cross-occurrence labelled orbit or
BRD theorem is assumed or proved.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A genuine ODD source cut with NO physical stage original
having its canonical auxiliary E-free level terminate there.

This is essential: arbitrary odd cuts may be genuinely selected
because a dependent positive E-parameter ends at the cut.
The stage is the TRUE old-run tail R.I(cut+1), not a diary
selected-original shadow. -/
def KptActualOddNoStageFreeEndCut
    (family : List (NormalizedForbidden 1 0 1))
    (E : Nat → Nat → Bool) (k N : Nat)
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (cut : Nat) : Prop :=
  ∃ a : Nat,
    cut = 2*a+1 ∧
    (∀ v : Fin N,
      v ∈ ambientStagePool
        (finiteNumericH (normalizedGraphModel E) k N)
        (U : Set (Fin N)) (R.I (cut+1)) →
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val
        ≠ cut)

/-- Exact source-cut union class for E84. It does NOT cover all
old-boring, odd/fake or auxiliary Kpt physical source cuts.
Outside-Allowed physical no-novelty remains explicit. -/
def KptActualTwoSafeSourceCut
    (family : List (NormalizedForbidden 1 0 1))
    (E : Nat → Nat → Bool) (k N : Nat)
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (cut : Nat) : Prop :=
  KptActualIsolatedDummyLowerCut E k N cut ∨
    KptActualOddNoStageFreeEndCut family E k N U X top R cut

/-- At ONE old-boring cut in the UNION of the two true safe
physical classes, E79 transfers one maximal complete OLD
source-prefix witness for each active original to the cut.

The DUMMY class uses E82/E77 zero-column real no-novelty;
the ODD class uses E83's necessary no-stage-E-free-end
criterion to exclude all genuine generated I1 parameters
while E72 transports complete dependent upper L+/E pairs.

There is NO old-prefix duplication for the two classes:
the same hMax predicate refers to ALL eligible Allowed cuts.
No pre-existing Y AlgorithmRun and no selected-L shadow. -/
theorem finiteNumericH_old_boring_two_safe_cut_quiet_of_original_max
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
    (cut : Nat) (hCut : cut < top)
    (hAllowed : cut ∈ Allowed)
    (hBoring : ¬ SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family)
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X) cut)
    (hSafe : KptActualTwoSafeSourceCut
      family E k N U X top R cut) :
    NewRootNoNoveltyAtCut family
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X)
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y) cut := by
  have hOldPrefix :
      KptCandidateOriginalOldPrefixCovered
        family (normalizedGraphModel E) k N
        hAvoid U X Y top R cut := by
    intro v hStage hRep
    exact kpt_actual_original_socle_covered_of_all_allowed_max
      family (normalizedGraphModel E) k N hAvoid
      U X Y top R Allowed hMax v cut
      hCut hAllowed hBoring hStage hRep
  rcases hSafe with hDummy | hOdd
  · have hZero : KptActualPositiveEvenRealZeroStage
        family E k N U X top R cut :=
      kpt_actual_isolated_dummy_cut_has_full_zero_original_stage
        family E k N U X top R cut hDummy
    exact finiteNumericH_old_boring_allowed_zero_stage_quiet_of_original_max
      family E hGraphSym k N hAvoid U X Y
      hX newV hNewInU hBare top R Allowed hMax
      cut hCut hAllowed hBoring hZero
  · obtain ⟨a,hReal,hNoStageEnd⟩ := hOdd
    subst cut
    exact finiteNumericH_old_boring_one_bare_root_odd_noNovelty
      family E hGraphSym k N hAvoid U X Y
      hX newV hNewInU hBare top R a
      hBoring hNoStageEnd hOldPrefix

/-- E84: from ONE maximal complete OLD Kpt-prefix certificate
per physical original across TWO safe source-cut classes, and
explicit physical no-novelty on all other genuinely old-boring
cuts, ACTUALLY CONSTRUCT the synchronized enlarged Kpt AlgorithmRun
with exactly the old selected-level function and TOTAL F map.

Allowed is arbitrary and may be disconnected/interleaved between
isolated-DUMMY lower real and safe ODD no-E-free-end cuts.
The E79 max is computed over the UNION, not separately per class.

This does NOT show original-prefix witnesses exist in the
actual resolved-Q/Henson diary; all other old-boring source
classes remain explicit. No uniform N, source-orbit or BRD. -/
theorem finiteNumericH_one_bare_root_run_of_two_safe_classes_original_max
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
    (hAllowedSafe : ∀ cut : Nat, cut < top → cut ∈ Allowed →
      KptActualTwoSafeSourceCut family E k N U X top R cut)
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
  · exact finiteNumericH_old_boring_two_safe_cut_quiet_of_original_max
      family E hGraphSym k N hAvoid U X Y
      hX newV hNewInU hBare top R Allowed hMax
      cut hCut hAllowed hBoring
      (hAllowedSafe cut hCut hAllowed)
  · exact hOtherQuiet cut hCut hAllowed hBoring

end Kk
