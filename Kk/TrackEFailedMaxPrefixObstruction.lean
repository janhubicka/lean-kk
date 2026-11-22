import Kk.TrackETwoSafeClassesOriginalMaxWholeRun
import Kk.TrackESelectedLevelOriginalBudget
import Mathlib.Tactic

/-!
# Track E E88: failure to synchronize a Kpt run forces an explicit
# maximal OLD Kpt-prefix defect or an outside-safe physical cut defect

English proof and 23 hostile checks committed FIRST:
docs/track_e_failed_original_or_offsafe_obstruction_english_audit_20261122.md

Merged E84 constructs an ACTUAL new AlgorithmRun with literally the
old selected I and TOTAL monoid-valued F from two full physical
source-exact certificate families: one maximal complete OLD Kpt
prefix witness per genuinely active physical original at the
Allowed isolated-dummy/safe-odd cuts, and actual full
NewRootNoNoveltyAtCut at every other OLD-BORING cut.

E88 takes the CONTRAPOSITIVE of this sufficient theorem:
  NO synchronized same-I/F run =>
    SOME maximal original old-prefix certificate fails, OR
    SOME outside-Allowed old-boring physical cut is not quiet.

The failed-original carrier is a TRUE Finset and has cardinal
at most U.card + the number of actually selected old levels
by merged E86. This is NOT a bound on bad CUTS, witness
existence, or common labelled source-orbit/BRD, and does not
assert the false converse that ANY missing prefix certificate
forces nonexistence of a synchronized run.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- One ACTUAL finite numerical-H+ physical original v fails
its E79 highest eligible OLD-Kpt prefix certificate.

The eligibility S_v is true OLD-BORING/new-live/full-Kpt-source
crossing support inside Allowed, and MUST be nonempty before
taking its max'. Failure means no old-live Kpt source has
the same literal complete OLD ancestor as original O_v;
the projection to ordinary-L graph ages is insufficient. -/
def KptActualFailedMaxOldSocleOriginal
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (Allowed : Set Nat) (v : Fin N) : Prop :=
  ∃ (hNonempty :
      (kpt_actual_original_socle_allowed_cuts
        family K k N hAvoid U X Y top R Allowed v).Nonempty),
    ¬ KptActualOldSocleCoveredAt family X top R
        ((finiteNumericH K k N).kptOriginal family hAvoid v)
        ((kpt_actual_original_socle_allowed_cuts
          family K k N hAvoid U X Y top R Allowed v).max' hNonempty)

/-- The ACTUAL finite set of physical original names whose
highest eligible old-boring Allowed source cut does NOT have
an old LIVE complete Kpt-prefix match.

This Finset of original names should never be confused with
a Finset of bad CUT coordinates or a diary-uniform source
orbit. No already existing Y AlgorithmRun is used here. -/
noncomputable def kpt_failed_max_old_socle_originals
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (Allowed : Set Nat) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun v =>
    KptActualFailedMaxOldSocleOriginal
      family K k N hAvoid U X Y top R Allowed v)

/-- Exact finite failed ORIGINAL membership, with no phantom
test when the eligible source cut set is empty. -/
theorem mem_kpt_failed_max_old_socle_originals
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (Allowed : Set Nat) (v : Fin N) :
    v ∈ kpt_failed_max_old_socle_originals
      family K k N hAvoid U X Y top R Allowed ↔
    KptActualFailedMaxOldSocleOriginal
      family K k N hAvoid U X Y top R Allowed v := by
  classical
  simp only [kpt_failed_max_old_socle_originals,
    Finset.mem_filter, Finset.mem_univ, true_and]

/-- Failed maximal Kpt old-prefix ORIGINAL names are genuinely
among the E85/E86 physical original NAMES needing at least
one test. No extra phantom original or empty S_v can fail. -/
theorem kpt_failed_max_old_socle_originals_subset_needed
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (Allowed : Set Nat) :
    kpt_failed_max_old_socle_originals
      family K k N hAvoid U X Y top R Allowed ⊆
    kpt_originals_needing_max_old_socle_test
      family K k N hAvoid U X Y top R Allowed := by
  classical
  intro v hv
  have hBad :=
    (mem_kpt_failed_max_old_socle_originals
      family K k N hAvoid U X Y top R Allowed v).mp hv
  obtain ⟨hNonempty,_⟩ := hBad
  exact (mem_kpt_originals_needing_max_old_socle_test
    family K k N hAvoid U X Y top R Allowed v).mpr hNonempty

/-- Quantitative E88: there are at most |U| + number of selected
OLD source levels different PHYSICAL ORIGINAL names witnessing
a failing highest complete old-Kpt-prefix test.

This does NOT bound the number of physical bad cuts or intervals
carried by these originals; G474 has the same distinction.
The maximal tests still need actual proof in the resolved diary. -/
theorem kpt_failed_max_old_socle_originals_card_le_root_add_selected
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (Allowed : Set Nat) :
    (kpt_failed_max_old_socle_originals
      family K k N hAvoid U X Y top R Allowed).card ≤
      U.card + (kpt_old_actual_selected_levels
        family X top R).card := by
  have hSub :=
    kpt_failed_max_old_socle_originals_subset_needed
      family K k N hAvoid U X Y top R Allowed
  have hCard := Finset.card_le_card hSub
  have hNeedBound :=
    kpt_originals_needing_max_old_socle_test_card_le_root_add_selected
      family K k N hAvoid U X Y top R Allowed
  exact hCard.trans hNeedBound

/-- E88's explicit ONE-WAY obstruction dichotomy. For a genuine
old normalized-Kpt AlgorithmRun on X and an actual one-BARE-root
extension Y, classify Allowed as true safe isolated-dummy or
no-stage-E-free-end odd source cuts.

If NO genuine Y AlgorithmRun exists with BOTH exactly old I and
entire total monoid-valued F, then EITHER:
 (A) some ACTUAL physical original has no old LIVE complete Kpt
     prefix mate at its highest eligible Allowed old-boring cut,
 OR
 (B) some OLD-BORING cut outside Allowed is physically nonquiet.

The proof is the contrapositive of the independently verified
SUFFICIENT E84 construction. We deliberately DO NOT claim the
converse: failing a chosen sufficient certificate may coexist
with a synchronized run constructed by a different argument.
No NEW AlgorithmRun is assumed in the other hypotheses. -/
theorem finiteNumericH_no_same_run_implies_failed_original_or_other_cut
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
    (hNoRun : ¬ ∃ RY : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family) Y top,
      RY.I = R.I ∧ RY.F = R.F) :
    (kpt_failed_max_old_socle_originals
      family (normalizedGraphModel E) k N hAvoid
      U X Y top R Allowed).Nonempty ∨
    (∃ cut : Nat,
      cut < top ∧ cut ∉ Allowed ∧
      ¬ SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family)
        (SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) X) cut ∧
      ¬ NewRootNoNoveltyAtCut family
        (SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) X)
        (SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) Y)
        cut) := by
  classical
  by_contra hNoBad
  have hNoFailed :
      ¬ (kpt_failed_max_old_socle_originals
        family (normalizedGraphModel E) k N hAvoid
        U X Y top R Allowed).Nonempty := by
    intro h
    exact hNoBad (Or.inl h)
  have hNoOther :
      ¬ (∃ cut : Nat,
        cut < top ∧ cut ∉ Allowed ∧
        ¬ SMTree.Envelope.IsInterestingAt
          (normalizedKptSMTree family)
          (SMTree.Envelope.closure
            (admissibleKptSTree family) (R.I (cut+1)) X) cut ∧
        ¬ NewRootNoNoveltyAtCut family
          (SMTree.Envelope.closure
            (admissibleKptSTree family) (R.I (cut+1)) X)
          (SMTree.Envelope.closure
            (admissibleKptSTree family) (R.I (cut+1)) Y)
          cut) := by
    intro h
    exact hNoBad (Or.inr h)
  have hMax : ∀ v : Fin N,
      ∀ (hNonempty :
        (kpt_actual_original_socle_allowed_cuts
          family (normalizedGraphModel E) k N
          hAvoid U X Y top R Allowed v).Nonempty),
      KptActualOldSocleCoveredAt family X top R
        ((finiteNumericH (normalizedGraphModel E) k N).kptOriginal family hAvoid v)
        ((kpt_actual_original_socle_allowed_cuts
          family (normalizedGraphModel E) k N
          hAvoid U X Y top R Allowed v).max' hNonempty) := by
    intro v hNonempty
    by_contra hNotCovered
    have hFail :
        v ∈ kpt_failed_max_old_socle_originals
          family (normalizedGraphModel E) k N hAvoid
          U X Y top R Allowed :=
      (mem_kpt_failed_max_old_socle_originals
        family (normalizedGraphModel E) k N hAvoid
        U X Y top R Allowed v).mpr ⟨hNonempty,hNotCovered⟩
    exact hNoFailed ⟨v,hFail⟩
  have hOtherQuiet : ∀ cut : Nat, cut < top → cut ∉ Allowed →
      ¬ SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family)
        (SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) X) cut →
      NewRootNoNoveltyAtCut family
        (SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) X)
        (SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) Y)
        cut := by
    intro cut hCut hNotAllowed hBoring
    by_contra hNotQuiet
    exact hNoOther ⟨cut,hCut,hNotAllowed,hBoring,hNotQuiet⟩
  exact hNoRun
    (finiteNumericH_one_bare_root_run_of_two_safe_classes_original_max
      family E hGraphSym k N hAvoid U X Y
      hX newV hNewInU hBare top R Allowed
      hAllowedSafe hMax hOtherQuiet)

/-- If the OTHER OLD-BORING source cuts have independently been
proved physically quiet, and no same-I/total-F new run exists,
then there is a CONCRETE physical ORIGINAL whose maximal
eligible Allowed complete OLD Kpt-prefix matching test fails.

This is obstruction extraction, NOT an equivalence between a
failed sufficient certificate and nonexistence of every run.
The finite failing-original carrier obeys E86's selected-level
cardinality bound, independently of physical numerical N. -/
theorem finiteNumericH_no_same_run_of_other_quiet_has_failed_original
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
        cut)
    (hNoRun : ¬ ∃ RY : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family) Y top,
      RY.I = R.I ∧ RY.F = R.F) :
    (kpt_failed_max_old_socle_originals
      family (normalizedGraphModel E) k N hAvoid
      U X Y top R Allowed).Nonempty := by
  rcases finiteNumericH_no_same_run_implies_failed_original_or_other_cut
      family E hGraphSym k N hAvoid U X Y
      hX newV hNewInU hBare top R Allowed
      hAllowedSafe hNoRun with hFailed | ⟨cut,hCut,hNotAllowed,hBoring,hNotQuiet⟩
  · exact hFailed
  · exact False.elim (hNotQuiet (hOtherQuiet cut hCut hNotAllowed hBoring))

end Kk
