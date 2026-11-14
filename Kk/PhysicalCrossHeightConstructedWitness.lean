import Kk.CrossHeightIndexedNovelty
import Kk.NumericHPhysicalNewRootRun
import Mathlib.Tactic

/-!
# Track E: construct the genuine old and taller new numerical-H+ runs

Track C has already verified a corrected physical new-root constructor
with ORIGINAL-only seeds and a complete finite indexed Kpt source.
Track E has verified that a new selected cut BELOW the old scan top
has a novel terminal Kpt node or complete dependent L+ crossing pair.

Here neither the NEW AlgorithmRun nor its finite exhaustive index
is assumed: both are constructed from the true finite H+ new root
at its exact numerical E free cut, and the new source is bounded.

A real OLD physical exhaustive-run witness supplies the older
AlgorithmRun and, crucially, a genuine old-top Kpt seed. Using its
physical original-prefix representation, the true old top is
bounded by the old numerical carrier N and therefore by the
chronological actual NEW top.

No arbitrary selected-front diary or fake E-only witness is used;
all auxiliary E, negative L and I2 forks survive in the literal
new source finite Kpt node universe.

English proof and adversarial tests committed before Lean:
  docs/track_e_physical_crossheight_constructed_witness_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A GENUINE old-top physical Kpt seed x must be an initial
segment of an ACTUAL old numerical-H+ Kpt original w.

Its Kpt level is therefore bounded by the free level of that
original, hence by its old numerical position < N. The real
chronological old-carrier bound N≤newTop yields oldTop≤newTop.

This argument does NOT work for a formal topI marker with no
old-top physical seed; the explicit hOldTopSeed is essential. -/
theorem finiteNumericH_old_physical_top_le_new_chronological_top
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N j oldTop : Nat)
    (hNTop : N ≤ hPosition k (j-1) k+1)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Set (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hSeeds : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid U)
    (hOldTopSeed : ∃ x : AdmissibleKptNode family,
      x ∈ X ∧ LevelTree.lev x = oldTop) :
    oldTop ≤ hPosition k (j-1) k+1 := by
  obtain ⟨x,hx,hLev⟩ := hOldTopSeed
  obtain ⟨o,⟨v,_hv,rfl⟩,hBelow⟩ := hSeeds hx
  have hKptBound :
      LevelTree.lev x ≤ (finiteNumericH K k N).freeLevel v.val :=
    LevelTree.level_le_of_le hBelow
  have hFree := (finiteNumericH K k N).freeLevel_le v.val
  have hvN : v.val < N := v.isLt
  omega

/-- PHYSICALLY CONSTRUCT BOTH genuine descending Kpt AlgorithmRuns
and ONE FINITE index of the entire NEW actual source.

Assumptions encode the real physical old/new numerical H+ structures:
  * N≤M and old-base K / new-base L agree in ALL genuinely old
    directed binary/unary/diagonal atoms below block frontier b;
  * both full ordinary-L H+ reducts avoid the specified forbidden
    family (not merely their selected graph shadows);
  * the OLD Kpt seed set is genuinely represented by old Kpt
    ORIGINAL prefix nodes and has a REAL physical exhaustive run;
  * the newly inserted original is an ACTUAL physical target at
    numerical position hPosition k j k with j>0 and k>0;
  * N lies below the exact new original E-free top coordinate.

The theorem constructs a real bounded new-root seed Y containing
the entire old meet/selected-parameter closure plus ONLY the
new genuine Kpt original at w (NOT all its prefixes); a true
new AlgorithmRun and an exhaustive finite Kpt node index with
live masks at all cuts.

For EVERY extra cut c STRICTLY BELOW oldTop selected by the
taller new run but skipped by the old run, the same actual finite
new node index witnesses either a NEW terminal source Kpt node,
or a NEW complete old/upper L+ crossing pair from the SAME live
Kpt node, absent from the old full pre-cut Kpt source.

No labelled inverse-source orbit or finite diary BRD bound is
asserted: this is an actual numerical-H+ physical extra-event
certificate, subject to the real K-free new-column hypotheses. -/
theorem finiteNumericH_constructed_growing_runs_extra_cuts_have_finite_witness
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K L : AgeTestModel db du dd)
    (k b N M j : Nat)
    (hNM : N ≤ M) (hBlock : N ≤ hPosition k b 0)
    (hk : 0 < k) (hj : 0 < j)
    (hTarget : hPosition k j k < M)
    (hNTop : N ≤ hPosition k (j-1) k+1)
    (hBin : ∀ i j : Nat, i < b → j < b →
      ∀ r : Fin db, K.binary i j r = L.binary i j r)
    (hUn : ∀ i : Nat, i < b → ∀ r : Fin du,
      K.unary i r = L.unary i r)
    (hDiag : ∀ i : Nat, i < b → ∀ r : Fin dd,
      K.diagonal i r = L.diagonal i r)
    (hAvoidK : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hAvoidL : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (U : Set (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hSeeds : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoidK U)
    (oldTop : Nat)
    (hOldPhysical : HasPhysicalExhaustiveKptRun family X oldTop) :
    let w : Fin M := ⟨hPosition k j k, hTarget⟩
    let newTop : Nat := hPosition k (j-1) k+1
    ∃ RunOld : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family) X oldTop,
      let Y : Set (AdmissibleKptNode family) :=
        finiteNumericH_physicalExtendedSeeds
          family L k M hAvoidL (RunOld.I 0) X ({w} : Set (Fin M))
      ∃ RunNew : SMTree.Envelope.AlgorithmRun
          (normalizedKptSMTree family) Y newTop,
        ∃ params : Finset (AdmissibleKptNode family),
          ∃ live : Nat → Fin params.card → Bool,
            Y ⊆ SMTree.Envelope.levelLe
              (T := AdmissibleKptNode family) newTop ∧
            (∀ z : AdmissibleKptNode family,
              z ∈ params ↔
              z ∈ SMTree.Envelope.closure
                (admissibleKptSTree family) (RunNew.I 0) Y) ∧
            (∀ cut : Nat, cut < oldTop →
              cut ∈ RunNew.I cut → cut ∉ RunOld.I cut →
                IndexedNewSourceCutWitness family
                  (fun t : Fin params.card =>
                    (params.equivFin.symm t).val)
                  live
                  (SMTree.Envelope.closure
                    (admissibleKptSTree family)
                    (RunOld.I (cut+1)) X)
                  cut) := by
  classical
  obtain ⟨RunOld,hOldTopSeed,
    _paramsOld,_liveOld,_oldExact,_oldInjective,
    _oldPresent,_oldCover⟩ := hOldPhysical
  let newTop : Nat := hPosition k (j-1) k+1
  let w : Fin M := ⟨hPosition k j k, hTarget⟩
  let Y : Set (AdmissibleKptNode family) :=
    finiteNumericH_physicalExtendedSeeds
      family L k M hAvoidL (RunOld.I 0) X ({w} : Set (Fin M))
  have hTopLe : oldTop ≤ newTop :=
    finiteNumericH_old_physical_top_le_new_chronological_top
      family K k N j oldTop hNTop hAvoidK U X hSeeds hOldTopSeed
  have hNewPhysical :=
    finiteNumericH_baseExtension_actual_top_root_run_bounded
      family K L k b N M j
      hNM hBlock hk hj hTarget hNTop
      hBin hUn hDiag hAvoidK hAvoidL U X hSeeds (RunOld.I 0)
  obtain ⟨⟨RunNew,_newTopSeed,params,live,hParams,_hInj,
    _hPresent,hCover⟩,hYBound⟩ := hNewPhysical
  have hSeed : X ⊆ Y := by
    intro z hz
    exact Or.inl ((SMTree.Envelope.subset_closure
      (admissibleKptSTree family) (RunOld.I 0) X) hz)
  refine ⟨RunOld,RunNew,params,live,hYBound,hParams,?_⟩
  intro cut hCut hNew hOld
  have hCutNew : cut < newTop := lt_of_lt_of_le hCut hTopLe
  exact crossheight_new_selected_Kpt_cut_has_indexed_physical_witness
    family X Y hSeed oldTop newTop cut
    hTopLe hOldTopSeed RunOld RunNew
    hCut hNew hOld
    (fun t : Fin params.card => (params.equivFin.symm t).val)
    live (hCover cut hCutNew)

end Kk
