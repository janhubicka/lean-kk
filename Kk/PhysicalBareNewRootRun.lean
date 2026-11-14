import Kk.PhysicalCrossHeightConstructedWitness
import Kk.NumericHPhysicalNewRootRun
import SuccessorTree.EnvelopeRunExistence
import Mathlib.Tactic

/-!
# Track E: physically construct a BARE original-only growing-height Kpt run

The corrected Track C new-root source first used
  Yfull = closure_I X ∪ {new genuine original Kpt node}.
Although this is legitimate, preinserting old dependent parameter
nodes can create superfluous initial seeds before the old generating
levels are actually selected in a new run.

For the bare physical stage we use ONLY
  Ybare = X ∪ {new genuine original Kpt node},
where X denotes the literal genuine OLD Kpt initial seed family.
The FULL closure is then computed by the real AlgorithmRun.

Track C's physically verified old/new base columns and original
prefix COVER prove Ybare is represented, and its chronological
bound proves it is bounded. We CONSTRUCT the true canonical
AlgorithmRun on Ybare and its exhaustive finite Kpt source index.
With the OLD actual physical run and real top seed, every EXTRA
cut below oldTop gets a finite live physical source witness.

This eliminates preinserted old closure as an initial-seed artifact
for the ONE-STEP physical new-root presentation. It does NOT prove
the unbounded resolved diary or the common labelled inverse orbit.

English-first proof and hostile audit:
  docs/track_e_physical_bare_new_root_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The truly BARE corrected new physical seed set: keep the OLD
initial Kpt source X and insert only the NEW actual Kpt original
at numerical H+ target hPosition k j k. No ancestor prefix pool
and no inherited old parameter closure is preinserted.

The old source X itself may contain legitimate dependent Kpt nodes,
but the new seed is one genuine original, not all its prefixes.
-/
def finiteNumericH_bareTopRootSeeds
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M j : Nat)
    (hAvoidL : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (hTarget : hPosition k j k < M)
    (X : Set (AdmissibleKptNode family)) :
    Set (AdmissibleKptNode family) :=
  X ∪
    ((fun v : Fin M =>
      (finiteNumericH L k M).kptOriginal family hAvoidL v) ''
      ({(⟨hPosition k j k, hTarget⟩ : Fin M)} : Set (Fin M)))

/-- A physically legitimate bare old+one-new-original Kpt initial
seed set has an ACTUAL prefix-pool covering set V of new B-original
names, is bounded by the true new-root free-level top and has a
real Kpt seed exactly at that top.

The covering V is constructed by Track C's real base-extension
source theorem (as ambientStagePool on cast old originals and
inherited levels, union the singleton NEW original name).
The larger closure_I X∪{w} is used only as a PROVEN dominating
COVER / bound; it is NOT the initial seed set of the new run.

The free-level top and the avoidance of BOTH numerical H+
structures remain genuine hypotheses about physical original
columns, not merely selected-old graph age agreement. -/
theorem finiteNumericH_bareTopRoot_seeds_represented_bounded
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
    (I : Set Nat) :
    ∃ V : Set (Fin M),
      (finiteNumericH_bareTopRootSeeds
        family L k M j hAvoidL hTarget X ⊆
        ambientPrefixPool family (finiteNumericH L k M)
          hAvoidL V) ∧
      (finiteNumericH_bareTopRootSeeds
        family L k M j hAvoidL hTarget X ⊆
        SMTree.Envelope.levelLe
          (T := AdmissibleKptNode family)
          (hPosition k (j-1) k+1)) ∧
      (∃ y : AdmissibleKptNode family,
        y ∈ finiteNumericH_bareTopRootSeeds
          family L k M j hAvoidL hTarget X ∧
        LevelTree.lev y = hPosition k (j-1) k+1) := by
  classical
  let B : EnumeratedPartialStructure db du dd :=
    finiteNumericH L k M
  let w : Fin M := ⟨hPosition k j k, hTarget⟩
  let O : Set (AdmissibleKptNode family) :=
    ((fun v : Fin M => B.kptOriginal family hAvoidL v) ''
      ({w} : Set (Fin M)))
  let Ybare : Set (AdmissibleKptNode family) := X ∪ O
  let Yfull : Set (AdmissibleKptNode family) :=
    finiteNumericH_physicalExtendedSeeds
      family L k M hAvoidL I X ({w} : Set (Fin M))
  let V : Set (Fin M) :=
    ambientStagePool B ((Fin.castLE hNM) '' U) I ∪
      ({w} : Set (Fin M))
  have hSub : Ybare ⊆ Yfull := by
    intro z hz
    rcases hz with hX | hO
    · exact Or.inl
        ((SMTree.Envelope.subset_closure
          (admissibleKptSTree family) I X) hX)
    · exact Or.inr hO
  have hFullCover : Yfull ⊆
      ambientPrefixPool family B hAvoidL V :=
    finiteNumericH_baseExtension_constructed_nextSeeds_represented
      family K L k b N M hNM hBlock hBin hUn hDiag
      hAvoidK hAvoidL U X hSeeds I ({w} : Set (Fin M))
  have hFullBound : Yfull ⊆
      SMTree.Envelope.levelLe
        (T := AdmissibleKptNode family)
        (hPosition k (j-1) k+1) :=
    (finiteNumericH_baseExtension_actual_top_root_run_bounded
      family K L k b N M j
      hNM hBlock hk hj hTarget hNTop
      hBin hUn hDiag hAvoidK hAvoidL U X hSeeds I).2
  let yTop : AdmissibleKptNode family :=
    B.kptOriginal family hAvoidL w
  have hYTop : yTop ∈ Ybare := by
    apply Or.inr
    exact ⟨w, by simp, rfl⟩
  have hTopLev : LevelTree.lev yTop =
      hPosition k (j-1) k+1 := by
    change B.freeLevel w.val = hPosition k (j-1) k+1
    exact finiteNumericH_top_freeLevel_exact
      L k M j hk hj hTarget
  refine ⟨V, hSub.trans hFullCover,
    hSub.trans hFullBound, yTop, hYTop, hTopLev⟩

/-- Construct a REAL bounded canonical AlgorithmRun, actual top
source and ONE complete finite injectively named Kpt closure index
directly from BARE old+new-original seeds.

No old-closure seed preinsertion is used: the true AlgorithmRun
regenerates meets and selected dependent parameters as it scans.
The original-prefix pool V is used only to certify full source
representation and finite exhaustion. -/
theorem finiteNumericH_bareTopRoot_construct_exhaustive_run
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
    (I : Set Nat) :
    (finiteNumericH_bareTopRootSeeds
      family L k M j hAvoidL hTarget X ⊆
      SMTree.Envelope.levelLe
        (T := AdmissibleKptNode family)
        (hPosition k (j-1) k+1)) ∧
    HasPhysicalExhaustiveKptRun family
      (finiteNumericH_bareTopRootSeeds
        family L k M j hAvoidL hTarget X)
      (hPosition k (j-1) k+1) := by
  classical
  obtain ⟨V,hCover,hBound,hTopSeed⟩ :=
    finiteNumericH_bareTopRoot_seeds_represented_bounded
      family K L k b N M j hNM hBlock hk hj
      hTarget hNTop hBin hUn hDiag hAvoidK hAvoidL
      U X hSeeds I
  let Y : Set (AdmissibleKptNode family) :=
    finiteNumericH_bareTopRootSeeds
      family L k M j hAvoidL hTarget X
  let top : Nat := hPosition k (j-1) k+1
  let Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y top :=
    SMTree.Envelope.canonicalAlgorithmRun
      (normalizedKptSMTree family) Y top
  obtain ⟨params,live,hParams,hInj,hLive,hCoverAll⟩ :=
    finiteNumericH_actualRun_uniform_exhaustive_source_index
      family L k M hAvoidL V Y hCover top Run
  refine ⟨hBound,Run,hTopSeed,params,live,hParams,
    hInj,hLive,hCoverAll⟩

/-- The physical OLD run is extracted from its actual complete
finite-source certificate. The taller NEW run is freshly
CONSTRUCTED from BARE old initial Kpt seeds plus a single true
new physical Kpt original at its exact numerical E-free top.

Its entire actual Kpt closure source has one finite exhaustive
index, including every real meet, auxiliary E and parameter node.

Every extra selected cut below oldTop is guaranteed to have a
LIVE finite source index witnessing a NEW terminal node or a
NEW complete old/upper dependent L+ crossing pair absent from
the old pre-cut closure. There is NO preinserted old parameter
closure in these new initial seeds, so this is a physically
cleaner one-step root extension than the Yfull constructor.

The oldTop≤newTop inequality is DERIVED from the actual old-top
seed's numerical original-prefix representation and the
chronological N≤newTop bound. No common labelled inverse-source
monoid orbit, selected graph-age diary claim or uniform BRD
carrier is asserted. -/
theorem finiteNumericH_old_and_bare_new_runs_extra_cuts_have_finite_witness
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
    ∃ RunOld : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family) X oldTop,
      ∃ RunNew : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family)
        (finiteNumericH_bareTopRootSeeds
          family L k M j hAvoidL hTarget X)
        (hPosition k (j-1) k+1),
      ∃ params : Finset (AdmissibleKptNode family),
        ∃ live : Nat → Fin params.card → Bool,
          (∀ z : AdmissibleKptNode family,
            z ∈ params ↔
              z ∈ SMTree.Envelope.closure
                (admissibleKptSTree family) (RunNew.I 0)
                (finiteNumericH_bareTopRootSeeds
                  family L k M j hAvoidL hTarget X)) ∧
          (∀ cut : Nat, cut < oldTop →
            cut ∈ RunNew.I cut → cut ∉ RunOld.I cut →
              IndexedNewSourceCutWitness family
                (fun t : Fin params.card =>
                  (params.equivFin.symm t).val)
                live
                (SMTree.Envelope.closure (admissibleKptSTree family)
                  (RunOld.I (cut+1)) X) cut) := by
  classical
  obtain ⟨RunOld,hOldTopSeed,
    _oldParams,_oldLive,_oldExact,_oldInj,
    _oldPresent,_oldCover⟩ := hOldPhysical
  have hTopLe : oldTop ≤ hPosition k (j-1) k+1 :=
    finiteNumericH_old_physical_top_le_new_chronological_top
      family K k N j oldTop hNTop hAvoidK U X hSeeds hOldTopSeed
  obtain ⟨_hBound,RunNew,_hNewTop,params,live,
    hParams,_hInj,_hPresent,hCover⟩ :=
    finiteNumericH_bareTopRoot_construct_exhaustive_run
      family K L k b N M j hNM hBlock hk hj
      hTarget hNTop hBin hUn hDiag hAvoidK hAvoidL
      U X hSeeds (RunOld.I 0)
  let Y : Set (AdmissibleKptNode family) :=
    finiteNumericH_bareTopRootSeeds
      family L k M j hAvoidL hTarget X
  have hSeed : X ⊆ Y := by
    intro z hz
    exact Or.inl hz
  refine ⟨RunOld,RunNew,params,live,hParams,?_⟩
  intro cut hCut hNew hOld
  exact crossheight_new_selected_Kpt_cut_has_indexed_physical_witness
    family X Y hSeed oldTop (hPosition k (j-1) k+1) cut
    hTopLe hOldTopSeed RunOld RunNew hCut hNew hOld
    (fun t : Fin params.card => (params.equivFin.symm t).val)
    live (hCover cut (lt_of_lt_of_le hCut hTopLe))

end Kk
