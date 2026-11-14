import Kk.NumericHBaseExtensionCoherence
import Kk.NumericHTopAuxE
import Kk.NumericHExhaustiveRunIndex
import SuccessorTree.EnvelopeRunExistence
import Mathlib.Tactic

/-!
# Track C: actual NEW Kpt roots + OLD full closure produce a REAL run

English proof and 16 hostile checks committed BEFORE this Lean source:
  docs/track_c_physical_new_root_run_english_audit.md

The previous Track C lemma covers OLD dependent L+ sources when the
base Henson original table gains new blocks. We now CONSTRUCT the
next Kpt seed set, rather than postulating its hNext inclusion:

  Y = entire old meet/parameter closure at old levels I
      UNION every genuine prefix of the new physical originals W.

Both summands use the actual forbidden-free Kpt tree and actual
physical numerical-H+ originals, including auxiliary E and negative
ordinary-L bits.

This complete seed set has a real original-prefix pool, admits the
genuine successor-tree canonical AlgorithmRun, and has one finite
exhaustive per-cut index. A physical real TOP-generation new root
discharges the positive top-seed requirement by its EXACT E free cut.

There is no claim that this entire seed set has a prescribed minimal
resolved diary or that the newly inserted Henson columns are K-free
without the separate avoidance hypotheses.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A canonical explicitly CONSTRUCTED next Kpt seed set:
all actual old meet/selected-parameter closure nodes, plus
ALL prefixes of genuine NEW physical original Kpt nodes.
This includes the full auxiliary E structure. -/
def finiteNumericH_physicalExtendedSeeds
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (hAvoidL : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (I : Set Nat)
    (X : Set (AdmissibleKptNode family))
    (W : Set (Fin M)) : Set (AdmissibleKptNode family) :=
  SMTree.Envelope.closure (admissibleKptSTree family) I X ∪
    ambientPrefixPool family (finiteNumericH L k M) hAvoidL W

/-- After extending the base Henson model K to L and the finite
numeric carrier N to M, the EXPLICIT full-old-closure plus
genuine-new-root seed family is contained in a literal
physical original-prefix pool. The new-root/old-closure dichotomy
follows from its DEFINITION; no arbitrary hNext assumption.

All old auxiliary E, fake predecessors and meet-generated
parameters are preserved using the previous physical base
extension theorem and the verified multi-root closure invariant.
-/
theorem finiteNumericH_baseExtension_constructed_nextSeeds_represented
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K L : AgeTestModel db du dd)
    (k b N M : Nat) (hNM : N ≤ M)
    (hBlock : N ≤ hPosition k b 0)
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
    (I : Set Nat)
    (W : Set (Fin M)) :
    finiteNumericH_physicalExtendedSeeds family L k M
      hAvoidL I X W ⊆
      ambientPrefixPool family (finiteNumericH L k M) hAvoidL
        (ambientStagePool (finiteNumericH L k M)
          ((Fin.castLE hNM) '' U) I ∪ W) := by
  let U' : Set (Fin M) := (Fin.castLE hNM) '' U
  have hOldSeeds :
      X ⊆ ambientPrefixPool family (finiteNumericH L k M)
        hAvoidL U' :=
    finiteNumericH_baseExtension_old_seedPool_lifts
      family K L k b N M hNM hBlock hBin hUn hDiag
      hAvoidK hAvoidL U X hSeeds
  exact finiteNumericH_multiRoot_nextSeed_pool_preserved
    family L k M hAvoidL U' W I X
    (finiteNumericH_physicalExtendedSeeds family L k M
      hAvoidL I X W)
    hOldSeeds (by intro z hz; exact hz)

/-- An actual REAL numerical-H+ AlgorithmRun together with ONE
complete finite, injectively named Kpt source-index universe and
an exact Boolean active mask at EVERY scanned cut.

This assertion includes a genuine seed at the actual chosen top,
not merely existence of a run on an empty seed family. -/
def HasPhysicalExhaustiveKptRun
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Y : Set (AdmissibleKptNode family))
    (top : Nat) : Prop :=
  ∃ R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y top,
    (∃ y ∈ Y, LevelTree.lev y = top) ∧
    ∃ params : Finset (AdmissibleKptNode family),
      ∃ presentAt : Nat → Fin params.card → Bool,
        (∀ z : AdmissibleKptNode family,
          z ∈ params ↔
          z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
            (R.I 0) Y) ∧
        Function.Injective
          (fun j : Fin params.card => (params.equivFin.symm j).val) ∧
        (∀ cut : Nat, ∀ j : Fin params.card,
          presentAt cut j = true ↔
          (params.equivFin.symm j).val ∈
            SMTree.Envelope.closure (admissibleKptSTree family)
              (R.I (cut+1)) Y) ∧
        (∀ cut : Nat, cut < top →
          ∀ z : AdmissibleKptNode family,
            z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
              (R.I (cut+1)) Y ↔
            ∃ j : Fin params.card,
              (params.equivFin.symm j).val = z ∧
              presentAt cut j = true)

/-- Given a GENUINE newly available physical original w whose
canonical E free level is top, the explicitly formed seed Y
contains its actual Kpt original at precisely that level.

Consequently the pinned successor-tree CONSTRUCTS a real
AlgorithmRun (not an assumed algorithm), and Track C's finite
exhaustive source theorem CONSTRUCTS its one common per-cut
full-Kpt source-node index and Boolean live masks.

No assumed existence of new L+ parameter nodes or of a
canonical resolved macrodiary is hidden in the conclusion.
-/
theorem finiteNumericH_baseExtension_construct_actual_run_from_new_root
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K L : AgeTestModel db du dd)
    (k b N M : Nat) (hNM : N ≤ M)
    (hBlock : N ≤ hPosition k b 0)
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
    (I : Set Nat)
    (W : Set (Fin M)) (top : Nat)
    (hNewRoot : ∃ w : Fin M, w ∈ W ∧
      (finiteNumericH L k M).freeLevel w.val = top) :
    HasPhysicalExhaustiveKptRun family
      (finiteNumericH_physicalExtendedSeeds
        family L k M hAvoidL I X W) top := by
  classical
  let B : EnumeratedPartialStructure db du dd :=
    finiteNumericH L k M
  let U' : Set (Fin M) := (Fin.castLE hNM) '' U
  let V : Set (Fin M) := ambientStagePool B U' I ∪ W
  let Y : Set (AdmissibleKptNode family) :=
    finiteNumericH_physicalExtendedSeeds family L k M
      hAvoidL I X W
  have hY : Y ⊆ ambientPrefixPool family B hAvoidL V :=
    finiteNumericH_baseExtension_constructed_nextSeeds_represented
      family K L k b N M hNM hBlock hBin hUn hDiag
      hAvoidK hAvoidL U X hSeeds I W
  obtain ⟨w,hw,hFree⟩ := hNewRoot
  have hTop : ∃ y ∈ Y, LevelTree.lev y = top := by
    let y : AdmissibleKptNode family :=
      B.kptOriginal family hAvoidL w
    refine ⟨y, ?_, ?_⟩
    · change y ∈
        SMTree.Envelope.closure (admissibleKptSTree family) I X ∪
          ambientPrefixPool family B hAvoidL W
      exact Or.inr ⟨y, ⟨w,hw,rfl⟩, le_rfl⟩
    · change B.freeLevel w.val = top
      exact hFree
  let R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y top :=
    SMTree.Envelope.canonicalAlgorithmRun
      (normalizedKptSMTree family) Y top
  obtain ⟨params,presentAt,hExact,hInjective,hPresent,hCover⟩ :=
    finiteNumericH_actualRun_uniform_exhaustive_source_index
      family L k M hAvoidL V Y hY top R
  refine ⟨R,hTop,params,presentAt,hExact,hInjective,hPresent,hCover⟩

/-- A NEW genuine numerical H+ TOP-generation original at block j>0
has its EXACT generated free cut top=hPosition k (j-1) k+1.

Adjoining its ACTUAL Kpt original and EVERY inherited old
meet/parameter source now CONSTRUCTS a true successor-tree
AlgorithmRun with a top-level seed and exhaustive finite full
source index, with NO separately assumed top-root certificate.

The one-point Henson / mixed-clique check needed to realize
the requested NEW original binary L column remains a separate
Track A/B premise encoded in hAvoidL and K/L old-column fidelity.
-/
theorem finiteNumericH_baseExtension_actual_top_root_run
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K L : AgeTestModel db du dd)
    (k b N M j : Nat)
    (hNM : N ≤ M) (hBlock : N ≤ hPosition k b 0)
    (hk : 0 < k) (hj : 0 < j)
    (hTarget : hPosition k j k < M)
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
    let w : Fin M := ⟨hPosition k j k, hTarget⟩
    let Y := finiteNumericH_physicalExtendedSeeds
      family L k M hAvoidL I X ({w} : Set (Fin M))
    HasPhysicalExhaustiveKptRun family Y
      (hPosition k (j-1) k + 1) := by
  let w : Fin M := ⟨hPosition k j k, hTarget⟩
  have hRoot :
      ∃ v : Fin M, v ∈ ({w} : Set (Fin M)) ∧
        (finiteNumericH L k M).freeLevel v.val =
          hPosition k (j-1) k + 1 := by
    refine ⟨w, by simp, ?_⟩
    change (finiteNumericH L k M).freeLevel
      (hPosition k j k) = hPosition k (j-1) k+1
    exact finiteNumericH_top_freeLevel_exact
      L k M j hk hj hTarget
  exact finiteNumericH_baseExtension_construct_actual_run_from_new_root
    family K L k b N M hNM hBlock hBin hUn hDiag
    hAvoidK hAvoidL U X hSeeds I ({w} : Set (Fin M))
    (hPosition k (j-1) k+1) hRoot

/-- A selected top-generation numeric H+ root supplies more than
a top seed: if the OLD numerical carrier N lies at or below
its ACTUAL canonical free cut, then EVERY node of the constructed
new seed Y (including all inherited MEETS/PARAMETERS and new-root
prefixes) is at or below the scan height.

This essential boundedness was NOT automatic from the previous
top-seed theorem. It enables proper application of bounded
successor-tree envelope invariants, still without identifying a
canonical global resolved macrodiary. -/
theorem finiteNumericH_baseExtension_actual_top_root_run_bounded
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
    let w : Fin M := ⟨hPosition k j k, hTarget⟩
    let Y := finiteNumericH_physicalExtendedSeeds
      family L k M hAvoidL I X ({w} : Set (Fin M))
    HasPhysicalExhaustiveKptRun family Y
      (hPosition k (j-1) k+1) ∧
    Y ⊆ SMTree.Envelope.levelLe
      (T := AdmissibleKptNode family)
      (hPosition k (j-1) k+1) := by
  let A : EnumeratedPartialStructure db du dd :=
    finiteNumericH K k N
  let B : EnumeratedPartialStructure db du dd :=
    finiteNumericH L k M
  let top : Nat := hPosition k (j-1) k+1
  let w : Fin M := ⟨hPosition k j k, hTarget⟩
  let Y : Set (AdmissibleKptNode family) :=
    finiteNumericH_physicalExtendedSeeds
      family L k M hAvoidL I X ({w} : Set (Fin M))
  have hOldLevel : X ⊆
      SMTree.Envelope.levelLe
        (T := AdmissibleKptNode family) top := by
    intro z hz
    obtain ⟨o,⟨v,_hv,rfl⟩,hBelow⟩ := hSeeds hz
    have hLev := LevelTree.level_le_of_le hBelow
    have hFree := A.freeLevel_le v.val
    have hvN : v.val < N := v.isLt
    change LevelTree.lev z ≤ top
    omega
  have hClosureBound :
      SMTree.Envelope.closure (admissibleKptSTree family) I X ⊆
        SMTree.Envelope.levelLe
          (T := AdmissibleKptNode family) top :=
    SMTree.Envelope.closure_subset_levelLe
      (S := admissibleKptSTree family) I X top hOldLevel
  have hNewFree : B.freeLevel w.val = top := by
    change (finiteNumericH L k M).freeLevel
      (hPosition k j k) = hPosition k (j-1) k+1
    exact finiteNumericH_top_freeLevel_exact
      L k M j hk hj hTarget
  have hYBound : Y ⊆ SMTree.Envelope.levelLe
      (T := AdmissibleKptNode family) top := by
    intro z hz
    rcases hz with hzOld | hzNew
    · exact hClosureBound hzOld
    · obtain ⟨o, ⟨v,hv,rfl⟩,hBelow⟩ := hzNew
      have hEq : v = w := by
        simpa using hv
      subst v
      have hLev := LevelTree.level_le_of_le hBelow
      change LevelTree.lev z ≤ top
      omega
  constructor
  · exact finiteNumericH_baseExtension_actual_top_root_run
      family K L k b N M j hNM hBlock hk hj hTarget
      hBin hUn hDiag hAvoidK hAvoidL U X hSeeds I
  · exact hYBound

#print axioms Kk.finiteNumericH_baseExtension_constructed_nextSeeds_represented
#print axioms Kk.finiteNumericH_baseExtension_construct_actual_run_from_new_root
#print axioms Kk.finiteNumericH_baseExtension_actual_top_root_run
#print axioms Kk.finiteNumericH_baseExtension_actual_top_root_run_bounded

end Kk
