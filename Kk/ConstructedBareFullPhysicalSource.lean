import Kk.BareFullFinalSourceIdentity
import Kk.PhysicalBareNewRootRun
import Kk.PhysicalCrossHeightConstructedWitness
import Mathlib.Tactic

/-!
# Track C — construct both actual bounded bare/full root runs and their source agreement

English-first proof and hostile review:
  docs/track_c_constructed_bare_full_physical_english_audit.md

Input is one ACTUAL old physical exhaustive Kpt run, genuine old/new
numerical-H+ physical models K,L with complete old original columns,
full normalized forbidden-family avoidance, and one physically present
new top original w. This module CONSTRUCTS both real new AlgorithmRuns;
their existence is not a premise.

The verified same-top bare/full source theorems then give identical
interesting selected I levels and literal equality of the FINAL complete
dependent Kpt closure. The bare run's exact finite index represents
that same full source for the inherited-full run.

This does not construct the global diary or compare two distinct
physical occurrences. Genuine K4 auxiliary cuts must be retained.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Genuine physical construction of the BARE and inherited-full new-root
AlgorithmRuns, with EXACT selected-level and complete FINAL Kpt-source
equality.

All old K/L atoms below the base frontier, both actual numerical-H+
forbidden-family tests and old seed prefix coverage are hypotheses;
the existence of either NEW run and the chronological top relation
are conclusions derived from prior exact physical constructors.

No arbitrary ancestor prefixes are used as new INITIAL seeds. -/
theorem finiteNumericH_construct_bare_full_root_same_source
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
    let top : Nat := hPosition k (j-1) k+1
    let w : Fin M := ⟨hPosition k j k, hTarget⟩
    let O : Set (AdmissibleKptNode family) :=
      ((fun v : Fin M =>
        (finiteNumericH L k M).kptOriginal family hAvoidL v) ''
        ({w} : Set (Fin M)))
    ∃ Rold : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family) X oldTop,
      ∃ Rbare : SMTree.Envelope.AlgorithmRun
          (normalizedKptSMTree family) (X ∪ O) top,
        ∃ Rfull : SMTree.Envelope.AlgorithmRun
            (normalizedKptSMTree family)
            (SMTree.Envelope.closure (admissibleKptSTree family)
              (Rold.I 0) X ∪ O) top,
          (∀ i : Nat, i ≤ top → Rbare.I i = Rfull.I i) ∧
          SMTree.Envelope.closure (admissibleKptSTree family)
              (Rbare.I 0) (X ∪ O) =
            SMTree.Envelope.closure (admissibleKptSTree family)
              (Rfull.I 0)
              (SMTree.Envelope.closure (admissibleKptSTree family)
                (Rold.I 0) X ∪ O) := by
  classical
  let top : Nat := hPosition k (j-1) k+1
  let w : Fin M := ⟨hPosition k j k, hTarget⟩
  let O : Set (AdmissibleKptNode family) :=
    ((fun v : Fin M =>
      (finiteNumericH L k M).kptOriginal family hAvoidL v) ''
      ({w} : Set (Fin M)))
  obtain ⟨Rold, hOldTopSeed, _oldParams, _oldLive,
    _oldExact, _oldInj, _oldMask, _oldCover⟩ := hOldPhysical
  have hOldLe : oldTop ≤ top :=
    finiteNumericH_old_physical_top_le_new_chronological_top
      family K k N j oldTop hNTop hAvoidK U X hSeeds hOldTopSeed
  have hBarePhysical :
      HasPhysicalExhaustiveKptRun family (X ∪ O) top :=
    (finiteNumericH_bareTopRoot_construct_exhaustive_run
      family K L k b N M j hNM hBlock hk hj hTarget hNTop
      hBin hUn hDiag hAvoidK hAvoidL U X hSeeds (Rold.I 0)).2
  have hFullPhysical :
      HasPhysicalExhaustiveKptRun family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (Rold.I 0) X ∪ O) top :=
    (finiteNumericH_baseExtension_actual_top_root_run_bounded
      family K L k b N M j hNM hBlock hk hj hTarget hNTop
      hBin hUn hDiag hAvoidK hAvoidL U X hSeeds (Rold.I 0)).1
  obtain ⟨Rbare, _bareTop, _bareParams, _bareLive,
    _bareExact, _bareInj, _bareMask, _bareCover⟩ :=
    hBarePhysical
  obtain ⟨Rfull, _fullTop, _fullParams, _fullLive,
    _fullExact, _fullInj, _fullMask, _fullCover⟩ :=
    hFullPhysical
  have hSel :
      ∀ i : Nat, i ≤ top → Rbare.I i = Rfull.I i :=
    finiteNumericH_bare_and_full_new_runs_same_selected_levels
      family L k M hAvoidL X ({w} : Set (Fin M))
      oldTop top hOldLe hOldTopSeed Rold Rbare Rfull
  have hFinal :
      SMTree.Envelope.closure (admissibleKptSTree family)
          (Rbare.I 0) (X ∪ O) =
        SMTree.Envelope.closure (admissibleKptSTree family)
          (Rfull.I 0)
          (SMTree.Envelope.closure (admissibleKptSTree family)
            (Rold.I 0) X ∪ O) :=
    finiteNumericH_bare_full_runs_final_source_eq
      family L k M hAvoidL X ({w} : Set (Fin M))
      oldTop top hOldLe hOldTopSeed Rold Rbare Rfull
  exact ⟨Rold, Rbare, Rfull, hSel, hFinal⟩

/-- Construct a SINGLE finite exact source index for BOTH actual
new-root seed presentations, not just two unrelated finite indices.

The source Finset is the bare run's TRUE full final Kpt closure.
Since the verified bare/full source equality holds, the SAME
Finset is EXACTLY the inherited-full run's final Kpt closure.
One genuine Boolean live mask from the bare run covers every
bare pre-cut source, and also every FULL pre-cut source node
at/above each tested cut (without falsely equating low masks).

The index enumerates dependent node identities, hence retains every
ordinary L, negative atom, auxiliary E and chosen parameter record.
It does NOT provide a uniform bound across distinct diary copies. -/
theorem finiteNumericH_construct_bare_full_common_source_index
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
    let top : Nat := hPosition k (j-1) k+1
    let w : Fin M := ⟨hPosition k j k, hTarget⟩
    let O : Set (AdmissibleKptNode family) :=
      ((fun v : Fin M =>
        (finiteNumericH L k M).kptOriginal family hAvoidL v) ''
        ({w} : Set (Fin M)))
    ∃ Rold : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family) X oldTop,
      ∃ Rbare : SMTree.Envelope.AlgorithmRun
          (normalizedKptSMTree family) (X ∪ O) top,
        ∃ Rfull : SMTree.Envelope.AlgorithmRun
            (normalizedKptSMTree family)
            (SMTree.Envelope.closure (admissibleKptSTree family)
              (Rold.I 0) X ∪ O) top,
          ∃ params : Finset (AdmissibleKptNode family),
            ∃ live : Nat → Fin params.card → Bool,
              (∀ i : Nat, i ≤ top → Rbare.I i = Rfull.I i) ∧
              (∀ z : AdmissibleKptNode family,
                z ∈ params ↔
                z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
                  (Rbare.I 0) (X ∪ O)) ∧
              (∀ z : AdmissibleKptNode family,
                z ∈ params ↔
                z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
                  (Rfull.I 0)
                  (SMTree.Envelope.closure (admissibleKptSTree family)
                    (Rold.I 0) X ∪ O)) ∧
              Function.Injective
                (fun a : Fin params.card => (params.equivFin.symm a).val) ∧
              (∀ cut : Nat, cut < top →
                ∀ z : AdmissibleKptNode family,
                  z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
                    (Rbare.I (cut+1)) (X ∪ O) ↔
                  ∃ a : Fin params.card,
                    (params.equivFin.symm a).val = z ∧
                    live cut a = true) ∧
              (∀ cut : Nat, cut < top →
                ∀ z : AdmissibleKptNode family,
                  cut ≤ LevelTree.lev z →
                    (z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
                      (Rfull.I (cut+1))
                      (SMTree.Envelope.closure (admissibleKptSTree family)
                        (Rold.I 0) X ∪ O) ↔
                     ∃ a : Fin params.card,
                       (params.equivFin.symm a).val = z ∧
                       live cut a = true)) := by
  classical
  let top : Nat := hPosition k (j-1) k+1
  let w : Fin M := ⟨hPosition k j k, hTarget⟩
  let O : Set (AdmissibleKptNode family) :=
    ((fun v : Fin M =>
      (finiteNumericH L k M).kptOriginal family hAvoidL v) ''
      ({w} : Set (Fin M)))
  obtain ⟨Rold,Rbare,Rfull,hSel,hFinal⟩ :=
    finiteNumericH_construct_bare_full_root_same_source
      family K L k b N M j hNM hBlock hk hj hTarget hNTop
      hBin hUn hDiag hAvoidK hAvoidL U X hSeeds oldTop hOldPhysical
  obtain ⟨V,hPool,_hBound,_hTop⟩ :=
    finiteNumericH_bareTopRoot_seeds_represented_bounded
      family K L k b N M j hNM hBlock hk hj hTarget hNTop
      hBin hUn hDiag hAvoidK hAvoidL U X hSeeds (Rold.I 0)
  obtain ⟨params,live,hExact,hInj,hLive,hCover⟩ :=
    finiteNumericH_actualRun_uniform_exhaustive_source_index
      family L k M hAvoidL V
      (finiteNumericH_bareTopRootSeeds
        family L k M j hAvoidL hTarget X)
      hPool top Rbare
  have hFullExact :
      ∀ z : AdmissibleKptNode family,
        z ∈ params ↔
        z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (Rfull.I 0)
          (SMTree.Envelope.closure (admissibleKptSTree family)
            (Rold.I 0) X ∪ O) := by
    intro z
    rw [← hFinal]
    exact hExact z
  have hFullVisible :
      ∀ cut : Nat, cut < top →
        ∀ z : AdmissibleKptNode family,
          cut ≤ LevelTree.lev z →
            (z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
              (Rfull.I (cut+1))
              (SMTree.Envelope.closure (admissibleKptSTree family)
                (Rold.I 0) X ∪ O) ↔
             ∃ a : Fin params.card,
               (params.equivFin.symm a).val = z ∧
               live cut a = true) := by
    intro cut hCut z hLev
    have hEvent :=
      finiteNumericH_bare_full_runs_all_cut_events_eq
        family L k M hAvoidL X ({w} : Set (Fin M))
        oldTop top
        (finiteNumericH_old_physical_top_le_new_chronological_top
          family K k N j oldTop hNTop hAvoidK U X hSeeds
          (by
            obtain ⟨_oldR,hTopSeed,_,_,_,_,_,_⟩ := hOldPhysical
            exact hTopSeed))
        (by
          obtain ⟨_oldR,hTopSeed,_,_,_,_,_,_⟩ := hOldPhysical
          exact hTopSeed)
        Rold Rbare Rfull cut hCut
    have hEquals := (hEvent.1 z hLev).symm
    exact hEquals.trans (hCover cut hCut z)
  exact ⟨Rold,Rbare,Rfull,params,live,hSel,hExact,hFullExact,
    hInj,hCover,hFullVisible⟩

end Kk
