import Kk.FullKptOldLBitNoFork
import Kk.K4GenerationZeroSourceSeparator
import Mathlib.Tactic

/-!
# Track D: transport ONE genuine physical old0 ordinary L bit to FULL Kpt nodes

English-first audit:
docs/audits/2026-11-16-track-d-physical-name-to-full-kpt-bit-english.md

Two actual Kpt nodes with their EXACT full dependent OLD source
records represented by two genuine finite numerical-H originals
inherit the OLD ordinary L bit at one physical generation-zero
coordinate. If that old base sees the selected later TOP original
but not the auxiliary later original, the Kpt nodes' complete
OLD dependent L+ records differ.

Crucially, the old-raw representation assumptions are explicit.
Physical numeric types are NOT identified with arbitrary Kpt
parameter/meet nodes by selected graph-age equality.

This is STACKED on the full-Kpt old-L bit no-fork PR #268.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Two ACTUAL Kpt nodes with exact complete old-source records
carried by physical Fin N original names inherit the SAME concrete
old numerical-H ordinary-L bit that separates a selected TOP
copy from a later negative auxiliary copy.

The physical old separator is generation zero of an older Q base,
and is strictly BEFORE the tested real numeric cut. Actual source
membership and source representation are explicitly assumed via
the two full raw-type equations; no selected shadow inference. -/
theorem kpt_old_ordinary_bit_certificate_of_named_numeric_originals
    {family : List (NormalizedForbidden 1 0 1)}
    (zSelected zAux : AdmissibleKptNode family)
    (E : Nat → Nat → Bool)
    (k N old cutBase selected aux g m : Nat)
    (hOldCut : old < cutBase)
    (hCutSelected : cutBase < selected)
    (hCutAux : cutBase < aux)
    (hg : g ≤ k) (hm : m ≤ k)
    (hPositive : E old selected = true)
    (hNegative : E old aux = false)
    (hCutIn : hPosition k cutBase g < N)
    (selectedName auxName : Fin N)
    (hSelectedName : selectedName.val = hPosition k selected k)
    (hAuxName : auxName.val = hPosition k aux m)
    (hRawSelected :
      kptFullOldAtCut zSelected (hPosition k cutBase g) =
        some (⟨hPosition k cutBase g,
          (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
            (hPosition k cutBase g) selectedName.val⟩ :
          RawPartialTypeNode 1 0 1))
    (hRawAux :
      kptFullOldAtCut zAux (hPosition k cutBase g) =
        some (⟨hPosition k cutBase g,
          (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
            (hPosition k cutBase g) auxName.val⟩ :
          RawPartialTypeNode 1 0 1)) :
    KptOldOrdinaryBitSeparation
      zSelected zAux (hPosition k cutBase g) := by
  classical
  let cut : Nat := hPosition k cutBase g
  let oldZero : Nat := hPosition k old 0
  let A : EnumeratedPartialStructure 1 0 1 :=
    finiteNumericH (normalizedGraphModel E) k N
  let T : PartialTypeWithE cut 1 0 1 :=
    A.partialTypeAt cut selectedName.val
  let V : PartialTypeWithE cut 1 0 1 :=
    A.partialTypeAt cut auxName.val
  have hPhysical :=
    finiteNumericH_old_zero_separates_top_from_negative
      E k N old cutBase selected aux g m
      hOldCut hCutSelected hCutAux hg hm hPositive hNegative
  change
    oldZero < cut ∧
    cut < hPosition k selected k ∧
    cut < hPosition k aux m ∧
    A.L.binary oldZero (hPosition k selected k) (0 : Fin 1) = true ∧
    A.L.binary oldZero (hPosition k aux m) (0 : Fin 1) = false ∧
    A.partialTypeAt cut (hPosition k selected k) ≠
      A.partialTypeAt cut (hPosition k aux m) at hPhysical
  obtain ⟨hEarlier,_hSelLater,_hAuxLater,hBitYes,hBitNo,_hFullDifferent⟩ :=
    hPhysical
  have hBitSelected :
      A.L.binary oldZero selectedName.val (0 : Fin 1) = true := by
    rw [hSelectedName]
    exact hBitYes
  have hBitAux :
      A.L.binary oldZero auxName.val (0 : Fin 1) = false := by
    rw [hAuxName]
    exact hBitNo
  have hReductSelected :
      T.lReduct =
        RelationalPrefixType.ofAgeModel A.L cut selectedName.val :=
    partialTypeAt_lReduct_eq_ofAgeModel A cut selectedName.val
  have hReductAux :
      V.lReduct =
        RelationalPrefixType.ofAgeModel A.L cut auxName.val :=
    partialTypeAt_lReduct_eq_ofAgeModel A cut auxName.val
  have hOldLSelected :
      T.lReduct.binary
        (some (⟨oldZero,hEarlier⟩ : Fin cut))
        none (0 : Fin 1) = true := by
    rw [hReductSelected]
    change A.L.binary oldZero selectedName.val (0 : Fin 1) = true
    exact hBitSelected
  have hOldLAux :
      V.lReduct.binary
        (some (⟨oldZero,hEarlier⟩ : Fin cut))
        none (0 : Fin 1) = false := by
    rw [hReductAux]
    change A.L.binary oldZero auxName.val (0 : Fin 1) = false
    exact hBitAux
  refine ⟨T,V,hRawSelected,hRawAux,⟨oldZero,hEarlier⟩,?_⟩
  rw [hOldLSelected,hOldLAux]
  decide

/-- The ACTUAL two Kpt node old dependent L+ records are distinct,
provided they are represented by the two named finite physical
original types in the numerical old0 positive/negative scenario.

No claim is made that arbitrary meet/parameter pairs satisfy these
raw-type representation hypotheses, or that all full I2 is absent. -/
theorem kpt_old_raw_types_distinct_of_named_numeric_originals
    {family : List (NormalizedForbidden 1 0 1)}
    (zSelected zAux : AdmissibleKptNode family)
    (E : Nat → Nat → Bool)
    (k N old cutBase selected aux g m : Nat)
    (hOldCut : old < cutBase)
    (hCutSelected : cutBase < selected)
    (hCutAux : cutBase < aux)
    (hg : g ≤ k) (hm : m ≤ k)
    (hPositive : E old selected = true)
    (hNegative : E old aux = false)
    (hCutIn : hPosition k cutBase g < N)
    (selectedName auxName : Fin N)
    (hSelectedName : selectedName.val = hPosition k selected k)
    (hAuxName : auxName.val = hPosition k aux m)
    (hRawSelected :
      kptFullOldAtCut zSelected (hPosition k cutBase g) =
        some (⟨hPosition k cutBase g,
          (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
            (hPosition k cutBase g) selectedName.val⟩ :
          RawPartialTypeNode 1 0 1))
    (hRawAux :
      kptFullOldAtCut zAux (hPosition k cutBase g) =
        some (⟨hPosition k cutBase g,
          (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
            (hPosition k cutBase g) auxName.val⟩ :
          RawPartialTypeNode 1 0 1)) :
    kptFullOldAtCut zSelected (hPosition k cutBase g) ≠
      kptFullOldAtCut zAux (hPosition k cutBase g) := by
  exact kpt_old_ordinary_bit_separation_forces_full_old_distinct
    zSelected zAux (hPosition k cutBase g)
    (kpt_old_ordinary_bit_certificate_of_named_numeric_originals
      zSelected zAux E k N old cutBase selected aux g m
      hOldCut hCutSelected hCutAux hg hm hPositive hNegative
      hCutIn selectedName auxName hSelectedName hAuxName
      hRawSelected hRawAux)

#print axioms kpt_old_ordinary_bit_certificate_of_named_numeric_originals
#print axioms kpt_old_raw_types_distinct_of_named_numeric_originals

end Kk
