import Kk.NumericHFullSelectedColumn
import Kk.HBlockNonedges
import Mathlib.Tactic

/-!
# Track D: old generation-zero numeric bit separates complete L+ source types

English-first proof with 17 hostile checks:
docs/audits/2026-11-16-track-d-generation-zero-separator-english.md

For an ACTUAL old Q vertex v and a tested real cut at a later base i,
the generation-zero H copy v₀ is numerically BEFORE the tested cut.
If v sees one future selected TOP base j, but not a later auxiliary base b,
then the literal numerical H relation has a positive old-to-j-top
ordinary L bit and a negative old-to-b-m bit for EVERY m≤k.

The bit at v₀ already distinguishes their COMPLETE old L-prefix
records, hence their entire dependent old L+ source types.
No invented auxiliary E on an L-only witness, no selected-age shadow,
and no global no-I2/boringness claim.
-/

namespace Kk

open SuccessorTree.V10

/-- One actual ordinary L bit at an old coordinate STRICTLY
below a cut separates the two COMPLETE dependent old L+ types,
including all negative ordinary and auxiliary E atoms.

No Kpt-eligibility/source-closure hypothesis follows from this
equality test; that remains a separate application obligation. -/
theorem finiteOldFullTypes_ne_of_distinguishing_L_bit
    (A : EnumeratedPartialStructure 1 0 1)
    (cut old x y : Nat)
    (hOld : old < cut)
    (hPositive : A.L.binary old x (0 : Fin 1) = true)
    (hNegative : A.L.binary old y (0 : Fin 1) = false) :
    A.partialTypeAt cut x ≠ A.partialTypeAt cut y := by
  intro hEqual
  have hReduct :
      (A.partialTypeAt cut x).lReduct =
        (A.partialTypeAt cut y).lReduct :=
    congrArg (fun T : PartialTypeWithE cut 1 0 1 => T.lReduct)
      hEqual
  have hLeft :
      (A.partialTypeAt cut x).lReduct =
        RelationalPrefixType.ofAgeModel A.L cut x :=
    partialTypeAt_lReduct_eq_ofAgeModel A cut x
  have hRight :
      (A.partialTypeAt cut y).lReduct =
        RelationalPrefixType.ofAgeModel A.L cut y :=
    partialTypeAt_lReduct_eq_ofAgeModel A cut y
  rw [hLeft, hRight] at hReduct
  have hBit := congrArg
    (fun T : RelationalPrefixType cut 1 0 1 =>
      T.binary (some (⟨old,hOld⟩ : Fin cut)) none (0 : Fin 1))
    hReduct
  change A.L.binary old x (0 : Fin 1) =
    A.L.binary old y (0 : Fin 1) at hBit
  rw [hPositive,hNegative] at hBit
  cases hBit

/-- At a genuine finite numerical H lower source cut,
a generation-zero copy of an old Q vertex physically separates
the COMPLETE dependent old L+ source types of:
* a selected later TOP-generation coding original with positive
  old Q edge, and
* a later auxiliary original of ANY bounded generation with a
  negative old Q edge.

The required original-base chronology is explicit. The source
name/parameter closure membership is NOT inferred from these
ordinary-L bits. -/
theorem finiteNumericH_old_zero_separates_top_from_negative
    (E : Nat → Nat → Bool)
    (k N old cutBase selected aux g m : Nat)
    (hOldCut : old < cutBase)
    (hCutSelected : cutBase < selected)
    (hCutAux : cutBase < aux)
    (hg : g ≤ k) (hm : m ≤ k)
    (hPositive : E old selected = true)
    (hNegative : E old aux = false) :
    let cut := hPosition k cutBase g
    let oldZero := hPosition k old 0
    let selectedTop := hPosition k selected k
    let auxCopy := hPosition k aux m
    oldZero < cut ∧ cut < selectedTop ∧ cut < auxCopy ∧
      (finiteNumericHL (normalizedGraphModel E) k N).binary
        oldZero selectedTop (0 : Fin 1) = true ∧
      (finiteNumericHL (normalizedGraphModel E) k N).binary
        oldZero auxCopy (0 : Fin 1) = false ∧
      (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
        cut selectedTop ≠
      (finiteNumericH (normalizedGraphModel E) k N).partialTypeAt
        cut auxCopy := by
  classical
  intro cut oldZero selectedTop auxCopy
  let A : EnumeratedPartialStructure 1 0 1 :=
    finiteNumericH (normalizedGraphModel E) k N
  have hEarlier : oldZero < cut :=
    hPosition_lt_of_block_lt
      k old cutBase 0 g (Nat.zero_le k) hOldCut
  have hTopLater : cut < selectedTop :=
    hPosition_lt_of_block_lt
      k cutBase selected g k hg hCutSelected
  have hAuxLater : cut < auxCopy :=
    hPosition_lt_of_block_lt
      k cutBase aux g m hg hCutAux
  have hOldSelected : old < selected :=
    hOldCut.trans hCutSelected
  have hOldAux : old < aux :=
    hOldCut.trans hCutAux
  have hPos :
      A.L.binary oldZero selectedTop (0 : Fin 1) = true := by
    change hNumericBinary (normalizedGraphModel E).binary k
      (hPosition k old 0) (hPosition k selected k)
      (0 : Fin 1) = true
    rw [numericH_older_generation_to_top_exact
      (normalizedGraphModel E).binary k old selected 0
      (0 : Fin 1) hOldSelected (Nat.zero_le k)]
    change E old selected = true
    exact hPositive
  have hNeg :
      A.L.binary oldZero auxCopy (0 : Fin 1) = false := by
    exact finiteNumericH_preserves_original_nonedge
      (normalizedGraphModel E) k N old aux 0 m
      hOldAux (Nat.zero_le k) hm
      (by
        intro t
        fin_cases t
        change E old aux = false
        exact hNegative)
      (0 : Fin 1)
  have hFullNe :
      A.partialTypeAt cut selectedTop ≠
        A.partialTypeAt cut auxCopy :=
    finiteOldFullTypes_ne_of_distinguishing_L_bit
      A cut oldZero selectedTop auxCopy hEarlier hPos hNeg
  exact ⟨hEarlier,hTopLater,hAuxLater,hPos,hNeg,hFullNe⟩

#print axioms finiteOldFullTypes_ne_of_distinguishing_L_bit
#print axioms finiteNumericH_old_zero_separates_top_from_negative

end Kk
