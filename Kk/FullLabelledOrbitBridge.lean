import Kk.OrderedSourceIdentification
import Kk.PrefixChainOrbitTransfer

/-!
# Track E: conditional full-labelled inverse-source and monoid-orbit bridge

This module deliberately separates three assertions.

* A *complete* record includes selected vertices, every named auxiliary
  parameter node, old and upper types on all named positions, and the
  interesting-level / microdiary event values.
* For two actual monoid maps, equality of selected inverse-image sets,
  named parameter singleton fibres, and all type/event assignments implies
  literal equality of the entire labelled source records.
* If every occurrence of a diary has the same actual full source record,
  the already proved prefix-chain Ramsey transfer gives diary-dependent
  colourings. This third theorem DOES NOT establish its coherence premise.

The numerical-H+ construction, corrected B3 classification, actual
envelope maps, and cross-occurrence inverse-image comparisons remain
geometric obligations of the KK manuscript / Tracks B--D. None are axioms
introduced by this file.
-/

namespace Kk

open SuccessorTree.V10

/-- A *literal* source record over one fixed set of label/parameter/event
indices. The two type assignments include both selected and parameter
positions; the event function must include nonstructural microevents.

To instantiate this record for numerical H+, the parameter index set
must enumerate *all* parameter-closed nodes inspected by I1/I2/I3/B3,
not just the selected original vertices. -/
structure FullLabelledSourceRecord
    (Labels Parameters SelectedNodes ParameterNodes Old Upper Events EventKind : Type)
    where
  selected : Labels → SelectedNodes
  parameters : Parameters → ParameterNodes
  oldTypes : Sum Labels Parameters → Old
  upperTypes : Sum Labels Parameters → Upper
  eventKinds : Events → EventKind

/-- Explicit literal-record extensionality: no selected-set shadow can
replace any of the five hypotheses. -/
theorem fullLabelledSourceRecord_ext
    {Labels Parameters SelectedNodes ParameterNodes Old Upper Events EventKind : Type}
    {R S : FullLabelledSourceRecord Labels Parameters SelectedNodes
      ParameterNodes Old Upper Events EventKind}
    (hs : R.selected = S.selected)
    (hp : R.parameters = S.parameters)
    (ho : R.oldTypes = S.oldTypes)
    (hu : R.upperTypes = S.upperTypes)
    (he : R.eventKinds = S.eventKinds) : R = S := by
  cases R with
  | mk rSel rPar rOld rUpper rEvents =>
    cases S with
    | mk sSel sPar sOld sUpper sEvents =>
      cases hs
      cases hp
      cases ho
      cases hu
      cases he
      rfl

/-- The actual Kpt/G+ source record, with abstract (but total) old,
upper and event payloads to be supplied by the numerical construction. -/
abbrev KptFullSourceRecord
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (n : Nat) (Parameters Old Upper Events EventKind : Type) :=
  FullLabelledSourceRecord (Fin n) Parameters
    (FiniteGPlusVertex family) (AdmissibleKptNode family)
    Old Upper Events EventKind

universe u v w

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- Equality of *complete* inverse-source records under two genuine Kpt
monoid maps. Only the named parameter-fibre injectivity is assumed here,
rather than importing a numerical-H-specific injectivity lemma.

Selected labels are recovered from the (unlabelled) selected inverse
sets using proper-prefix reflection; parameters are recovered from
their named singleton fibres. The remaining FULL type/event assignments
are explicit independent premises. -/
theorem full_source_records_eq_of_inverse_comparison
    {n : Nat} {Params Old Upper Events EventKind : Type}
    (F G : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (R S : KptFullSourceRecord family n Params Old Upper Events EventKind)
    (targetF targetG : Fin n → FiniteGPlusVertex family)
    (paramF paramG : Params → AdmissibleKptNode family)
    (hSelectedF : ∀ a, gPlusShapeImage F.map (R.selected a) = targetF a)
    (hSelectedG : ∀ a, gPlusShapeImage G.map (S.selected a) = targetG a)
    (hStrictF : ∀ a b : Fin n, a < b →
      (targetF a).IsProperPrefix (targetF b))
    (hStrictG : ∀ a b : Fin n, a < b →
      (targetG a).IsProperPrefix (targetG b))
    (hSelectedInverse :
      (gPlusShapeImage F.map) ⁻¹' (Set.range targetF) =
      (gPlusShapeImage G.map) ⁻¹' (Set.range targetG))
    (hParameterF : ∀ p, F.map (R.parameters p) = paramF p)
    (hParameterG : ∀ p, G.map (S.parameters p) = paramG p)
    (hParameterInjective : Function.Injective G.map)
    (hParameterInverse : ∀ p,
      F.map ⁻¹' ({paramF p} : Set (AdmissibleKptNode family)) =
      G.map ⁻¹' ({paramG p} : Set (AdmissibleKptNode family)))
    (hOld : R.oldTypes = S.oldTypes)
    (hUpper : R.upperTypes = S.upperTypes)
    (hEvents : R.eventKinds = S.eventKinds) :
    R = S := by
  have hSelected : R.selected = S.selected :=
    labelled_prefix_sources_eq_of_inverse_image_sets
      F G targetF targetG R.selected S.selected
      hSelectedF hSelectedG hStrictF hStrictG hSelectedInverse
  have hParameters : R.parameters = S.parameters := by
    funext p
    apply hParameterInjective
    have hMem :
        R.parameters p ∈
          F.map ⁻¹' ({paramF p} : Set (AdmissibleKptNode family)) := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff]
        using hParameterF p
    rw [hParameterInverse p] at hMem
    have hImage : G.map (R.parameters p) = paramG p := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hMem
    exact hImage.trans (hParameterG p).symm
  exact fullLabelledSourceRecord_ext
    hSelected hParameters hOld hUpper hEvents

/-- Equal full source records yield one common labelled *outgoing*
monoid source for both target copies. This is a concrete equality in
the actual G+ presentation, not an abstract envelope isomorphism. -/
theorem common_labelled_orbit_of_full_record_eq
    {n : Nat} {Params Old Upper Events EventKind : Type}
    (F G : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (R S : KptFullSourceRecord family n Params Old Upper Events EventKind)
    (targetF targetG : Fin n → FiniteGPlusVertex family)
    (hTargetFInj : Function.Injective targetF)
    (hTargetGInj : Function.Injective targetG)
    (hRecord : R = S)
    (hSelectedF : ∀ a, gPlusShapeImage F.map (R.selected a) = targetF a)
    (hSelectedG : ∀ a, gPlusShapeImage G.map (S.selected a) = targetG a) :
    ∃ source : LabelledGPlusCopy family (Fin n),
      LabelledGPlusCopy.map F source =
        (⟨targetF, hTargetFInj⟩ : LabelledGPlusCopy family (Fin n)) ∧
      LabelledGPlusCopy.map G source =
        (⟨targetG, hTargetGInj⟩ : LabelledGPlusCopy family (Fin n)) := by
  have hSourceInj : Function.Injective R.selected := by
    intro a b hab
    apply hTargetFInj
    calc
      targetF a = gPlusShapeImage F.map (R.selected a) :=
        (hSelectedF a).symm
      _ = gPlusShapeImage F.map (R.selected b) :=
        congrArg (gPlusShapeImage F.map) hab
      _ = targetF b := hSelectedF b
  have hSourceEq : R.selected = S.selected :=
    congrArg (fun T : KptFullSourceRecord family n Params Old Upper Events EventKind =>
      T.selected) hRecord
  refine ⟨⟨R.selected, hSourceInj⟩, ?_, ?_⟩
  · apply Subtype.ext
    funext a
    change gPlusShapeImage F.map (R.selected a) = targetF a
    exact hSelectedF a
  · apply Subtype.ext
    funext a
    change gPlusShapeImage G.map (R.selected a) = targetG a
    rw [hSourceEq]
    exact hSelectedG a

/-- Uniform abstract Track-E endpoint: an actual, prefix-chain,
*canonical full record per diary* plus actual maps and coherence of the
whole source record produces the upper colouring statement.

The full-record coherence premise is exactly the missing resolved-H+
geometry. The finite full-profile carrier and Ramsey step are *derived*
by the existing verified prefix-chain transfer theorem. -/
theorem full_source_coherence_implies_diary_colour_bound
    {n : Nat} {ι κ Params Old Upper Events EventKind : Type}
    [Fintype κ] [Nonempty κ]
    (enum : Nat ≃ FiniteGPlusVertex family)
    (diaryIndices : Finset ι)
    (sources : ι → KptFullSourceRecord family n Params Old Upper Events EventKind)
    (tops : ι → FiniteGPlusVertex family)
    (hPrefix : ∀ i a, ((sources i).selected a).val.IsPrefix (tops i).val)
    (hInjective : ∀ i, Function.Injective (sources i).selected)
    (diary : LabelledGOmegaCopy (Fin n) → ι)
    (selected : Set (LabelledGOmegaCopy (Fin n)))
    (hIndexed : ∀ e, e ∈ selected → diary e ∈ diaryIndices)
    (pulledBack : LabelledGOmegaCopy (Fin n) →
      KptFullSourceRecord family n Params Old Upper Events EventKind)
    (envelope : LabelledGOmegaCopy (Fin n) →
      SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (hImage : ∀ e, e ∈ selected → ∀ a,
      enum.symm (gPlusShapeImage (envelope e).map
        ((pulledBack e).selected a)) = e.1 a)
    (hCoherent : ∀ e, e ∈ selected →
      pulledBack e = sources (diary e))
    (colour : LabelledGOmegaCopy (Fin n) → κ) :
    ∃ (F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
      (byDiary : ι → κ),
      ∀ e, e ∈ selected →
        colour (LabelledGOmegaCopy.map enum F e) =
          byDiary (diary e) := by
  classical
  apply prefix_chain_orbits_colour_factors
    enum diaryIndices tops (fun i => (sources i).selected)
    hPrefix hInjective diary selected hIndexed ?_ colour
  intro e he i hDiary
  have hSourceSelected :
      (pulledBack e).selected = (sources i).selected := by
    rw [hCoherent e he, hDiary]
  let source : LabelledGPlusCopy family (Fin n) :=
    ⟨(sources i).selected, hInjective i⟩
  have hGPlus :
      LabelledGPlusCopy.map (envelope e) source =
        LabelledGOmegaCopy.toGPlus enum e := by
    apply Subtype.ext
    funext a
    change gPlusShapeImage (envelope e).map
      ((sources i).selected a) = enum (e.1 a)
    apply enum.symm.injective
    have h := hImage e he a
    rw [hSourceSelected] at h
    simpa only [enum.symm_apply_apply] using h
  refine ⟨envelope e, ?_⟩
  change LabelledGOmegaCopy.map enum (envelope e)
      (LabelledGOmegaCopy.fromGPlus enum source) = e
  calc
    LabelledGOmegaCopy.map enum (envelope e)
        (LabelledGOmegaCopy.fromGPlus enum source) =
      LabelledGOmegaCopy.fromGPlus enum
        (LabelledGPlusCopy.map (envelope e) source) := by
          unfold LabelledGOmegaCopy.map
          rw [LabelledGOmegaCopy.toGPlus_fromGPlus]
    _ = LabelledGOmegaCopy.fromGPlus enum
          (LabelledGOmegaCopy.toGPlus enum e) := by rw [hGPlus]
    _ = e := LabelledGOmegaCopy.fromGPlus_toGPlus enum e


/-- A useful quantified form of the Track-E contract. It is enough to
compare all full source records pairwise within a diary class: choosing
one genuine representative for every realised diary then yields ONE
canonical labelled source and the conditional Ramsey upper bound.

The representative need not be a shortest occurrence, and is NOT used
as the common source itself: its *pulled-back* full record is. The
assumptions require the representative source prefix chains to have
genuine caps, while the same-diary record equality is still a
KK-specific geometric obligation. -/
theorem pairwise_full_source_comparison_implies_diary_colour_bound
    {n : Nat} {ι κ Params Old Upper Events EventKind : Type}
    [Fintype κ] [Nonempty κ]
    (enum : Nat ≃ FiniteGPlusVertex family)
    (diaryIndices : Finset ι)
    (diary : LabelledGOmegaCopy (Fin n) → ι)
    (selected : Set (LabelledGOmegaCopy (Fin n)))
    (hIndexed : ∀ e, e ∈ selected → diary e ∈ diaryIndices)
    (representative : ι → LabelledGOmegaCopy (Fin n))
    (hRep : ∀ i, i ∈ diaryIndices →
      representative i ∈ selected ∧ diary (representative i) = i)
    (pulledBack : LabelledGOmegaCopy (Fin n) →
      KptFullSourceRecord family n Params Old Upper Events EventKind)
    (tops : ι → FiniteGPlusVertex family)
    (hPrefix : ∀ i a,
      ((pulledBack (representative i)).selected a).val.IsPrefix (tops i).val)
    (hInjective : ∀ i,
      Function.Injective (pulledBack (representative i)).selected)
    (envelope : LabelledGOmegaCopy (Fin n) →
      SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (hImage : ∀ e, e ∈ selected → ∀ a,
      enum.symm (gPlusShapeImage (envelope e).map
        ((pulledBack e).selected a)) = e.1 a)
    (hPairwise : ∀ e, e ∈ selected → ∀ e', e' ∈ selected →
      diary e = diary e' → pulledBack e = pulledBack e')
    (colour : LabelledGOmegaCopy (Fin n) → κ) :
    ∃ (F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
      (byDiary : ι → κ),
      ∀ e, e ∈ selected →
        colour (LabelledGOmegaCopy.map enum F e) =
          byDiary (diary e) := by
  apply full_source_coherence_implies_diary_colour_bound
    enum diaryIndices (fun i => pulledBack (representative i))
    tops hPrefix hInjective diary selected hIndexed
    pulledBack envelope hImage ?_ colour
  intro e he
  have hRepresentative := hRep (diary e) (hIndexed e he)
  exact hPairwise e he (representative (diary e))
    hRepresentative.1 hRepresentative.2.symm

end Kk
