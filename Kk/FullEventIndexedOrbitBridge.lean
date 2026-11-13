import Kk.FullLabelledOrbitBridge
import SuccessorTree.V10.KptStageClosureNormalForm

/-!
# Track E: event-indexed full-source comparison by physical closure recipes

This strengthens the earlier flat source-record interface. Actual
Algorithm-5.4 source tests use PER-CUT source participation and complete
old/upper L+ type assignments, and event incidence matters in addition
to its I1/I2/I3/B3 kind. The event index must be the fully synchronized
event/microevent sequence, NOT merely the macrodiary.

This is a strict *conditional* source uniqueness theorem. Normal-form
recipes do not magically exist: Track C must provide genuine names and
certify actual seed/positive parameter/compatible-meet normal forms,
while D must compare full event traces. The two occurrence maps are
genuine Kpt monoid maps. No numeric H+ assumptions are discharged here.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The complete data compared at one compressed source event.

The cut is in *source* coordinates; target numerical gaps may differ.
The ordered inputs retain which selected vertex or auxiliary parameter
participates in this event. A successor-character payload can include
the complete ordered tuple of dependencies if needed by the concrete
numerical H+ construction. -/
structure FullSourceEventFrame
    (Labels Parameters Kind Character : Type) where
  compressedSourceCut : Nat
  kind : Kind
  orderedInputs : List (Sum Labels Parameters)
  successorCharacter : Character

/-- A complete synchronized algorithm trace must retain source
presence and assigned old/upper types **at every event**.

The index Events must include all auxiliary I1/I2/I3/B3 microevents.
The actual meaning of Old, Upper, Kind and Character must be supplied
by the physical H+ source; generic payload types do not certify this.
-/
structure FullEventIndexedSourceRecord
    (Labels Parameters SelectedNodes ParameterNodes Old Upper
      Events Kind Character : Type) where
  selected : Labels → SelectedNodes
  parameters : Parameters → ParameterNodes
  presentAt : Events → Sum Labels Parameters → Bool
  oldAt : Events → Sum Labels Parameters → Old
  upperAt : Events → Sum Labels Parameters → Upper
  eventFrame : Events → FullSourceEventFrame Labels Parameters Kind Character

theorem fullEventIndexedSourceRecord_ext
    {Labels Parameters SelectedNodes ParameterNodes Old Upper
      Events Kind Character : Type}
    {R S : FullEventIndexedSourceRecord Labels Parameters
      SelectedNodes ParameterNodes Old Upper Events Kind Character}
    (hSelected : R.selected = S.selected)
    (hParameters : R.parameters = S.parameters)
    (hPresent : R.presentAt = S.presentAt)
    (hOld : R.oldAt = S.oldAt)
    (hUpper : R.upperAt = S.upperAt)
    (hEvents : R.eventFrame = S.eventFrame) : R = S := by
  cases R with
  | mk sr pr ar or ur er =>
    cases S with
    | mk ss ps as os us es =>
      cases hSelected
      cases hParameters
      cases hPresent
      cases hOld
      cases hUpper
      cases hEvents
      rfl

/-- Physical source-atom indices are kept separate: selected original
parameters may include positive free-cut nodes distinct from initial
seeds and from arbitrary ambient originals used in meet witnesses. -/
structure KptSourceAtomAssignment
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Seeds Positives Originals : Type) where
  seed : Seeds → AdmissibleKptNode family
  positiveParameter : Positives → AdmissibleKptNode family
  ambientOriginal : Originals → AdmissibleKptNode family

/-- Track-C's three normal-form constructors. These are syntactic
recipes; meeting two incompatible nodes is not certified until the
separate SameComponent premise below is checked. -/
inductive KptClosureRecipe (Seeds Positives Originals : Type)
  | seed (s : Seeds)
  | positive (p : Positives)
  | meetOf (u v : Originals)

namespace KptClosureRecipe

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}
variable {Seeds Positives Originals : Type}

noncomputable def evaluate
    (atoms : KptSourceAtomAssignment family Seeds Positives Originals) :
    KptClosureRecipe Seeds Positives Originals →
      AdmissibleKptNode family
  | .seed s => atoms.seed s
  | .positive p => atoms.positiveParameter p
  | .meetOf u v =>
      LevelTree.meet (atoms.ambientOriginal u) (atoms.ambientOriginal v)

/-- The normal-form meet case is geometrically legitimate only with
the actual SameComponent certificate. -/
def WellFormed
    (atoms : KptSourceAtomAssignment family Seeds Positives Originals) :
    KptClosureRecipe Seeds Positives Originals → Prop
  | .seed _ => True
  | .positive _ => True
  | .meetOf u v =>
      SMTree.Envelope.SameComponent
        (atoms.ambientOriginal u) (atoms.ambientOriginal v)

theorem evaluate_congr
    {A B : KptSourceAtomAssignment family Seeds Positives Originals}
    (hAtoms : A = B)
    (r : KptClosureRecipe Seeds Positives Originals) :
    evaluate A r = evaluate B r := by
  cases hAtoms
  rfl

theorem wellFormed_congr
    {A B : KptSourceAtomAssignment family Seeds Positives Originals}
    (hAtoms : A = B)
    (r : KptClosureRecipe Seeds Positives Originals) :
    WellFormed A r ↔ WellFormed B r := by
  cases hAtoms
  rfl

end KptClosureRecipe

/-- All event-indexed source values are in the *same* genuine Kpt/G+
source presentation. This does not assert that arbitrary event payloads
really arise from the numerical construction. -/
abbrev KptEventIndexedSourceRecord
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (n : Nat) (Parameters Old Upper Events Kind Character : Type) :=
  FullEventIndexedSourceRecord
    (Fin n) Parameters (FiniteGPlusVertex family)
    (AdmissibleKptNode family) Old Upper Events Kind Character

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- Cross-occurrence comparison from an unlabelled selected inverse set
and identical **physical closure recipes**, rather than equal singleton
inverse fibres for every derived dependent Kpt parameter.

The meet certificates are explicitly returned on the second side:
a purely syntactic "meet" label without SameComponent is not valid
closure geometry. Old/upper assignments and full event frames must
still be checked at **every** synchronized microevent. -/
theorem full_event_source_eq_of_inverse_sets_and_recipes
    {n : Nat} {Parameters Old Upper Events Kind Character : Type}
    {Seeds Positives Originals : Type}
    (F G : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (R S : KptEventIndexedSourceRecord family n
      Parameters Old Upper Events Kind Character)
    (targetF targetG : Fin n → FiniteGPlusVertex family)
    (hSelectedF : ∀ a, gPlusShapeImage F.map (R.selected a) = targetF a)
    (hSelectedG : ∀ a, gPlusShapeImage G.map (S.selected a) = targetG a)
    (hStrictF : ∀ a b : Fin n, a < b →
      (targetF a).IsProperPrefix (targetF b))
    (hStrictG : ∀ a b : Fin n, a < b →
      (targetG a).IsProperPrefix (targetG b))
    (hInverse :
      (gPlusShapeImage F.map) ⁻¹' (Set.range targetF) =
      (gPlusShapeImage G.map) ⁻¹' (Set.range targetG))
    (atomsF atomsG :
      KptSourceAtomAssignment family Seeds Positives Originals)
    (recipes : Parameters → KptClosureRecipe Seeds Positives Originals)
    (hRecipeF : ∀ p,
      R.parameters p = (recipes p).evaluate atomsF)
    (hRecipeG : ∀ p,
      S.parameters p = (recipes p).evaluate atomsG)
    (hAtoms : atomsF = atomsG)
    (hWellFormedF : ∀ p,
      (recipes p).WellFormed atomsF)
    (hPresent : R.presentAt = S.presentAt)
    (hOld : R.oldAt = S.oldAt)
    (hUpper : R.upperAt = S.upperAt)
    (hEvents : R.eventFrame = S.eventFrame) :
    R = S ∧ ∀ p, (recipes p).WellFormed atomsG := by
  have hSelected : R.selected = S.selected :=
    labelled_prefix_sources_eq_of_inverse_image_sets
      F G targetF targetG R.selected S.selected
      hSelectedF hSelectedG hStrictF hStrictG hInverse
  have hParameters : R.parameters = S.parameters := by
    funext p
    calc
      R.parameters p = (recipes p).evaluate atomsF := hRecipeF p
      _ = (recipes p).evaluate atomsG :=
        KptClosureRecipe.evaluate_congr hAtoms (recipes p)
      _ = S.parameters p := (hRecipeG p).symm
  constructor
  · exact fullEventIndexedSourceRecord_ext
      hSelected hParameters hPresent hOld hUpper hEvents
  · intro p
    exact ((KptClosureRecipe.wellFormed_congr
      hAtoms (recipes p)).mp (hWellFormedF p))

/-- Extract only the selected Kpt/G+ data needed by the **already
checked** finite type-respecting Ramsey transfer. This forgetful map
is for the Ramsey step only; it cannot justify claiming that a
flat record has verified all of the full per-event L+ geometry. -/
def KptEventIndexedSourceRecord.orbitProjection
    {n : Nat} {Parameters Old Upper Events Kind Character : Type}
    (R : KptEventIndexedSourceRecord family n Parameters
      Old Upper Events Kind Character) :
    KptFullSourceRecord family n Parameters Unit Unit Unit Unit := {
  selected := R.selected
  parameters := R.parameters
  oldTypes := fun _ => ()
  upperTypes := fun _ => ()
  eventKinds := fun _ => ()
}

/-- Once actual full time-indexed records are coherent for each
diary, the already verified uniform prefix-chain Ramsey reduction
applies to their selected source projections. In particular no
additional countable-source theorem is needed. -/
theorem full_event_source_coherence_implies_diary_colour_bound
    {n : Nat} {ι κ Parameters Old Upper Events Kind Character : Type}
    [Fintype κ] [Nonempty κ]
    (enum : Nat ≃ FiniteGPlusVertex family)
    (diaryIndices : Finset ι)
    (sources : ι → KptEventIndexedSourceRecord family n
      Parameters Old Upper Events Kind Character)
    (tops : ι → FiniteGPlusVertex family)
    (hPrefix : ∀ i a, ((sources i).selected a).val.IsPrefix (tops i).val)
    (hInjective : ∀ i, Function.Injective (sources i).selected)
    (diary : LabelledGOmegaCopy (Fin n) → ι)
    (selected : Set (LabelledGOmegaCopy (Fin n)))
    (hIndexed : ∀ e, e ∈ selected → diary e ∈ diaryIndices)
    (pulledBack : LabelledGOmegaCopy (Fin n) →
      KptEventIndexedSourceRecord family n Parameters
        Old Upper Events Kind Character)
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
  apply full_source_coherence_implies_diary_colour_bound
    enum diaryIndices
    (fun i => (sources i).orbitProjection)
    tops hPrefix hInjective
    diary selected hIndexed
    (fun e => (pulledBack e).orbitProjection)
    envelope hImage ?_ colour
  intro e he
  rw [hCoherent e he]

/-- Negative regression: event-kind equality does not identify
source participation. Two genuine event *records* can have identical
kinds but different selected/parameter source names. -/
theorem event_kind_does_not_determine_inputs :
    ∃ A B : FullSourceEventFrame Unit Unit Unit Unit,
      A.kind = B.kind ∧ A ≠ B := by
  refine ⟨
    { compressedSourceCut := 0, kind := (),
      orderedInputs := [Sum.inl ()], successorCharacter := () },
    { compressedSourceCut := 0, kind := (),
      orderedInputs := [Sum.inr ()], successorCharacter := () },
    rfl, ?_⟩
  intro h
  have hInputs := congrArg FullSourceEventFrame.orderedInputs h
  cases hInputs

/-- Negative regression: a common source, equal initial types,
parameter presence and event frames can still hide a different
second-cut assigned upper L+ type. -/
private def toyCutRecord (b : Bool) :
    FullEventIndexedSourceRecord Unit Unit Unit Unit
      Unit Bool Bool Unit Unit := {
  selected := fun _ => ()
  parameters := fun _ => ()
  presentAt := fun _ _ => true
  oldAt := fun _ _ => ()
  upperAt := fun e _ => if e then b else false
  eventFrame := fun _ => {
    compressedSourceCut := 0
    kind := ()
    orderedInputs := []
    successorCharacter := () }
}

theorem assigned_upper_type_requires_event_indexing :
    (toyCutRecord false).selected = (toyCutRecord true).selected ∧
    (toyCutRecord false).parameters = (toyCutRecord true).parameters ∧
    (toyCutRecord false).presentAt = (toyCutRecord true).presentAt ∧
    (toyCutRecord false).oldAt = (toyCutRecord true).oldAt ∧
    (toyCutRecord false).eventFrame = (toyCutRecord true).eventFrame ∧
    (toyCutRecord false).upperAt ≠ (toyCutRecord true).upperAt := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro h
  have hv := congrArg (fun f => f true (Sum.inl ())) h
  cases hv


/-- A literal finite-index source trace: all selected labels, named
parameters and event/microevent ranks are finite. To use this alias
for the manuscript, Tracks C/D must provide a **uniform** size or a
canonical padding convention across the compared diary occurrences. -/
abbrev KptFiniteEventSourceRecord
    {db du dd : Nat} (family : List (NormalizedForbidden db du dd))
    (n nParams nEvents : Nat) (Old Upper Kind Character : Type) :=
  KptEventIndexedSourceRecord family n (Fin nParams) Old Upper
    (Fin nEvents) Kind Character

/-- Disjointly-typed lookup of the *actual* source node for a selected
label or a named dependent Kpt parameter. It retains which of the two
kinds of source is being requested. -/
def KptEventIndexedSourceRecord.namedNode
    {n : Nat} {Parameters Old Upper Events Kind Character : Type}
    (R : KptEventIndexedSourceRecord family n
      Parameters Old Upper Events Kind Character) :
    Sum (Fin n) Parameters →
      Sum (FiniteGPlusVertex family) (AdmissibleKptNode family)
  | .inl a => .inl (R.selected a)
  | .inr p => .inr (R.parameters p)

/-- Physical local-reconstruction bridge: full synchronized event frames
and equal source nodes imply equality of assigned old/upper L+ types
IF both actual numerical presentations use the same deterministic
assignment functions on their full event frames and named source nodes.

The reconstruction premise is not known from equality of old source
types or B3 verdicts; it must reflect actual chosen upper successor
characters, including auxiliary E. This theorem is independent of
finite H+, and does not discharge that premise. -/
theorem full_event_source_eq_of_local_reconstruction
    {n : Nat} {Parameters Old Upper Events Kind Character : Type}
    (R S : KptEventIndexedSourceRecord family n
      Parameters Old Upper Events Kind Character)
    (hSelected : R.selected = S.selected)
    (hParams : R.parameters = S.parameters)
    (hPresent : R.presentAt = S.presentAt)
    (hFrames : R.eventFrame = S.eventFrame)
    (recoverOld : Events →
      FullSourceEventFrame (Fin n) Parameters Kind Character →
      Sum (FiniteGPlusVertex family) (AdmissibleKptNode family) → Old)
    (recoverUpper : Events →
      FullSourceEventFrame (Fin n) Parameters Kind Character →
      Sum (FiniteGPlusVertex family) (AdmissibleKptNode family) → Upper)
    (hOldR : ∀ j x,
      R.oldAt j x = recoverOld j (R.eventFrame j) (R.namedNode x))
    (hOldS : ∀ j x,
      S.oldAt j x = recoverOld j (S.eventFrame j) (S.namedNode x))
    (hUpperR : ∀ j x,
      R.upperAt j x = recoverUpper j (R.eventFrame j) (R.namedNode x))
    (hUpperS : ∀ j x,
      S.upperAt j x = recoverUpper j (S.eventFrame j) (S.namedNode x)) :
    R = S := by
  have hNodes : R.namedNode = S.namedNode := by
    funext x
    cases x with
    | inl a =>
      change Sum.inl (R.selected a) = Sum.inl (S.selected a)
      exact congrArg Sum.inl (congrFun hSelected a)
    | inr p =>
      change Sum.inr (R.parameters p) = Sum.inr (S.parameters p)
      exact congrArg Sum.inr (congrFun hParams p)
  have hOldAt : R.oldAt = S.oldAt := by
    funext j x
    calc
      R.oldAt j x = recoverOld j (R.eventFrame j) (R.namedNode x) :=
        hOldR j x
      _ = recoverOld j (S.eventFrame j) (S.namedNode x) := by
        rw [hFrames, hNodes]
      _ = S.oldAt j x := (hOldS j x).symm
  have hUpperAt : R.upperAt = S.upperAt := by
    funext j x
    calc
      R.upperAt j x = recoverUpper j (R.eventFrame j) (R.namedNode x) :=
        hUpperR j x
      _ = recoverUpper j (S.eventFrame j) (S.namedNode x) := by
        rw [hFrames, hNodes]
      _ = S.upperAt j x := (hUpperS j x).symm
  exact fullEventIndexedSourceRecord_ext
    hSelected hParams hPresent hOldAt hUpperAt hFrames

/-- A physically named common source span: the same **genuine**
selected G+ labels and every named dependent Kpt parameter must map
to the stated target selected vertices / parameter nodes under the
two monoid maps. This is stronger than a source-only equality or an
unlabelled minimal-envelope isomorphism. It is still conditional on
the input maps and actual target-node transport checks. -/
theorem full_event_source_common_selected_and_parameter_targets
    {n : Nat} {Parameters Old Upper Events Kind Character : Type}
    (F G : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (R S : KptEventIndexedSourceRecord family n
      Parameters Old Upper Events Kind Character)
    (targetF targetG : Fin n → FiniteGPlusVertex family)
    (targetParamF targetParamG : Parameters → AdmissibleKptNode family)
    (hInjF : Function.Injective targetF)
    (hInjG : Function.Injective targetG)
    (hRecord : R = S)
    (hSelectedF : ∀ a, gPlusShapeImage F.map (R.selected a) = targetF a)
    (hSelectedG : ∀ a, gPlusShapeImage G.map (S.selected a) = targetG a)
    (hParamF : ∀ p, F.map (R.parameters p) = targetParamF p)
    (hParamG : ∀ p, G.map (S.parameters p) = targetParamG p) :
    ∃ (source : LabelledGPlusCopy family (Fin n))
      (sourceParameters : Parameters → AdmissibleKptNode family),
      LabelledGPlusCopy.map F source =
        (⟨targetF, hInjF⟩ : LabelledGPlusCopy family (Fin n)) ∧
      LabelledGPlusCopy.map G source =
        (⟨targetG, hInjG⟩ : LabelledGPlusCopy family (Fin n)) ∧
      (∀ p, F.map (sourceParameters p) = targetParamF p) ∧
      (∀ p, G.map (sourceParameters p) = targetParamG p) := by
  have hFlat : R.orbitProjection = S.orbitProjection :=
    congrArg
      (fun T : KptEventIndexedSourceRecord family n Parameters
        Old Upper Events Kind Character => T.orbitProjection) hRecord
  obtain ⟨source, hF, hG⟩ :=
    common_labelled_orbit_of_full_record_eq
      F G R.orbitProjection S.orbitProjection
      targetF targetG hInjF hInjG hFlat
      hSelectedF hSelectedG
  have hParams : R.parameters = S.parameters :=
    congrArg
      (fun T : KptEventIndexedSourceRecord family n Parameters
        Old Upper Events Kind Character => T.parameters) hRecord
  refine ⟨source, R.parameters, hF, hG, hParamF, ?_⟩
  intro p
  rw [hParams]
  exact hParamG p



/-- Non-vacuous completeness certificate for a genuinely physical
Algorithm-5.4 source: EVERY node of the actual parameter-closed Kpt
source at a synchronized cut must occur as one of the named, active
dependent source parameters, and every named active parameter must
really belong to that closure.

This is an *additional geometric hypothesis*, not a field automatically
true of an arbitrary event-indexed record. In particular an empty
parameter index does not certify a nonempty actual source closure. -/
def KptEventIndexedSourceRecord.CoversParameterClosure
    {n : Nat} {Parameters Old Upper Events Kind Character : Type}
    (R : KptEventIndexedSourceRecord family n
      Parameters Old Upper Events Kind Character)
    (actualClosure : Events → Set (AdmissibleKptNode family)) : Prop :=
  ∀ (j : Events) (z : AdmissibleKptNode family),
    z ∈ actualClosure j ↔
      ∃ p : Parameters,
        R.presentAt j (Sum.inr p) = true ∧ R.parameters p = z

/-- Full-record equality **plus independent physical coverage** implies
literal equality of the entire actual source parameter closures at
every synchronized cut. This does not follow from equality of a
possibly incomplete family of named nodes and does not identify target
envelopes without actual monoid transport. -/
theorem full_record_and_coverage_identify_source_closures
    {n : Nat} {Parameters Old Upper Events Kind Character : Type}
    (R S : KptEventIndexedSourceRecord family n
      Parameters Old Upper Events Kind Character)
    (actualR actualS : Events → Set (AdmissibleKptNode family))
    (hRecord : R = S)
    (hR : R.CoversParameterClosure actualR)
    (hS : S.CoversParameterClosure actualS) :
    actualR = actualS := by
  cases hRecord
  funext j
  ext z
  exact (hR j z).trans (hS j z).symm


end Kk
