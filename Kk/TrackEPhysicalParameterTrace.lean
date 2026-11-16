import Kk.TrackEUsedRecipeEventReconstruction
import Kk.NumericHIndexedUpperRecords
import Mathlib.Tactic

/-!
# Track E E57: literal physical Kpt parameter traces at event cuts

For genuinely named dependent Kpt parameters, actual source membership
and same-node complete old/upper L+ raw ancestors give canonical
event-indexed presence and type records. There is no arbitrary
old/upper reconstruction oracle for THESE named dependent parameters.

The selected G+ labels remain a different sort and require their own
source representation. Equality of physical membership across distinct
diary occurrences, event-cut alignment and genuine monoid maps remain
open geometric obligations.

English first: docs/track_e_physical_param_trace_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- Physical faithfulness of the DEPENDENT Kpt parameter portion of
a full event record. An inactive parameter has neither old nor upper
raw L+ crossing type at that event. An active parameter gets both
actual raw ancestor records from the SAME admissible Kpt node. -/
def KptPhysicalParameterTrace
    {n : Nat} {Parameters Events Kind Character : Type}
    (R : KptEventIndexedSourceRecord family n Parameters
      (Option (RawPartialTypeNode db du dd))
      (Option (RawPartialTypeNode db du dd)) Events Kind Character)
    (actual : Events → Set (AdmissibleKptNode family)) : Prop :=
  (∀ e p, R.presentAt e (.inr p) = true ↔
    R.parameters p ∈ actual e) ∧
  (∀ e p, R.oldAt e (.inr p) =
    if R.presentAt e (.inr p) = true then
      kptFullOldAtCut (R.parameters p)
        (R.eventFrame e).compressedSourceCut
    else none) ∧
  (∀ e p, R.upperAt e (.inr p) =
    if R.presentAt e (.inr p) = true then
      kptFullUpperAtCut (R.parameters p)
        (R.eventFrame e).compressedSourceCut
    else none)

/-- Build a PHYSICAL full event-indexed record from actual Kpt
parameter nodes and their actual per-event membership sets. The
selected G+ label data is supplied independently: it is not
silently identified with the distinct Kpt parameter sort.

This is source data extracted from a physical finite run when
actual e is its full parameter-closed pre-cut source. It is NOT
an occurrence-independent diary canonicalizer. -/
noncomputable def kptPhysicalEventRecord
    {n : Nat} {Parameters Events Kind Character : Type}
    (selected : Fin n → FiniteGPlusVertex family)
    (parameters : Parameters → AdmissibleKptNode family)
    (actual : Events → Set (AdmissibleKptNode family))
    (frame : Events → FullSourceEventFrame (Fin n) Parameters
      Kind Character)
    (selectedPresent : Events → Fin n → Bool)
    (selectedOld selectedUpper :
      Events → Fin n → Option (RawPartialTypeNode db du dd)) :
    KptEventIndexedSourceRecord family n Parameters
      (Option (RawPartialTypeNode db du dd))
      (Option (RawPartialTypeNode db du dd)) Events Kind Character := by
  classical
  exact {
    selected := selected
    parameters := parameters
    presentAt := fun e x =>
      match x with
      | .inl a => selectedPresent e a
      | .inr p => decide (parameters p ∈ actual e)
    oldAt := fun e x =>
      match x with
      | .inl a => selectedOld e a
      | .inr p =>
          if parameters p ∈ actual e then
            kptFullOldAtCut (parameters p) (frame e).compressedSourceCut
          else none
    upperAt := fun e x =>
      match x with
      | .inl a => selectedUpper e a
      | .inr p =>
          if parameters p ∈ actual e then
            kptFullUpperAtCut (parameters p) (frame e).compressedSourceCut
          else none
    eventFrame := frame
  }

/-- The constructed physical trace IS faithful to the supplied
complete source membership sets, at every event and for every
named dependent Kpt parameter, with no extra source-type axiom. -/
theorem kptPhysicalEventRecord_has_parameter_trace
    {n : Nat} {Parameters Events Kind Character : Type}
    (selected : Fin n → FiniteGPlusVertex family)
    (parameters : Parameters → AdmissibleKptNode family)
    (actual : Events → Set (AdmissibleKptNode family))
    (frame : Events → FullSourceEventFrame (Fin n) Parameters
      Kind Character)
    (selectedPresent : Events → Fin n → Bool)
    (selectedOld selectedUpper :
      Events → Fin n → Option (RawPartialTypeNode db du dd)) :
    KptPhysicalParameterTrace
      (kptPhysicalEventRecord selected parameters actual frame
        selectedPresent selectedOld selectedUpper) actual := by
  classical
  constructor
  · intro e p
    simp [kptPhysicalEventRecord]
  constructor
  · intro e p
    by_cases hp : parameters p ∈ actual e
    · simp [kptPhysicalEventRecord, hp]
    · simp [kptPhysicalEventRecord, hp]
  · intro e p
    by_cases hp : parameters p ∈ actual e
    · simp [kptPhysicalEventRecord, hp]
    · simp [kptPhysicalEventRecord, hp]

/-- At every aligned physical event, equal named Kpt parameter nodes
and equivalent actual source membership imply equal presence bits
and BOTH complete raw old/upper dependent L+ fields.

This does not identify selected G+ labels or assert that all
actual closure nodes have been named by the parameter index. -/
theorem kpt_physical_parameter_fields_eq_of_membership
    {n : Nat} {Parameters Events Kind Character : Type}
    (R S : KptEventIndexedSourceRecord family n Parameters
      (Option (RawPartialTypeNode db du dd))
      (Option (RawPartialTypeNode db du dd)) Events Kind Character)
    (actualR actualS : Events → Set (AdmissibleKptNode family))
    (hParameters : R.parameters = S.parameters)
    (hFrames : R.eventFrame = S.eventFrame)
    (hPhysicalR : KptPhysicalParameterTrace R actualR)
    (hPhysicalS : KptPhysicalParameterTrace S actualS)
    (hMembership : ∀ e p,
      R.parameters p ∈ actualR e ↔
      S.parameters p ∈ actualS e) :
    (∀ e p, R.presentAt e (.inr p) =
       S.presentAt e (.inr p)) ∧
    (∀ e p, R.oldAt e (.inr p) =
       S.oldAt e (.inr p)) ∧
    (∀ e p, R.upperAt e (.inr p) =
       S.upperAt e (.inr p)) := by
  have hPresent : ∀ e p, R.presentAt e (.inr p) =
      S.presentAt e (.inr p) := by
    intro e p
    have hTrue :
        (R.presentAt e (.inr p) = true) ↔
        (S.presentAt e (.inr p) = true) :=
      (hPhysicalR.1 e p).trans
        ((hMembership e p).trans (hPhysicalS.1 e p).symm)
    cases hR : R.presentAt e (.inr p) <;>
      cases hS : S.presentAt e (.inr p) <;>
      simp_all
  refine ⟨hPresent, ?_, ?_⟩
  · intro e p
    calc
      R.oldAt e (.inr p) =
          (if R.presentAt e (.inr p) = true then
            kptFullOldAtCut (R.parameters p)
              (R.eventFrame e).compressedSourceCut
           else none) := hPhysicalR.2.1 e p
      _ = (if S.presentAt e (.inr p) = true then
            kptFullOldAtCut (S.parameters p)
              (S.eventFrame e).compressedSourceCut
           else none) := by
          rw [hPresent e p, congrFun hParameters p,
            congrFun hFrames e]
      _ = S.oldAt e (.inr p) := (hPhysicalS.2.1 e p).symm
  · intro e p
    calc
      R.upperAt e (.inr p) =
          (if R.presentAt e (.inr p) = true then
            kptFullUpperAtCut (R.parameters p)
              (R.eventFrame e).compressedSourceCut
           else none) := hPhysicalR.2.2 e p
      _ = (if S.presentAt e (.inr p) = true then
            kptFullUpperAtCut (S.parameters p)
              (S.eventFrame e).compressedSourceCut
           else none) := by
          rw [hPresent e p, congrFun hParameters p,
            congrFun hFrames e]
      _ = S.upperAt e (.inr p) := (hPhysicalS.2.2 e p).symm

/-- A more PHYSICAL E56 source-record interface. The selected G+
source tuples are identified by genuine prefix-chain inverse sets;
dependent parameter nodes are identified using ONLY actually USED
Kpt closure recipes; dependent physical activity and full old/upper
L+ assignments are derived from membership alignment and literal
raw Kpt ancestor operations.

The selected labels' activity and raw types are still distinct
explicit hypotheses; all physical event frames and source-coordinate
cuts must be synchronized. This does not supply the cross-occurrence
geometry from a macrodiary, nor construct a common monoid orbit. -/
theorem full_event_source_eq_of_used_recipes_and_physical_trace
    {n : Nat} {Parameters Events Kind Character : Type}
    {Seeds Positives Originals : Type}
    (F G : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (R S : KptEventIndexedSourceRecord family n Parameters
      (Option (RawPartialTypeNode db du dd))
      (Option (RawPartialTypeNode db du dd)) Events Kind Character)
    (targetF targetG : Fin n → FiniteGPlusVertex family)
    (hSelectedF : ∀ a,
      gPlusShapeImage F.map (R.selected a) = targetF a)
    (hSelectedG : ∀ a,
      gPlusShapeImage G.map (S.selected a) = targetG a)
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
    (hSeed : ∀ p s,
      recipes p = .seed s → atomsF.seed s = atomsG.seed s)
    (hPositive : ∀ p q,
      recipes p = .positive q →
        atomsF.positiveParameter q = atomsG.positiveParameter q)
    (hMeet : ∀ p u v,
      recipes p = .meetOf u v →
        LevelTree.meet
          (atomsF.ambientOriginal u) (atomsF.ambientOriginal v) =
        LevelTree.meet
          (atomsG.ambientOriginal u) (atomsG.ambientOriginal v))
    (hWellFormedF : ∀ p, (recipes p).WellFormed atomsF)
    (hWellFormedG : ∀ p, (recipes p).WellFormed atomsG)
    (actualR actualS : Events → Set (AdmissibleKptNode family))
    (hPhysicalR : KptPhysicalParameterTrace R actualR)
    (hPhysicalS : KptPhysicalParameterTrace S actualS)
    (hMembership : ∀ e p,
      R.parameters p ∈ actualR e ↔
      S.parameters p ∈ actualS e)
    (hFrames : R.eventFrame = S.eventFrame)
    (hSelectedPresent : ∀ e a,
      R.presentAt e (.inl a) = S.presentAt e (.inl a))
    (hSelectedOld : ∀ e a,
      R.oldAt e (.inl a) = S.oldAt e (.inl a))
    (hSelectedUpper : ∀ e a,
      R.upperAt e (.inl a) = S.upperAt e (.inl a)) :
    R = S := by
  have hSelected : R.selected = S.selected :=
    labelled_prefix_sources_eq_of_inverse_image_sets
      F G targetF targetG R.selected S.selected
      hSelectedF hSelectedG hStrictF hStrictG hInverse
  have hParams : R.parameters = S.parameters :=
    kpt_used_recipes_identify_parameter_nodes
      R S atomsF atomsG recipes hRecipeF hRecipeG
      hSeed hPositive hMeet
  obtain ⟨hParamPresent,hParamOld,hParamUpper⟩ :=
    kpt_physical_parameter_fields_eq_of_membership
      R S actualR actualS hParams hFrames
      hPhysicalR hPhysicalS hMembership
  have hPresent : R.presentAt = S.presentAt := by
    funext e x
    cases x with
    | inl a => exact hSelectedPresent e a
    | inr p => exact hParamPresent e p
  have hOld : R.oldAt = S.oldAt := by
    funext e x
    cases x with
    | inl a => exact hSelectedOld e a
    | inr p => exact hParamOld e p
  have hUpper : R.upperAt = S.upperAt := by
    funext e x
    cases x with
    | inl a => exact hSelectedUpper e a
    | inr p => exact hParamUpper e p
  exact fullEventIndexedSourceRecord_ext
    hSelected hParams hPresent hOld hUpper hFrames

end Kk
