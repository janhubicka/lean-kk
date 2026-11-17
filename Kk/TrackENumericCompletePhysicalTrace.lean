import Kk.TrackEPhysicalParameterTrace
import Kk.NumericHExhaustiveRunIndex
import Mathlib.Tactic

/-!
# Track E E61: genuine numerical-H Kpt runs yield complete physical event traces

The actual complete finite index of the final physical Kpt closure
comes from finiteNumericH_actualRun_uniform_exhaustive_source_index.
At every actual scanned source cut it names ALL the nodes in the true
pre-cut meet-and-parameter closure. Combine it with the E57 literal
old/upper raw ancestor trace to construct a record satisfying BOTH
KptPhysicalParameterTrace and CoversParameterClosure.

This is a one-run geometrically instantiated completeness result.
There is no cross-occurrence diary-event normalization or orbit.

English-first proof and 18 hostile tests:
docs/track_e_numeric_complete_parameter_trace_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- One REAL finite numerical-H+ AlgorithmRun, with actual forbidden
avoidance and physical original-source representation, has a fully
physical event trace indexed at EVERY scanned source cut.

Every actual Kpt node of EVERY pre-cut full closure is named by some
active dependent parameter. Every active dependent parameter denotes
an actual Kpt node of that closure. Its old/upper dependent L+ types
are the same-node literal raw Kpt ancestors, with no oracle.

The frame kind/participant/successor character and selected G+
data are intentionally supplied externally; asserting they coincide
for DIFFERENT diary occurrences is still open. -/
theorem finiteNumericH_actualRun_exists_complete_Kpt_event_trace
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Set (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid U)
    (runHeight : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X runHeight)
    (n : Nat) {Kind Character : Type}
    (selected : Fin n → FiniteGPlusVertex family)
    (frame : (P : Nat) → Fin runHeight →
      FullSourceEventFrame (Fin n) (Fin P) Kind Character)
    (hFrameCut : ∀ (P : Nat) (e : Fin runHeight),
      (frame P e).compressedSourceCut = e.val)
    (selectedPresent : Fin runHeight → Fin n → Bool)
    (selectedOld selectedUpper : Fin runHeight → Fin n →
      Option (RawPartialTypeNode db du dd)) :
    ∃ params : Finset (AdmissibleKptNode family),
      ∃ record : KptEventIndexedSourceRecord family n
        (Fin params.card)
        (Option (RawPartialTypeNode db du dd))
        (Option (RawPartialTypeNode db du dd))
        (Fin runHeight) Kind Character,
        (∀ j : Fin params.card,
          record.parameters j = (params.equivFin.symm j).val) ∧
        (∀ e : Fin runHeight,
          record.eventFrame e = frame params.card e ∧
          (record.eventFrame e).compressedSourceCut = e.val) ∧
        KptPhysicalParameterTrace record
          (fun e : Fin runHeight =>
            SMTree.Envelope.closure (admissibleKptSTree family)
              (R.I (e.val+1)) X) ∧
        record.CoversParameterClosure
          (fun e : Fin runHeight =>
            SMTree.Envelope.closure (admissibleKptSTree family)
              (R.I (e.val+1)) X) := by
  classical
  obtain ⟨params, presentAt, _hParams, _hInjective,
    hPresent, hExact⟩ :=
    finiteNumericH_actualRun_uniform_exhaustive_source_index
      family K k N hAvoid U X hX runHeight R
  let named : Fin params.card → AdmissibleKptNode family :=
    fun j => (params.equivFin.symm j).val
  let actual : Fin runHeight → Set (AdmissibleKptNode family) :=
    fun e => SMTree.Envelope.closure (admissibleKptSTree family)
      (R.I (e.val+1)) X
  let trace : KptEventIndexedSourceRecord family n
      (Fin params.card)
      (Option (RawPartialTypeNode db du dd))
      (Option (RawPartialTypeNode db du dd))
      (Fin runHeight) Kind Character :=
    kptPhysicalEventRecord selected named actual
      (frame params.card)
      selectedPresent selectedOld selectedUpper
  have hPhysical : KptPhysicalParameterTrace trace actual :=
    kptPhysicalEventRecord_has_parameter_trace
      selected named actual (frame params.card)
      selectedPresent selectedOld selectedUpper
  refine ⟨params, trace, ?_, ?_, hPhysical, ?_⟩
  · intro j
    rfl
  · intro e
    exact ⟨rfl, hFrameCut params.card e⟩
  · intro e z
    constructor
    · intro hz
      obtain ⟨j,hName,hLive⟩ :=
        (hExact e.val e.isLt z).mp hz
      have hIn : named j ∈ actual e :=
        (hPresent e.val j).mp hLive
      exact ⟨j,(hPhysical.1 e j).mpr hIn,hName⟩
    · rintro ⟨j,hActive,hName⟩
      have hIn : trace.parameters j ∈ actual e :=
        (hPhysical.1 e j).mp hActive
      rw [hName] at hIn
      exact hIn

end Kk
