import Kk.IndexedPhysicalCrossing
import Mathlib.Tactic

/-!
# Track E: actual finite-index structural I1/I2 and full source crossing

The verified Track C exhaustive final Kpt closure index has a literal
active-node membership mask at EVERY cut of a genuine numerical H+
AlgorithmRun. It supplies not only all old/upper full L+ pairs, but
also EXACT I1 terminal-node presence and I2 same-component meet
events. Both structural tests are recorded without assuming I2 fails.

The same physical Kpt node retains its index at all cuts. This
repairs the terminal-prefix blindness of crossing-pair spectra and
does not replace genuine meet incidence by a selected-shadow age test.

English-first audit:
  docs/track_e_indexed_physical_crossing_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Exact per-cut coverage of actual Kpt nodes recovers BOTH
structural Algorithm 5.4 tests: (I1) node at the cut and (I2)
a same-component pair with its actual meet at the cut.

The second equivalence uses the SAME live index for BOTH nodes;
it does not infer the meet from equality of their old types.
No-crossing nodes are still included, as needed for I1. -/
theorem physical_I1_I2_iff_indexed_active_nodes
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {Params : Type}
    (node : Params → AdmissibleKptNode family)
    (presentAt : Nat → Params → Bool)
    (Z : Set (AdmissibleKptNode family))
    (cut : Nat)
    (hExact : ∀ z : AdmissibleKptNode family,
      z ∈ Z ↔ ∃ j : Params, node j = z ∧ presentAt cut j = true) :
    ((∃ z : AdmissibleKptNode family,
        z ∈ Z ∧ LevelTree.lev z = cut) ↔
      ∃ j : Params, presentAt cut j = true ∧
        LevelTree.lev (node j) = cut) ∧
    ((∃ a : AdmissibleKptNode family, a ∈ Z ∧
        ∃ b : AdmissibleKptNode family, b ∈ Z ∧
          SMTree.Envelope.SameComponent a b ∧
          LevelTree.lev (LevelTree.meet a b) = cut) ↔
      ∃ i : Params, presentAt cut i = true ∧
        ∃ j : Params, presentAt cut j = true ∧
          SMTree.Envelope.SameComponent (node i) (node j) ∧
          LevelTree.lev (LevelTree.meet (node i) (node j)) = cut) := by
  constructor
  · constructor
    · rintro ⟨z,hz,hLevel⟩
      obtain ⟨j,hNode,hLive⟩ := (hExact z).1 hz
      refine ⟨j,hLive,?_⟩
      rw [hNode]
      exact hLevel
    · rintro ⟨j,hLive,hLevel⟩
      exact ⟨node j,(hExact (node j)).2 ⟨j,rfl,hLive⟩,hLevel⟩
  · constructor
    · rintro ⟨a,ha,b,hb,hCommon,hMeet⟩
      obtain ⟨i,hi,hLiveI⟩ := (hExact a).1 ha
      obtain ⟨j,hj,hLiveJ⟩ := (hExact b).1 hb
      refine ⟨i,hLiveI,j,hLiveJ,?_,?_⟩
      · simpa only [hi,hj] using hCommon
      · simpa only [hi,hj] using hMeet
    · rintro ⟨i,hLiveI,j,hLiveJ,hCommon,hMeet⟩
      refine ⟨node i,(hExact (node i)).2 ⟨i,rfl,hLiveI⟩,
        node j,(hExact (node j)).2 ⟨j,rfl,hLiveJ⟩,
        hCommon,hMeet⟩

/-- Complete physical structural/event record of ONE finite
numerical-H+ AlgorithmRun, over one and the same exhaustive source
node index at ALL cuts.

For each cut, the outputs give:
* exact I1 presence from active Kpt source nodes at that level;
* exact I2 meet incidence from active pairs of genuine Kpt nodes;
* exact full dependent old-to-upper L+ crossing relation, including
  E atoms, and potentially MULTIPLE outputs at an I2 cut.

The final closure index is injective and exhaustive. There is NO
unconditional uniform bound on its size across different N, and
no assertion that two diary occurrences have the same indices.
-/
theorem numericH_actual_run_all_cuts_full_structural_trace
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Set (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid U)
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top) :
    ∃ params : Finset (AdmissibleKptNode family),
      ∃ presentAt : Nat → Fin params.card → Bool,
      (∀ z : AdmissibleKptNode family,
        z ∈ params ↔
          z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
            (R.I 0) X) ∧
      Function.Injective
        (fun j : Fin params.card => (params.equivFin.symm j).val) ∧
      (∀ cut, cut < top →
        let Z : Set (AdmissibleKptNode family) :=
          SMTree.Envelope.closure (admissibleKptSTree family)
            (R.I (cut+1)) X
        let node : Fin params.card → AdmissibleKptNode family :=
          fun j => (params.equivFin.symm j).val
        ((∃ z : AdmissibleKptNode family,
            z ∈ Z ∧ LevelTree.lev z = cut) ↔
          ∃ j : Fin params.card,
            presentAt cut j = true ∧ LevelTree.lev (node j) = cut) ∧
        ((∃ a : AdmissibleKptNode family, a ∈ Z ∧
            ∃ b : AdmissibleKptNode family, b ∈ Z ∧
              SMTree.Envelope.SameComponent a b ∧
              LevelTree.lev (LevelTree.meet a b) = cut) ↔
          ∃ i : Fin params.card, presentAt cut i = true ∧
            ∃ j : Fin params.card, presentAt cut j = true ∧
              SMTree.Envelope.SameComponent (node i) (node j) ∧
              LevelTree.lev (LevelTree.meet (node i) (node j)) = cut) ∧
        IndexedPhysicalCrossing family node presentAt cut =
          FullPhysicalClosureCrossing family Z cut) := by
  classical
  obtain ⟨params,presentAt,hParams,hInj,_hPresent,hCover⟩ :=
    finiteNumericH_actualRun_uniform_exhaustive_source_index
      family K k N hAvoid U X hX top R
  refine ⟨params,presentAt,hParams,hInj,?_⟩
  intro cut hCut
  let Z : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (R.I (cut+1)) X
  let node : Fin params.card → AdmissibleKptNode family :=
    fun j => (params.equivFin.symm j).val
  have hExact : ∀ z : AdmissibleKptNode family,
      z ∈ Z ↔ ∃ j : Fin params.card,
        node j = z ∧ presentAt cut j = true :=
    hCover cut hCut
  have hStructural :=
    physical_I1_I2_iff_indexed_active_nodes
      family node presentAt Z cut hExact
  have hCrossing :=
    indexed_physical_crossing_eq_full_closure_relation
      family node presentAt Z cut hExact
  exact ⟨hStructural.1,hStructural.2,hCrossing⟩

end Kk
