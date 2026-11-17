import Kk.TrackECoherentFinalIndexRetention
import Kk.NumericHExhaustiveRunIndex
import Mathlib.Tactic

/-!
# Track E E63: actual numerical-H+ nested runs have coherent finite source names

Apply the CHECKED genuine exhaustive finite Kpt source-index theorem
to both actual numerical-H+ AlgorithmRuns, then E62's coherent
old-to-new final-source index injection. This discharges the
abstract existence/exactness/live-mask premises of E62 in one
concrete finite numerical-H+ structure.

The source embedding is one-way OLD->NEW, and relies on
actual nested Kpt seeds in ONE normalized tree. It does not
construct a diary-uniform event template, the reverse
no-novelty comparison or a common labelled inverse-source orbit.

English-first proof and 20 hostile checks:
docs/track_e_numeric_coherent_source_injection_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- In one genuine finite numerical-H+ physical source, two actual
nested Kpt AlgorithmRuns of increasing tops have independently
CONSTRUCTED exhaustive final physical Kpt name sets and accurate
per-cut live masks. There is one injective name map old->new that
preserves actual physical Kpt nodes, all old-cut activity and
both complete dependent old/upper L+ raw ancestor records.

If another name map preserves the SAME actual old Kpt node on each
old index, it equals this one: the new exhaustive index is injective.
This is strictly a one-way nested physical source-growth theorem,
not a canonical labelled diary-orbit or upper BRD result. -/
theorem finiteNumericH_actual_nested_runs_coherent_source_index
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Set (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid U)
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid U)
    (hXY : X ⊆ Y)
    (oldTop newTop : Nat) (hTopLe : oldTop ≤ newTop)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = oldTop)
    (RunOld : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (RunNew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y newTop) :
    ∃ oldParams newParams : Finset (AdmissibleKptNode family),
      ∃ oldLive : Nat → Fin oldParams.card → Bool,
      ∃ newLive : Nat → Fin newParams.card → Bool,
      ∃ φ : Fin oldParams.card → Fin newParams.card,
        Function.Injective φ ∧
        (∀ i : Fin oldParams.card,
          (newParams.equivFin.symm (φ i)).val =
            (oldParams.equivFin.symm i).val) ∧
        (∀ cut : Nat, cut < oldTop →
          ∀ z : AdmissibleKptNode family,
            z ∈ SMTree.Envelope.closure
              (admissibleKptSTree family) (RunOld.I (cut+1)) X ↔
            ∃ i : Fin oldParams.card,
              (oldParams.equivFin.symm i).val = z ∧
              oldLive cut i = true) ∧
        (∀ cut : Nat, cut < oldTop →
          ∀ z : AdmissibleKptNode family,
            z ∈ SMTree.Envelope.closure
              (admissibleKptSTree family) (RunNew.I (cut+1)) Y ↔
            ∃ j : Fin newParams.card,
              (newParams.equivFin.symm j).val = z ∧
              newLive cut j = true) ∧
        (∀ cut : Nat, cut < oldTop →
          ∀ i : Fin oldParams.card,
            oldLive cut i = true → newLive cut (φ i) = true) ∧
        (∀ cut : Nat, cut < oldTop →
          ∀ i : Fin oldParams.card,
            kptFullOldAtCut
              ((newParams.equivFin.symm (φ i)).val) cut =
                kptFullOldAtCut
                  ((oldParams.equivFin.symm i).val) cut ∧
            kptFullUpperAtCut
              ((newParams.equivFin.symm (φ i)).val) cut =
                kptFullUpperAtCut
                  ((oldParams.equivFin.symm i).val) cut) ∧
        (∀ ψ : Fin oldParams.card → Fin newParams.card,
          (∀ i : Fin oldParams.card,
            (newParams.equivFin.symm (ψ i)).val =
              (oldParams.equivFin.symm i).val) → ψ = φ) := by
  classical
  obtain ⟨oldParams, oldLive,
      hOldParams, hOldInj, hOldPresent, hOldExact⟩ :=
    finiteNumericH_actualRun_uniform_exhaustive_source_index
      family K k N hAvoid U X hX oldTop RunOld
  obtain ⟨newParams, newLive,
      hNewParams, hNewInj, hNewPresent, hNewExact⟩ :=
    finiteNumericH_actualRun_uniform_exhaustive_source_index
      family K k N hAvoid U Y hY newTop RunNew
  let oldNode : Fin oldParams.card → AdmissibleKptNode family :=
    fun i => (oldParams.equivFin.symm i).val
  let newNode : Fin newParams.card → AdmissibleKptNode family :=
    fun j => (newParams.equivFin.symm j).val
  have hOldFinal : ∀ i : Fin oldParams.card,
      oldNode i ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (RunOld.I 0) X := by
    intro i
    have hIn : oldNode i ∈ oldParams :=
      (oldParams.equivFin.symm i).property
    exact (hOldParams (oldNode i)).mp hIn
  have hNewFinalExact : ∀ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (RunNew.I 0) Y ↔
      ∃ j : Fin newParams.card, newNode j = z := by
    intro z
    constructor
    · intro hz
      have hIn : z ∈ newParams := (hNewParams z).mpr hz
      let j : Fin newParams.card := newParams.equivFin ⟨z,hIn⟩
      refine ⟨j,?_⟩
      simp [newNode,j]
    · rintro ⟨j,hEq⟩
      have hIn : newNode j ∈ newParams :=
        (newParams.equivFin.symm j).property
      have hFinal : newNode j ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (RunNew.I 0) Y :=
        (hNewParams (newNode j)).mp hIn
      rw [hEq] at hFinal
      exact hFinal
  obtain ⟨φ, hInj, hNames, hLive, hRaw⟩ :=
    crossheight_coherent_old_final_index_embedding
      family X Y hXY oldTop newTop hTopLe hTopSeed
      RunOld RunNew oldNode newNode oldLive newLive
      hOldInj hOldFinal hNewFinalExact
      (by
        intro cut hCut i hActive
        exact (hOldPresent cut i).mp hActive)
      (by
        intro cut hCut j
        exact hNewPresent cut j)
  refine ⟨oldParams,newParams,oldLive,newLive,φ,
    hInj,hNames,?_,?_,hLive,hRaw,?_⟩
  · intro cut hCut z
    exact hOldExact cut hCut z
  · intro cut hCut z
    exact hNewExact cut (by omega) z
  · intro ψ hψ
    exact crossheight_coherent_final_index_embedding_unique
      oldNode newNode hNewInj ψ φ hψ hNames

end Kk
