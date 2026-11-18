import Kk.CoherentKptLiveImage
import Kk.ConstructedCoherentIndexAdapter

/-!
Track C: actual finite numerical-H+ source live trichotomy.
English proof and hostile audit:
  docs/track_c_physical_live_source_trichotomy_english_audit.md

Unlike an abstract Fin-index lemma, this starts from genuine physical
old/new H+ run hypotheses, and obtains both exhaustive finite sources
and their coherent map by the verified physical constructor. It
classifies each new-live full Kpt node as transported, newly active on
an old name, or literally absent from the complete old finite source.
No bound on the latter two classes or common inverse orbit follows.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Every actually constructed new-live finite H+ Kpt source name
is either transported OLD-live, old-source newly active, or literally
fresh relative to the old finite full Kpt source index.

Both new AlgorithmRun and new full-source index are CONSTRUCTED, not
assumed; the entire geometric hypothesis list is identical to the
existing physical coherent-index constructor. -/
theorem finiteNumericH_constructed_live_source_trichotomy
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
    ∃ oldParams newParams : Finset (AdmissibleKptNode family),
      ∃ oldLive : Nat → Fin oldParams.card → Bool,
        ∃ newLive : Nat → Fin newParams.card → Bool,
          ∃ e : CoherentKptIndex family
            (fun i : Fin oldParams.card =>
              (oldParams.equivFin.symm i).val)
            (fun j : Fin newParams.card =>
              (newParams.equivFin.symm j).val)
            oldLive newLive oldTop,
            ∀ cut : Nat, cut < oldTop →
              ∀ q : Fin newParams.card, newLive cut q = true →
                (∃ i : Fin oldParams.card,
                  oldLive cut i = true ∧ e.map i = q) ∨
                (∃ i : Fin oldParams.card,
                  oldLive cut i ≠ true ∧
                  (oldParams.equivFin.symm i).val =
                    (newParams.equivFin.symm q).val) ∨
                (∀ i : Fin oldParams.card,
                  (oldParams.equivFin.symm i).val ≠
                    (newParams.equivFin.symm q).val) := by
  classical
  obtain ⟨_Rold, _Rnew, oldParams, newParams, oldLive,
      newLive, e, _hOldExact, _hNewExact, _hTypes, _hUnique⟩ :=
    finiteNumericH_constructed_composable_coherent_source_index
      family K L k b N M j hNM hBlock hk hj hTarget hNTop
      hBin hUn hDiag hAvoidK hAvoidL U X hSeeds oldTop hOldPhysical
  refine ⟨oldParams, newParams, oldLive, newLive, e, ?_⟩
  intro cut _hcut q hq
  by_cases hTransported : ∃ i : Fin oldParams.card,
      oldLive cut i = true ∧ e.map i = q
  · exact Or.inl hTransported
  · right
    exact e.canonical_new_live_residual_old_inactive_or_fresh
      newParams cut q hq hTransported

end Kk

#check @Kk.finiteNumericH_constructed_live_source_trichotomy
#print axioms Kk.finiteNumericH_constructed_live_source_trichotomy
