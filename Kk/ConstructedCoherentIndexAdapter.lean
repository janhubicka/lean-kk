import Kk.CoherentKptIndexComposition
import Mathlib.Tactic

/-!
# Track C: physically constructed Kpt source indexes ARE coherent maps

English proof and adversarial audit committed before Lean:
  docs/track_c_physical_index_adapter_english_audit.md

This module exports the exact true old/new H+ physical source theorem
as a CoherentKptIndex of horizon oldTop, preserving the actual
old/new exhaustive source indexes and their live-cut records.

It also proves rigidity and path independence whenever source
and final index enumerations refer to literal Kpt nodes in the
SAME normalized successor tree. No reverse new→old map is
constructed by physical root growth.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Physical new-root source construction supplies the ACTUAL
CoherentKptIndex required by finite-stage composition.

No AlgorithmRun or source index is assumed for the NEW stage:
both true runs, two finite exhaustive source indexes and their
one-way source-name map come from the existing physical theorem.
Complete old/upper L+/E records are preserved on the SAME
genuine Kpt nodes, including all negative atoms and auxiliaries.

This is ONE genuine finite numerical-H+ stage, not an
unbounded resolved-copy or cross-occurrence theorem. -/
theorem finiteNumericH_constructed_composable_coherent_source_index
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
    let Y : Set (AdmissibleKptNode family) :=
      finiteNumericH_bareTopRootSeeds
        family L k M j hAvoidL hTarget X
    ∃ Rold : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family) X oldTop,
      ∃ Rnew : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family) Y top,
        ∃ oldParams newParams : Finset (AdmissibleKptNode family),
          ∃ oldLive : Nat → Fin oldParams.card → Bool,
            ∃ newLive : Nat → Fin newParams.card → Bool,
              ∃ e : CoherentKptIndex family
                (fun i : Fin oldParams.card =>
                  (oldParams.equivFin.symm i).val)
                (fun j : Fin newParams.card =>
                  (newParams.equivFin.symm j).val)
                oldLive newLive oldTop,
              (∀ cut : Nat, cut < oldTop →
                ∀ z : AdmissibleKptNode family,
                  z ∈ SMTree.Envelope.closure
                    (admissibleKptSTree family)
                      (Rold.I (cut+1)) X ↔
                  ∃ i : Fin oldParams.card,
                    (oldParams.equivFin.symm i).val = z ∧
                    oldLive cut i = true) ∧
              (∀ cut : Nat, cut < oldTop →
                ∀ z : AdmissibleKptNode family,
                  z ∈ SMTree.Envelope.closure
                    (admissibleKptSTree family)
                      (Rnew.I (cut+1)) Y ↔
                  ∃ i : Fin newParams.card,
                    (newParams.equivFin.symm i).val = z ∧
                    newLive cut i = true) ∧
              (∀ cut : Nat, cut < oldTop →
                ∀ i : Fin oldParams.card,
                  kptFullOldAtCut
                    ((newParams.equivFin.symm (e.map i)).val) cut =
                    kptFullOldAtCut
                      ((oldParams.equivFin.symm i).val) cut ∧
                  kptFullUpperAtCut
                    ((newParams.equivFin.symm (e.map i)).val) cut =
                    kptFullUpperAtCut
                      ((oldParams.equivFin.symm i).val) cut) ∧
              (∀ ψ : Fin oldParams.card → Fin newParams.card,
                (∀ i : Fin oldParams.card,
                  (newParams.equivFin.symm (ψ i)).val =
                    (oldParams.equivFin.symm i).val) →
                ψ = e.map) := by
  classical
  obtain ⟨Rold, Rnew, oldParams, newParams, oldLive, newLive,
    φ, hInjective, hSameNodes, hOldExact, hNewExact,
    hOldLiveForward, hFullTypes, hUnique⟩ :=
    finiteNumericH_constructed_old_new_coherent_source_index
      family K L k b N M j
      hNM hBlock hk hj hTarget hNTop
      hBin hUn hDiag hAvoidK hAvoidL U X hSeeds oldTop hOldPhysical
  let e : CoherentKptIndex family
      (fun i : Fin oldParams.card => (oldParams.equivFin.symm i).val)
      (fun i : Fin newParams.card => (newParams.equivFin.symm i).val)
      oldLive newLive oldTop :=
    { map := φ
      map_injective := hInjective
      same_node := hSameNodes
      live_forward := hOldLiveForward }
  exact ⟨Rold, Rnew, oldParams, newParams, oldLive, newLive, e,
    hOldExact, hNewExact, hFullTypes,
    by intro ψ hψ; exact hUnique ψ hψ⟩

namespace CoherentKptIndex

/-- A coherent map on a fixed old/final Kpt node enumeration is UNIQUE
when the final enumeration is injective; different proof paths or
choices of intermediate finite indexes cannot alter the old-name map.
The finite live-cut horizon does not enter this uniqueness proof. -/
theorem map_unique_of_target_injective
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    {P Q : Nat}
    {nodeP : Fin P → AdmissibleKptNode family}
    {nodeQ : Fin Q → AdmissibleKptNode family}
    {liveP : Nat → Fin P → Bool}
    {liveQ : Nat → Fin Q → Bool}
    {t u : Nat}
    (hNodeQ : Function.Injective nodeQ)
    (f : CoherentKptIndex family nodeP nodeQ liveP liveQ t)
    (g : CoherentKptIndex family nodeP nodeQ liveP liveQ u) :
    f.map = g.map := by
  funext i
  apply hNodeQ
  calc
    nodeQ (f.map i) = nodeP i := f.same_node i
    _ = nodeQ (g.map i) := (g.same_node i).symm

/-- Any two actual finite source-index paths with the SAME old/final
Kpt node lists and same old/final live masks induce exactly the
same old-to-final source name map, provided the final node list is
injective. These paths may have different intermediate lists and
cut horizons; only their common end universe is identified. -/
theorem diamond_path_independent
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    {P Q R S : Nat}
    {nodeP : Fin P → AdmissibleKptNode family}
    {nodeQ : Fin Q → AdmissibleKptNode family}
    {nodeR : Fin R → AdmissibleKptNode family}
    {nodeS : Fin S → AdmissibleKptNode family}
    {liveP : Nat → Fin P → Bool}
    {liveQ : Nat → Fin Q → Bool}
    {liveR : Nat → Fin R → Bool}
    {liveS : Nat → Fin S → Bool}
    {t u v w : Nat}
    (hNodeS : Function.Injective nodeS)
    (f : CoherentKptIndex family nodeP nodeQ liveP liveQ t)
    (g : CoherentKptIndex family nodeQ nodeS liveQ liveS u)
    (h : CoherentKptIndex family nodeP nodeR liveP liveR v)
    (k : CoherentKptIndex family nodeR nodeS liveR liveS w) :
    g.map ∘ f.map = k.map ∘ h.map := by
  exact CoherentKptIndex.map_unique_of_target_injective hNodeS
    (f.comp g) (h.comp k)

/-- A source enumeration that can be coherently matched in BOTH
directions to another injectively enumerated Kpt source gives
a genuine inverse on the initial index set. Such reverse
coverage is NOT automatic during physical new-root growth. -/
theorem reverse_left_inverse
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    {P Q : Nat}
    {nodeP : Fin P → AdmissibleKptNode family}
    {nodeQ : Fin Q → AdmissibleKptNode family}
    {liveP : Nat → Fin P → Bool}
    {liveQ : Nat → Fin Q → Bool}
    {t u : Nat}
    (hNodeP : Function.Injective nodeP)
    (f : CoherentKptIndex family nodeP nodeQ liveP liveQ t)
    (g : CoherentKptIndex family nodeQ nodeP liveQ liveP u) :
    Function.LeftInverse g.map f.map := by
  intro i
  apply hNodeP
  calc
    nodeP (g.map (f.map i)) = nodeQ (f.map i) :=
      g.same_node (f.map i)
    _ = nodeP i := f.same_node i

/-- Two-sided coherence with injective endpoint node enumerations
gives an actual Fin-index bijection; it is a conditional criterion,
not a new-to-old physical growth theorem. -/
def equivalence_of_reverse
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    {P Q : Nat}
    {nodeP : Fin P → AdmissibleKptNode family}
    {nodeQ : Fin Q → AdmissibleKptNode family}
    {liveP : Nat → Fin P → Bool}
    {liveQ : Nat → Fin Q → Bool}
    {t u : Nat}
    (hNodeP : Function.Injective nodeP)
    (hNodeQ : Function.Injective nodeQ)
    (f : CoherentKptIndex family nodeP nodeQ liveP liveQ t)
    (g : CoherentKptIndex family nodeQ nodeP liveQ liveP u) :
    Fin P ≃ Fin Q where
  toFun := f.map
  invFun := g.map
  left_inv := reverse_left_inverse hNodeP f g
  right_inv := reverse_left_inverse hNodeQ g f

/-- If BOTH forward and reverse coherent source maps actually
exist, old/new live-cut bits agree below their COMMON cut
horizon; this must NOT be applied to a genuine one-way new root
unless a separate reverse source theorem is established. -/
theorem live_iff_of_reverse
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    {P Q : Nat}
    {nodeP : Fin P → AdmissibleKptNode family}
    {nodeQ : Fin Q → AdmissibleKptNode family}
    {liveP : Nat → Fin P → Bool}
    {liveQ : Nat → Fin Q → Bool}
    {t u : Nat}
    (hNodeP : Function.Injective nodeP)
    (f : CoherentKptIndex family nodeP nodeQ liveP liveQ t)
    (g : CoherentKptIndex family nodeQ nodeP liveQ liveP u)
    (cut : Nat) (hcut : cut < min t u) (i : Fin P) :
    liveP cut i = true ↔ liveQ cut (f.map i) = true := by
  have ht : cut < t := by omega
  have hu : cut < u := by omega
  constructor
  · exact f.live_forward cut ht i
  · intro h
    have hr := g.live_forward cut hu (f.map i) h
    simpa only [reverse_left_inverse hNodeP f g i] using hr

end CoherentKptIndex

end Kk
