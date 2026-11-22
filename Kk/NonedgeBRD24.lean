import Kk.NonedgeBRDSemantics
import Kk.NonedgeHistoryCount
import Kk.NonedgeProfileBridge
import Kk.HensonLeftDenseConstruction
import Kk.HensonUniversality
import Mathlib.Data.Fintype.EquivFin

/-!
# The nonedge degree-24 goal, a concrete model, and honest proof interfaces

This file does NOT prove the final nonedge big Ramsey degree. It proves
that the ordinary Henson hypotheses have a concrete model and connects
the independently counted legal histories to the ordinary BRD definition
under two explicit, still uninstantiated infinite hypotheses.

`NonedgeDegree24Goal` is the requested proposition, not a theorem.
The theorem `degree24_of_history_interfaces` is conditional on a real
record map, canonization of every finite coloring, and occurrence of
every history in every induced copy. None is introduced as an axiom.

English proof and prior audit:
`docs/nonedge_brd24_interface_20261122.md`.
-/

namespace Kk.NonedgeBRD

set_option maxRecDepth 100000

/-- An actual countably infinite graph, independently of any Ramsey claim. -/
def constructedHenson4 : SimpleGraph Nat :=
  graphOfBool (LeftDenseConstruction.edge 4)
    (LeftDenseConstruction.edge_loopless 4)
    (LeftDenseConstruction.edge_symmetric 4)

theorem constructedHenson4_cliqueFree : constructedHenson4.CliqueFree 4 := by
  intro S hClique
  apply LeftDenseConstruction.edge_cliqueFree 4 (by omega) (S.sup id + 1)
  refine ⟨S, hClique.card_eq, ?_, ?_⟩
  · intro x hx
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hx)
  · intro x hx y hy hxy
    exact hClique.isClique hx hy hxy

theorem constructedHenson4_leftDense :
    OnePointLeftDense (boolAdj constructedHenson4) 4 := by
  simpa [constructedHenson4] using
    LeftDenseConstruction.edge_onePointLeftDense 4 (by omega)

/-- No hypothetical graph or density assumptions are needed for this model. -/
theorem constructedHenson4_isHenson4 : IsHenson4 constructedHenson4 :=
  isHenson4_of_onePointLeftDense constructedHenson4
    constructedHenson4_cliqueFree constructedHenson4_leftDense

theorem exists_henson4 : ∃ G : SimpleGraph Nat, IsHenson4 G :=
  ⟨constructedHenson4, constructedHenson4_isHenson4⟩

/-- The final proposition requested by the project. No theorem in this
module claims to inhabit it. -/
def NonedgeDegree24Goal : Prop :=
  ∀ G : SimpleGraph Nat, IsHenson4 G → DegreeEq G 24

/-- The universal target is equivalent to the same degree assertion in
the explicit model. Ordinary extension and universality justify this
reduction; no privileged enumeration is built into the degree. -/
theorem nonedgeDegree24Goal_iff_constructed :
    NonedgeDegree24Goal ↔ DegreeEq constructedHenson4 24 := by
  constructor
  · intro h
    exact h constructedHenson4 constructedHenson4_isHenson4
  · intro h G hG
    exact (HensonUniversality.degreeEq_iff_of_isHenson4
      constructedHenson4 G constructedHenson4_isHenson4 hG 24).mp h

/-- Canonization for all finite colorings using records of the preimage
copies. This hypothesis must be proved by the genuine upper construction. -/
def HistoryCanonizes (G : SimpleGraph Nat)
    (record : NonedgeCopy G → NonedgeHistory.History) : Prop :=
  ∀ k : Nat, ∀ c : NonedgeCopy G → Fin k,
    ∃ f : G ↪g G, ∃ byHistory : NonedgeHistory.History → Fin k,
      ∀ A : NonedgeCopy G,
        c (NonedgeCopy.map f A) = byHistory (record A)

/-- Every history occurs among the actual copies INSIDE every induced
self-copy. Global surjectivity of `record` alone would be insufficient. -/
def HistoriesOccurInEveryCopy (G : SimpleGraph Nat)
    (record : NonedgeCopy G → NonedgeHistory.History) : Prop :=
  ∀ f : G ↪g G,
    Function.Surjective (fun A : NonedgeCopy G => record (NonedgeCopy.map f A))

theorem degreeLE24_of_history_canonizes
    (G : SimpleGraph Nat) (record : NonedgeCopy G → NonedgeHistory.History)
    (hCanon : HistoryCanonizes G record) : DegreeLE G 24 := by
  classical
  intro k c
  obtain ⟨f, byHistory, hColours⟩ := hCanon k c
  refine ⟨f, Finset.univ.image byHistory, ?_, ?_⟩
  · calc
      (Finset.univ.image byHistory).card ≤
          (Finset.univ : Finset NonedgeHistory.History).card :=
        Finset.card_image_le
      _ = 24 := by rw [Finset.card_univ, NonedgeHistory.history_card]
  · intro A
    rw [hColours A]
    exact Finset.mem_image.mpr ⟨record A, Finset.mem_univ _, rfl⟩

/-- A bijective numbering of the independently defined accepted-history
type. The number 24 enters only through the proved cardinality theorem. -/
noncomputable def numberHistory : NonedgeHistory.History ≃ Fin 24 :=
  Fintype.equivFinOfCardEq NonedgeHistory.history_card

theorem unavoidable24_of_histories_occur
    (G : SimpleGraph Nat) (record : NonedgeCopy G → NonedgeHistory.History)
    (hOccurs : HistoriesOccurInEveryCopy G record) :
    Unavoidable G 24 (fun A => numberHistory (record A)) := by
  intro f colour
  obtain ⟨history, rfl⟩ := numberHistory.surjective colour
  obtain ⟨A, hA⟩ := hOccurs f history
  exact ⟨A, congrArg numberHistory hA⟩

/-- CONDITIONAL exactness. The finite count is verified, but neither
infinite premise nor an actual Henson record assignment is supplied here. -/
theorem degree24_of_history_interfaces
    (G : SimpleGraph Nat) (record : NonedgeCopy G → NonedgeHistory.History)
    (hCanon : HistoryCanonizes G record)
    (hOccurs : HistoriesOccurInEveryCopy G record) : DegreeEq G 24 :=
  degreeEq_of_upper_and_unavoidable G 24
    (degreeLE24_of_history_canonizes G record hCanon)
    (fun A => numberHistory (record A))
    (unavoidable24_of_histories_occur G record hOccurs)

/-- The precise remaining sufficient obligations on ONE concrete model.
This is still conditional: no actual record/canonization/unavoidability
package satisfying these premises has been constructed. -/
theorem nonedgeDegree24Goal_of_constructed_history_interfaces
    (record : NonedgeCopy constructedHenson4 → NonedgeHistory.History)
    (hCanon : HistoryCanonizes constructedHenson4 record)
    (hOccurs : HistoriesOccurInEveryCopy constructedHenson4 record) :
    NonedgeDegree24Goal :=
  nonedgeDegree24Goal_iff_constructed.mpr
    (degree24_of_history_interfaces constructedHenson4 record hCanon hOccurs)

end Kk.NonedgeBRD
