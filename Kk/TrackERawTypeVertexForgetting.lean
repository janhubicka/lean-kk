import SuccessorTree.V10.GPlusOrdinaryCode
import Mathlib.Tactic

/-!
# Track E E59: ordinary finite G+ code forgets the distinguished type vertex

This is a literal positive-size **raw record** counterexample, not
an assertion that two particular raw nodes are both admissible
under a fixed forbidden family or arise in a resolved diary.

Complete raw dependent L+ types retain a distinguished type vertex
none. RawPartialTypeNode.ordinaryCode keeps ONLY the ordinary
some/some socle table (including E); it cannot recover the
unary predicate of none from the finite code.

English-first hostile audit:
docs/track_e_raw_type_vertex_forgetting_counterexample_english.md
-/

namespace Kk

open SuccessorTree.V10

/-- Two complete raw L+ types over the SAME one-vertex socle.
All ordinary L and E atoms agree; only the unary value of the
distinguished type vertex 'none' depends on bit. -/
def rawTypeWithDistinguishedUnary (bit : Bool) :
    RawPartialTypeNode 0 1 0 :=
  ⟨1, {
    lReduct := {
      binary := fun _ _ t => Fin.elim0 t
      unary := fun x _ =>
        match x with
        | none => bit
        | some _ => false
      diagonal := fun _ t => Fin.elim0 t
    }
    eRelation := fun x y =>
      match x, y with
      | some _, none => true
      | _, _ => false
  }⟩

/-- Both raw records have the literally identical full finite
ordinary L+ socle code. E is retained and equal on that socle. -/
theorem rawTypeWithDistinguishedUnary_ordinaryCode_eq :
    RawPartialTypeNode.ordinaryCode
      (rawTypeWithDistinguishedUnary false) =
    RawPartialTypeNode.ordinaryCode
      (rawTypeWithDistinguishedUnary true) := by
  rfl

/-- A unary test on the distinguished non-socle vertex separates
the two COMPLETE raw Kpt type records. -/
theorem rawTypeWithDistinguishedUnary_ne :
    rawTypeWithDistinguishedUnary false ≠
      rawTypeWithDistinguishedUnary true := by
  intro h
  have hBit := congrArg
    (fun N : RawPartialTypeNode 0 1 0 =>
      N.2.lReduct.unary none (0 : Fin 1)) h
  have hImpossible : false = true := by
    simpa only [rawTypeWithDistinguishedUnary] using hBit
  cases hImpossible

/-- The ordinary-socle projection is NOT injective on the
complete raw L+ partial-type records, even at positive size.
This is a raw-data fact, not an admissible-Kpt diary counterexample. -/
theorem rawPartialType_ordinaryCode_not_injective :
    ∃ N M : RawPartialTypeNode 0 1 0,
      N.1 = 1 ∧ M.1 = 1 ∧ N ≠ M ∧
      RawPartialTypeNode.ordinaryCode N =
        RawPartialTypeNode.ordinaryCode M := by
  refine ⟨rawTypeWithDistinguishedUnary false,
    rawTypeWithDistinguishedUnary true, rfl, rfl,
    rawTypeWithDistinguishedUnary_ne,
    rawTypeWithDistinguishedUnary_ordinaryCode_eq⟩

end Kk
