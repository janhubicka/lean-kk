import Kk.LabelledCopies
import SuccessorTree.V10.GPlusCanonicalCodeReconstruction
import Mathlib.Tactic

/-!
# Common selected sources from complete retained target tables

English proof and independent review were committed before this module:
`docs/retained_prefix_source_and_plan_seeds_english_20261124.md` and
`docs/audits/2026-11-24-retained-prefix-source-independent-review.md`.

Recover each actual G+ preimage from its target's complete finite table at
the genuine retained level-map coordinates. Equality of these physical
compressed tables gives literal labelled source equality and an outgoing
common monoid orbit. Equality of inverse-image sets, common raw Kpt caps,
and equality of entire parameter records are not premises.

The actual resolved-record construction must still supply the stated
table equalities and real range lifts; this module does not replace
whole-source boringness or E1 coverage by an ordinary-age shadow.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

universe u

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- The actual source vertex is the COMPLETE finite target table pulled
back along its genuine retained coordinates. The target need not be named
syntactically as `gPlusShapeImage`; a verified image equation suffices.
Both Boolean values of all four tables, including E, are retained. -/
theorem gPlus_source_code_eq_retained_target
    (F : ShapeMap (admissibleKptSTree family))
    (source target : FiniteGPlusVertex family)
    (hImage : gPlusShapeImage F source = target)
    (rho : Fin source.val.size → Fin target.val.size)
    (hRho : ∀ i : Fin source.val.size,
      (rho i).val = kptShapeLevelMap family F i.val) :
    source.val = target.val.reindex source.val.size rho := by
  subst target
  have hRhoEq : rho =
      (fun i : Fin source.val.size =>
        Fin.cast (gPlusShapeImage_size F source).symm
          (shapeImageRetainedIndex F source i)) := by
    funext i
    apply Fin.ext
    exact hRho i
  rw [hRhoEq]
  exact (shapeImageRetainedCode_eq F source).symm

/-- Complete physical target reindexings identify labelled preimages
under two genuine shape maps. Source lengths may initially differ: their
equality is already part of equality of the complete reindexed codes.

No source-top, source-value or inverse-image-set equality is assumed.
The coordinate maps must be the actual retained numerical level maps. -/
theorem labelled_sources_eq_of_retained_target_tables
    {Labels : Type u}
    (F G : ShapeMap (admissibleKptSTree family))
    (sourceF sourceG targetF targetG : Labels → FiniteGPlusVertex family)
    (hImageF : ∀ a, gPlusShapeImage F (sourceF a) = targetF a)
    (hImageG : ∀ a, gPlusShapeImage G (sourceG a) = targetG a)
    (rhoF : ∀ a, Fin (sourceF a).val.size → Fin (targetF a).val.size)
    (rhoG : ∀ a, Fin (sourceG a).val.size → Fin (targetG a).val.size)
    (hRhoF : ∀ a i,
      (rhoF a i).val = kptShapeLevelMap family F i.val)
    (hRhoG : ∀ a i,
      (rhoG a i).val = kptShapeLevelMap family G i.val)
    (hTables : ∀ a,
      (targetF a).val.reindex (sourceF a).val.size (rhoF a) =
        (targetG a).val.reindex (sourceG a).val.size (rhoG a)) :
    sourceF = sourceG := by
  funext a
  apply Subtype.ext
  calc
    (sourceF a).val =
        (targetF a).val.reindex (sourceF a).val.size (rhoF a) :=
      gPlus_source_code_eq_retained_target
        F (sourceF a) (targetF a) (hImageF a) (rhoF a) (hRhoF a)
    _ = (targetG a).val.reindex (sourceG a).val.size (rhoG a) :=
      hTables a
    _ = (sourceG a).val :=
      (gPlus_source_code_eq_retained_target
        G (sourceG a) (targetG a) (hImageG a) (rhoG a) (hRhoG a)).symm

/-- Two target copies with equal complete retained physical tables are
actual outgoing monoid images of one identical labelled G+ source.
This concludes the orbit bridge, not merely a comparison of source ages.

For the manuscript application the earlier envelope/endpoint theorem
provides the lifts, while the concrete retained record must provide the
table equality. The prefix-chain finite carrier is supplied separately
by the existing checked Ramsey transfer. -/
theorem common_labelled_orbit_of_retained_target_tables
    {Labels : Type u}
    (F G : SMTree.MMap (normalizedKptSMTree family))
    (sourceF sourceG targetF targetG : Labels → FiniteGPlusVertex family)
    (hTargetFInj : Function.Injective targetF)
    (hTargetGInj : Function.Injective targetG)
    (hImageF : ∀ a, gPlusShapeImage F.map (sourceF a) = targetF a)
    (hImageG : ∀ a, gPlusShapeImage G.map (sourceG a) = targetG a)
    (rhoF : ∀ a, Fin (sourceF a).val.size → Fin (targetF a).val.size)
    (rhoG : ∀ a, Fin (sourceG a).val.size → Fin (targetG a).val.size)
    (hRhoF : ∀ a i,
      (rhoF a i).val = kptShapeLevelMap family F.map i.val)
    (hRhoG : ∀ a i,
      (rhoG a i).val = kptShapeLevelMap family G.map i.val)
    (hTables : ∀ a,
      (targetF a).val.reindex (sourceF a).val.size (rhoF a) =
        (targetG a).val.reindex (sourceG a).val.size (rhoG a)) :
    ∃ source : LabelledGPlusCopy family Labels,
      LabelledGPlusCopy.map F source =
        (⟨targetF, hTargetFInj⟩ : LabelledGPlusCopy family Labels) ∧
      LabelledGPlusCopy.map G source =
        (⟨targetG, hTargetGInj⟩ : LabelledGPlusCopy family Labels) := by
  have hSame : sourceF = sourceG :=
    labelled_sources_eq_of_retained_target_tables
      F.map G.map sourceF sourceG targetF targetG
      hImageF hImageG rhoF rhoG hRhoF hRhoG hTables
  have hSourceInj : Function.Injective sourceF := by
    intro a b hEq
    apply hTargetFInj
    calc
      targetF a = gPlusShapeImage F.map (sourceF a) := (hImageF a).symm
      _ = gPlusShapeImage F.map (sourceF b) := congrArg _ hEq
      _ = targetF b := hImageF b
  refine ⟨⟨sourceF, hSourceInj⟩, ?_, ?_⟩
  · apply Subtype.ext
    funext a
    exact hImageF a
  · apply Subtype.ext
    funext a
    change gPlusShapeImage G.map (sourceF a) = targetG a
    rw [hSame]
    exact hImageG a

end Kk
