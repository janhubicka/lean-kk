import Kk.B3CutStarNameTransport
import Kk.FullPhysicalCrossingRelation
import Mathlib.Tactic

/-!
# Track B: certify that FULL really covers the whole physical Kpt source

English-first proof and 19 hostile checks:
  docs/track_b_full_source_exhaustiveness_english_audit.md

The earlier HensonCutOccurrence.hRepresented gives only
  Full(v) → closureSelectedOriginal(v).
This does NOT imply that Full exhausts the full Kpt crossing.
The following repaired application requires BOTH exact Full-name
selection and representation of every physical closure node by
the common finite original-name pool.

Under these genuinely stronger hypotheses the full source/target
L+ crossing GRAPH equals the choice-free FullPhysicalClosureCrossing
relation. The actual unanchored cut-star permitted L-reduct set
then equals the intrinsic positive-cut projection of that relation.

The source-rank alignment and intrinsic cut-star equality ACROSS
diary occurrences remain unproved, as do full event labels, relative
continuation fidelity and the common labelled inverse orbit.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The intrinsic L-only positive-cut next-type spectrum of a
TRUE PHYSICAL Kpt closure crossing relation. It depends ONLY
on the actual closure Z, not original-name pools, arbitrary target
choices or selected auxiliary E bits on the abstract age witness.

The tested cut edge is a real ORDINARY-L atom of the complete
next L-reduct; it is not the auxiliary E relation. -/
def PhysicalCutStarUpperL
    (family : List (NormalizedForbidden 1 0 1))
    (Z : Set (AdmissibleKptNode family))
    (cut : Nat)
    (R : RelationalPrefixType (cut+1) 1 0 1) : Prop :=
  ∃ T : PartialTypeWithE cut 1 0 1,
    ∃ U : PartialTypeWithE (cut+1) 1 0 1,
      (T,U) ∈ FullPhysicalClosureCrossing family Z cut ∧
      U.lReduct = R ∧
      R.binary
        (some (⟨cut,Nat.lt_succ_self cut⟩ : Fin (cut+1)))
        none (0 : Fin 1) = true

namespace HensonCutOccurrence

variable {ell cut : Nat} {hell : 2 ≤ ell}

/-- An EXACT full selected-source name predicate plus an
EXHAUSTIVE actual original-prefix pool identifies the entire
chosen prescribed graph with the true physical FULL Kpt crossing
relation, including all E/negative L atoms.

Neither condition follows from the existing weaker
HensonCutOccurrence.hRepresented alone. -/
theorem fullProfile_graph_eq_physical_of_exhaustive
    (P : HensonCutOccurrence ell cut hell)
    (hFullExact : ∀ v : Fin P.M,
      P.Full v ↔
        closureSelectedOriginal (hensonForbiddenFamily ell hell)
          P.ambient P.hAvoid P.original P.Z cut v)
    (hPool : ∀ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      z ∈ P.Z →
        ∃ v : Fin P.M,
          z ≤ P.ambient.kptOriginal
            (hensonForbiddenFamily ell hell) P.hAvoid (P.original v)) :
    fullPrescribedCrossingGraph P.fullProfile =
      FullPhysicalClosureCrossing
        (hensonForbiddenFamily ell hell) P.Z cut := by
  classical
  have hFullEq : P.Full =
      closureSelectedOriginal (hensonForbiddenFamily ell hell)
        P.ambient P.hAvoid P.original P.Z cut := by
    funext v
    exact propext (hFullExact v)
  have hF :
      P.fullProfile =
        closureSelectedBoringData
          (hensonForbiddenFamily ell hell)
          P.ambient P.hAvoid P.original P.Z cut := by
    change selectedStagePoolPrescribedData
        P.ambient cut P.original P.Full =
      selectedStagePoolPrescribedData P.ambient cut P.original
        (closureSelectedOriginal (hensonForbiddenFamily ell hell)
          P.ambient P.hAvoid P.original P.Z cut)
    rw [hFullEq]
  rw [hF]
  exact finiteNumericH_full_crossing_graph_is_physical_relation
    (hensonForbiddenFamily ell hell)
    (normalizedGraphModel P.E) P.k P.N
    P.hAvoid P.original P.Z hPool cut P.hNoI2

/-- With the FULL source-certified name and pool hypotheses,
the permitted complete upper L-reducts of the actual unanchored
cut-star coincide EXACTLY with the positive-cut projection of
the complete physical L+ crossing relation.

Unlike earlier same-source-pool comparisons, the RIGHT side is
intrinsic to the physical Kpt closure Z and is independent of
the arbitrary choice of which ambient original names represent it.

No anchor or nonempty cut-star assumption is needed. -/
theorem starProfile_upperL_iff_physical_of_exhaustive
    (P : HensonCutOccurrence ell cut hell)
    (hFullExact : ∀ v : Fin P.M,
      P.Full v ↔
        closureSelectedOriginal (hensonForbiddenFamily ell hell)
          P.ambient P.hAvoid P.original P.Z cut v)
    (hPool : ∀ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      z ∈ P.Z →
        ∃ v : Fin P.M,
          z ≤ P.ambient.kptOriginal
            (hensonForbiddenFamily ell hell) P.hAvoid (P.original v))
    (R : RelationalPrefixType (cut+1) 1 0 1) :
    P.starProfile.PrescribedUpperLType R ↔
      PhysicalCutStarUpperL (hensonForbiddenFamily ell hell) P.Z cut R := by
  classical
  have hGraph := fullProfile_graph_eq_physical_of_exhaustive
    P hFullExact hPool
  constructor
  · intro hAllowed
    obtain ⟨S,hS,hR⟩ := hAllowed
    obtain ⟨v,hStar,_hEligible,_hOld,hNext⟩ :=
      selectedStagePoolPrescribedData_source_original
        P.ambient cut P.original P.starNames S hS
    obtain ⟨z,hz,hCross,hBelow⟩ :=
      P.hRepresented v hStar.1
    have hOldRaw :
        (⟨cut,P.ambient.partialTypeAt cut (P.original v).val⟩ :
          RawPartialTypeNode 1 0 1) =
        (LevelTree.ancestor z cut (Nat.le_of_lt hCross)).val :=
      (kptBelowOriginal_ancestor_raw
        (hensonForbiddenFamily ell hell) P.ambient P.hAvoid
        (P.original v) z hBelow cut
        (Nat.le_of_lt hCross)).symm
    have hUpperRaw :
        (⟨cut+1,P.ambient.partialTypeAt (cut+1) (P.original v).val⟩ :
          RawPartialTypeNode 1 0 1) =
        (LevelTree.ancestor z (cut+1)
          (Nat.succ_le_iff.mpr hCross)).val :=
      (kptBelowOriginal_ancestor_raw
        (hensonForbiddenFamily ell hell) P.ambient P.hAvoid
        (P.original v) z hBelow (cut+1)
        (Nat.succ_le_iff.mpr hCross)).symm
    have hNextR :
        (P.ambient.partialTypeAt (cut+1) (P.original v).val).lReduct = R := by
      calc
        (P.ambient.partialTypeAt (cut+1) (P.original v).val).lReduct =
            (P.starProfile.target S).lReduct :=
          congrArg
            (fun Q : PartialTypeWithE (cut+1) 1 0 1 => Q.lReduct)
            hNext.symm
        _ = R := hR.symm
    have hBitName :
        (P.ambient.partialTypeAt (cut+1) (P.original v).val).lReduct.binary
          (some (⟨cut,Nat.lt_succ_self cut⟩ : Fin (cut+1)))
          none (0 : Fin 1) = true := by
      rw [partialTypeAt_lReduct_eq_ofAgeModel
        P.ambient (cut+1) (P.original v).val]
      change P.ambient.L.binary cut (P.original v).val (0 : Fin 1) = true
      exact hStar.2
    have hBitR :
        R.binary (some (⟨cut,Nat.lt_succ_self cut⟩ : Fin (cut+1)))
          none (0 : Fin 1) = true := by
      have hBitEq := congrArg
        (fun Q : RelationalPrefixType (cut+1) 1 0 1 =>
          Q.binary (some (⟨cut,Nat.lt_succ_self cut⟩ : Fin (cut+1)))
            none (0 : Fin 1)) hNextR
      exact hBitEq.symm.trans hBitName
    exact ⟨
      P.ambient.partialTypeAt cut (P.original v).val,
      P.ambient.partialTypeAt (cut+1) (P.original v).val,
      ⟨z,hz,hCross,hOldRaw,hUpperRaw⟩,
      hNextR,hBitR⟩
  · rintro ⟨T,U,hPhysical,hR,hBitR⟩
    have hFullPair :
        (T,U) ∈ fullPrescribedCrossingGraph P.fullProfile := by
      rw [hGraph]
      exact hPhysical
    obtain ⟨hS,hChosen⟩ := hFullPair
    obtain ⟨v,hFull,_hEligible,_hOld,hNext⟩ :=
      selectedStagePoolPrescribedData_source_original
        P.ambient cut P.original P.Full T hS
    have hUName :
        U = P.ambient.partialTypeAt (cut+1) (P.original v).val :=
      hChosen.symm.trans hNext
    have hNameR :
        (P.ambient.partialTypeAt (cut+1) (P.original v).val).lReduct = R := by
      rw [←hUName]
      exact hR
    have hBitName :
        (P.ambient.partialTypeAt (cut+1) (P.original v).val).lReduct.binary
          (some (⟨cut,Nat.lt_succ_self cut⟩ : Fin (cut+1)))
          none (0 : Fin 1) = true := by
      rw [hNameR]
      exact hBitR
    have hPhysicalEdge :
        P.ambient.L.binary cut (P.original v).val (0 : Fin 1) = true := by
      rw [partialTypeAt_lReduct_eq_ofAgeModel
        P.ambient (cut+1) (P.original v).val] at hBitName
      change P.ambient.L.binary cut (P.original v).val (0 : Fin 1) = true
        at hBitName
      exact hBitName
    have hStar : P.starNames v := ⟨hFull,hPhysicalEdge⟩
    have hAllowed := star_name_complete_upperL_permitted P v hStar
    rw [hNameR] at hAllowed
    exact hAllowed

/-- Cross-ambient FULL corrected B3 depends only on the actual
physical closure's POSITIVE-CUT ordinary-L projection, not the
chosen finite original-name pool or the entire dependent L+ source
graph, provided BOTH claimed FULL sources are certified exhaustive.

Common old L-socle and common source-cut coordinate are genuine
cross-occurrence hypotheses. Equality of intrinsic cut-star
spectra has NOT been derived from the proposed diary. -/
theorem full_B3_crossAmbient_iff_of_intrinsic_physical_cutStar
    (P Q : HensonCutOccurrence ell cut hell)
    (hFullP : ∀ v : Fin P.M,
      P.Full v ↔ closureSelectedOriginal (hensonForbiddenFamily ell hell)
        P.ambient P.hAvoid P.original P.Z cut v)
    (hPoolP : ∀ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      z ∈ P.Z →
        ∃ v : Fin P.M,
          z ≤ P.ambient.kptOriginal
            (hensonForbiddenFamily ell hell) P.hAvoid (P.original v))
    (hFullQ : ∀ v : Fin Q.M,
      Q.Full v ↔ closureSelectedOriginal (hensonForbiddenFamily ell hell)
        Q.ambient Q.hAvoid Q.original Q.Z cut v)
    (hPoolQ : ∀ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      z ∈ Q.Z →
        ∃ v : Fin Q.M,
          z ≤ Q.ambient.kptOriginal
            (hensonForbiddenFamily ell hell) Q.hAvoid (Q.original v))
    (hOld : SameInitialL P.ambient.L Q.ambient.L cut)
    (hPhysical : ∀ R : RelationalPrefixType (cut+1) 1 0 1,
      PhysicalCutStarUpperL (hensonForbiddenFamily ell hell) P.Z cut R ↔
      PhysicalCutStarUpperL (hensonForbiddenFamily ell hell) Q.Z cut R) :
    P.fullProfile.CorrectedB3 (hensonForbiddenFamily ell hell) ↔
    Q.fullProfile.CorrectedB3 (hensonForbiddenFamily ell hell) := by
  apply full_B3_crossAmbient_iff_of_cutStar_profiles P Q hOld
  intro R
  exact (starProfile_upperL_iff_physical_of_exhaustive
    P hFullP hPoolP R).trans
      ((hPhysical R).trans
        (starProfile_upperL_iff_physical_of_exhaustive
          Q hFullQ hPoolQ R).symm)

end HensonCutOccurrence

#print axioms HensonCutOccurrence.fullProfile_graph_eq_physical_of_exhaustive
#print axioms HensonCutOccurrence.starProfile_upperL_iff_physical_of_exhaustive
#print axioms HensonCutOccurrence.full_B3_crossAmbient_iff_of_intrinsic_physical_cutStar

end Kk
