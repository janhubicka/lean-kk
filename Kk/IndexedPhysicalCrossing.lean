import Kk.NumericHIndexedUpperRecords
import Kk.CrossClosurePhysicalComparison
import Mathlib.Tactic

/-!
# Track E: exact finite indexing of genuine physical crossing relations

The finite source index is constructed by the actual numerical-H+
AlgorithmRun via Track C. We show that its active nodes and full
old/upper L+ Option records enumerate ALL and ONLY the canonical
physical closure crossings, including competing (I2) crossings.

Across two *different* index domains the physical relations agree
when each actual crossing pair in one indexed trace has an identical
full L+ pair in the other direction. This matches pairs without
claiming an unjustified bijection of closure nodes or envelopes.

English-first adversarial audit:
  docs/track_e_indexed_physical_crossing_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The full physical crossing relation read from an indexed set of
actual Kpt nodes and the exact per-cut closure live mask. The source
pair MUST come from the same index; a live node not crossing the cut
has neither old nor upper Option value and contributes no edge. -/
def IndexedPhysicalCrossing
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {Params : Type}
    (node : Params → AdmissibleKptNode family)
    (presentAt : Nat → Params → Bool)
    (cut : Nat) :
    Set (PartialTypeWithE cut db du dd ×
      PartialTypeWithE (cut+1) db du dd) :=
  {p | ∃ j : Params, presentAt cut j = true ∧
    kptFullOldAtCut (node j) cut =
      some (⟨cut,p.1⟩ : RawPartialTypeNode db du dd) ∧
    kptFullUpperAtCut (node j) cut =
      some (⟨cut+1,p.2⟩ : RawPartialTypeNode db du dd)}

/-- Exact source coverage at ONE cut is sufficient to identify
the indexed complete old/upper L+ relation with the actual physical
consecutive-ancestor relation. No-(I2), finite original-name pool
or chosen prescribed target function is needed. -/
theorem indexed_physical_crossing_eq_full_closure_relation
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {Params : Type}
    (node : Params → AdmissibleKptNode family)
    (presentAt : Nat → Params → Bool)
    (Z : Set (AdmissibleKptNode family))
    (cut : Nat)
    (hExact : ∀ z : AdmissibleKptNode family,
      z ∈ Z ↔ ∃ j : Params,
        node j = z ∧ presentAt cut j = true) :
    IndexedPhysicalCrossing family node presentAt cut =
      FullPhysicalClosureCrossing family Z cut := by
  ext p
  constructor
  · rintro ⟨j,hLive,hOld,hUpper⟩
    let z : AdmissibleKptNode family := node j
    have hz : z ∈ Z := (hExact z).2 ⟨j,rfl,hLive⟩
    by_cases hCross : cut < LevelTree.lev z
    · have hRecords := kpt_full_old_upper_types_of_crossing z cut hCross
      have hOldRaw :
          (⟨cut,p.1⟩ : RawPartialTypeNode db du dd) =
            (LevelTree.ancestor z cut (Nat.le_of_lt hCross)).val := by
        have hEq := hOld.symm.trans hRecords.1
        exact Option.some.inj hEq
      have hUpperRaw :
          (⟨cut+1,p.2⟩ : RawPartialTypeNode db du dd) =
            (LevelTree.ancestor z (cut+1)
              (Nat.succ_le_iff.mpr hCross)).val := by
        have hEq := hUpper.symm.trans hRecords.2
        exact Option.some.inj hEq
      exact ⟨z,hz,hCross,hOldRaw,hUpperRaw⟩
    · have hNone := (kpt_full_old_upper_none_of_no_crossing
        z cut hCross).1
      rw [hNone] at hOld
      cases hOld
  · rintro ⟨z,hz,hCross,hOld,hUpper⟩
    obtain ⟨j,hNode,hLive⟩ := (hExact z).1 hz
    have hRecords := kpt_full_old_upper_types_of_crossing z cut hCross
    refine ⟨j,hLive,?_,?_⟩
    · rw [hNode]
      exact hRecords.1.trans (congrArg some hOld.symm)
    · rw [hNode]
      exact hRecords.2.trans (congrArg some hUpper.symm)

/-- One true finite numerical H+ AlgorithmRun has a SINGLE exhaustive
finite name set for its entire final Kpt closure. Its exact live mask
and complete old/upper L+ types reconstruct the ENTIRE physical
crossing relation at EACH cut in the same scan, including (I2).

The named universe is an actual Finset of Kpt nodes, not a set of
selected originals or a collection of noncanonical meet recipes.
The size of this finite index is NOT uniformly bounded by a diary.
-/
theorem numericH_actual_run_all_cuts_indexed_physical_crossing
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
      (∀ cut, cut < top →
        IndexedPhysicalCrossing family
          (fun j : Fin params.card => (params.equivFin.symm j).val)
          presentAt cut =
        FullPhysicalClosureCrossing family
          (SMTree.Envelope.closure (admissibleKptSTree family)
            (R.I (cut+1)) X) cut) := by
  classical
  obtain ⟨params,presentAt,hParams,_hInj,_hPresent,hCover⟩ :=
    finiteNumericH_actualRun_uniform_exhaustive_source_index
      family K k N hAvoid U X hX top R
  refine ⟨params,presentAt,hParams,?_⟩
  intro cut hCut
  exact indexed_physical_crossing_eq_full_closure_relation
    family
    (fun j : Fin params.card => (params.equivFin.symm j).val)
    presentAt
    (SMTree.Envelope.closure (admissibleKptSTree family)
      (R.I (cut+1)) X) cut
    (hCover cut hCut)

/-- Two independently indexed physical crossing sources agree if and
only if every ACTIVE, actual old/upper source pair in either index is
represented by an identical full L+ pair in the other index.

No equivalence of the raw finite index types is assumed. Different
numbers of names can represent the same crossing pair; this theorem
therefore compares source RELATIONS, not envelope multiplicities. -/
theorem indexed_physical_crossings_eq_of_two_sided_pair_matching
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {Params₁ Params₂ : Type}
    (node₁ : Params₁ → AdmissibleKptNode family)
    (node₂ : Params₂ → AdmissibleKptNode family)
    (live₁ : Nat → Params₁ → Bool)
    (live₂ : Nat → Params₂ → Bool)
    (cut : Nat)
    (h12 : ∀ (j : Params₁)
        (p : PartialTypeWithE cut db du dd ×
          PartialTypeWithE (cut+1) db du dd),
      live₁ cut j = true →
      kptFullOldAtCut (node₁ j) cut =
        some (⟨cut,p.1⟩ : RawPartialTypeNode db du dd) →
      kptFullUpperAtCut (node₁ j) cut =
        some (⟨cut+1,p.2⟩ : RawPartialTypeNode db du dd) →
      ∃ i : Params₂, live₂ cut i = true ∧
        kptFullOldAtCut (node₂ i) cut =
          some (⟨cut,p.1⟩ : RawPartialTypeNode db du dd) ∧
        kptFullUpperAtCut (node₂ i) cut =
          some (⟨cut+1,p.2⟩ : RawPartialTypeNode db du dd))
    (h21 : ∀ (j : Params₂)
        (p : PartialTypeWithE cut db du dd ×
          PartialTypeWithE (cut+1) db du dd),
      live₂ cut j = true →
      kptFullOldAtCut (node₂ j) cut =
        some (⟨cut,p.1⟩ : RawPartialTypeNode db du dd) →
      kptFullUpperAtCut (node₂ j) cut =
        some (⟨cut+1,p.2⟩ : RawPartialTypeNode db du dd) →
      ∃ i : Params₁, live₁ cut i = true ∧
        kptFullOldAtCut (node₁ i) cut =
          some (⟨cut,p.1⟩ : RawPartialTypeNode db du dd) ∧
        kptFullUpperAtCut (node₁ i) cut =
          some (⟨cut+1,p.2⟩ : RawPartialTypeNode db du dd)) :
    IndexedPhysicalCrossing family node₁ live₁ cut =
      IndexedPhysicalCrossing family node₂ live₂ cut := by
  ext p
  constructor
  · rintro ⟨j,hLive,hOld,hUpper⟩
    exact h12 j p hLive hOld hUpper
  · rintro ⟨j,hLive,hOld,hUpper⟩
    exact h21 j p hLive hOld hUpper

/-- The application-facing cross-occurrence criterion for two
DIFFERENT closures in the SAME normalized Kpt tree. Each closure
has its own exhaustive live index; bidirectional finite L+ pair
matching yields equality of their canonical complete physical
crossing relations at the aligned source cut, INCLUDING I2.

Track C now constructs such indices within each actual numerical-H+
AlgorithmRun. The still-open step is producing matching pairs from
the refined diary, with correct level normalization. -/
theorem two_physical_closures_crossing_eq_of_indexed_pair_matching
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {Params₁ Params₂ : Type}
    (Z₁ Z₂ : Set (AdmissibleKptNode family))
    (node₁ : Params₁ → AdmissibleKptNode family)
    (node₂ : Params₂ → AdmissibleKptNode family)
    (live₁ : Nat → Params₁ → Bool)
    (live₂ : Nat → Params₂ → Bool)
    (cut : Nat)
    (hExact₁ : ∀ z : AdmissibleKptNode family,
      z ∈ Z₁ ↔ ∃ j : Params₁,
        node₁ j = z ∧ live₁ cut j = true)
    (hExact₂ : ∀ z : AdmissibleKptNode family,
      z ∈ Z₂ ↔ ∃ j : Params₂,
        node₂ j = z ∧ live₂ cut j = true)
    (h12 : ∀ (j : Params₁)
        (p : PartialTypeWithE cut db du dd ×
          PartialTypeWithE (cut+1) db du dd),
      live₁ cut j = true →
      kptFullOldAtCut (node₁ j) cut =
        some (⟨cut,p.1⟩ : RawPartialTypeNode db du dd) →
      kptFullUpperAtCut (node₁ j) cut =
        some (⟨cut+1,p.2⟩ : RawPartialTypeNode db du dd) →
      ∃ i : Params₂, live₂ cut i = true ∧
        kptFullOldAtCut (node₂ i) cut =
          some (⟨cut,p.1⟩ : RawPartialTypeNode db du dd) ∧
        kptFullUpperAtCut (node₂ i) cut =
          some (⟨cut+1,p.2⟩ : RawPartialTypeNode db du dd))
    (h21 : ∀ (j : Params₂)
        (p : PartialTypeWithE cut db du dd ×
          PartialTypeWithE (cut+1) db du dd),
      live₂ cut j = true →
      kptFullOldAtCut (node₂ j) cut =
        some (⟨cut,p.1⟩ : RawPartialTypeNode db du dd) →
      kptFullUpperAtCut (node₂ j) cut =
        some (⟨cut+1,p.2⟩ : RawPartialTypeNode db du dd) →
      ∃ i : Params₁, live₁ cut i = true ∧
        kptFullOldAtCut (node₁ i) cut =
          some (⟨cut,p.1⟩ : RawPartialTypeNode db du dd) ∧
        kptFullUpperAtCut (node₁ i) cut =
          some (⟨cut+1,p.2⟩ : RawPartialTypeNode db du dd)) :
    FullPhysicalClosureCrossing family Z₁ cut =
      FullPhysicalClosureCrossing family Z₂ cut := by
  rw [← indexed_physical_crossing_eq_full_closure_relation
        family node₁ live₁ Z₁ cut hExact₁,
      ← indexed_physical_crossing_eq_full_closure_relation
        family node₂ live₂ Z₂ cut hExact₂]
  exact indexed_physical_crossings_eq_of_two_sided_pair_matching
    family node₁ node₂ live₁ live₂ cut h12 h21

end Kk
