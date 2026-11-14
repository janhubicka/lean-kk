import Kk.NumericHI2FullFork
import Kk.FullPhysicalCrossingRelation
import Mathlib.Tactic

/-!
# Track C: exact physical meaning of the full indexed I2 fork

English proof and adversarial audit committed BEFORE this file:
  docs/track_c_physical_i2_relation_english_audit.md

The full physical Kpt crossing relation is meaningful even when it
is not the graph of any prescribed SINGLE-VALUED source function.
The already verified Track E converse says nonfunctionality forces
an I2 meet. Here we prove the reverse under the mathematically
indispensable no-I1 condition and connect the physical fork to
Track C's finite full-Kpt active source index.

We do NOT identify distinct occurrences or assume away the genuine
K4 auxiliary microlevels. No artificial E on an L-only age witness.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A genuine crossing Kpt node z has EXACT complete old/upper L+
type witnesses in the canonical full physical crossing relation.
The values are obtained by literal dependent restrictions of the
SAME raw Kpt record, not by an independently chosen graph model.

Both values also agree with the complete optional raw ancestor
records used by the finite indexed Track C source. -/
theorem kpt_actual_crossing_has_physical_full_pair
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family))
    (cut : Nat)
    (z : AdmissibleKptNode family)
    (hz : z ∈ Z)
    (hCut : cut < LevelTree.lev z) :
    ∃ T : PartialTypeWithE cut db du dd,
      ∃ U : PartialTypeWithE (cut+1) db du dd,
        (T,U) ∈ FullPhysicalClosureCrossing family Z cut ∧
        kptFullOldAtCut z cut =
          some (⟨cut,T⟩ : RawPartialTypeNode db du dd) ∧
        kptFullUpperAtCut z cut =
          some (⟨cut+1,U⟩ : RawPartialTypeNode db du dd) := by
  let T : PartialTypeWithE cut db du dd :=
    z.val.2.restrict (Nat.le_of_lt hCut)
  let U : PartialTypeWithE (cut+1) db du dd :=
    z.val.2.restrict (Nat.succ_le_iff.mpr hCut)
  have hOld :
      (⟨cut,T⟩ : RawPartialTypeNode db du dd) =
        (LevelTree.ancestor z cut (Nat.le_of_lt hCut)).val := by
    change
      (⟨cut,z.val.2.restrict (Nat.le_of_lt hCut)⟩ :
        RawPartialTypeNode db du dd) =
        (LevelTree.ancestor z cut (Nat.le_of_lt hCut)).val
    rw [admissibleKpt_levelTree_ancestor_eq]
    rfl
  have hUpper :
      (⟨cut+1,U⟩ : RawPartialTypeNode db du dd) =
        (LevelTree.ancestor z (cut+1) (Nat.succ_le_iff.mpr hCut)).val := by
    change
      (⟨cut+1,z.val.2.restrict (Nat.succ_le_iff.mpr hCut)⟩ :
        RawPartialTypeNode db du dd) =
        (LevelTree.ancestor z (cut+1) (Nat.succ_le_iff.mpr hCut)).val
    rw [admissibleKpt_levelTree_ancestor_eq]
    rfl
  have hPair : (T,U) ∈ FullPhysicalClosureCrossing family Z cut :=
    ⟨z,hz,hCut,hOld,hUpper⟩
  have hRaw := kpt_full_old_upper_types_of_crossing z cut hCut
  refine ⟨T,U,hPair,?_,?_⟩
  · calc
      kptFullOldAtCut z cut =
          some (LevelTree.ancestor z cut (Nat.le_of_lt hCut)).val := hRaw.1
      _ = some (⟨cut,T⟩ : RawPartialTypeNode db du dd) :=
        congrArg some hOld.symm
  · calc
      kptFullUpperAtCut z cut =
          some (LevelTree.ancestor z (cut+1)
            (Nat.succ_le_iff.mpr hCut)).val := hRaw.2
      _ = some (⟨cut+1,U⟩ : RawPartialTypeNode db du dd) :=
        congrArg some hUpper.symm

/-- Distinct complete upper L+ options over one old raw type
produce TWO actual physical crossing pairs with the SAME source
and DISTINCT upper values. This direction needs no no-I1 premise. -/
theorem kpt_full_fork_forces_physical_crossing_nonfunctional
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family))
    (cut : Nat)
    (hFork : KptFullCutFork family Z cut) :
    ∃ T : PartialTypeWithE cut db du dd,
      ∃ U V : PartialTypeWithE (cut+1) db du dd,
        (T,U) ∈ FullPhysicalClosureCrossing family Z cut ∧
        (T,V) ∈ FullPhysicalClosureCrossing family Z cut ∧
        U ≠ V := by
  obtain ⟨a,ha,b,hb,hCutA,hCutB,hSameOld,hDifferentUpper⟩ := hFork
  obtain ⟨T,U,hPairA,hOldA,hUpperA⟩ :=
    kpt_actual_crossing_has_physical_full_pair
      family Z cut a ha hCutA
  obtain ⟨S,V,hPairB,hOldB,hUpperB⟩ :=
    kpt_actual_crossing_has_physical_full_pair
      family Z cut b hb hCutB
  have hRawOld :
      (⟨cut,T⟩ : RawPartialTypeNode db du dd) =
        (⟨cut,S⟩ : RawPartialTypeNode db du dd) := by
    apply Option.some.inj
    calc
      some (⟨cut,T⟩ : RawPartialTypeNode db du dd) =
          kptFullOldAtCut a cut := hOldA.symm
      _ = kptFullOldAtCut b cut := hSameOld
      _ = some (⟨cut,S⟩ : RawPartialTypeNode db du dd) := hOldB
  have hSameType : T = S :=
    eq_of_heq (Sigma.mk.inj_iff.mp hRawOld).2
  have hNextDiff : U ≠ V := by
    intro heq
    apply hDifferentUpper
    calc
      kptFullUpperAtCut a cut =
          some (⟨cut+1,U⟩ : RawPartialTypeNode db du dd) := hUpperA
      _ = some (⟨cut+1,V⟩ : RawPartialTypeNode db du dd) :=
          congrArg (fun t : PartialTypeWithE (cut+1) db du dd =>
            some (⟨cut+1,t⟩ : RawPartialTypeNode db du dd)) heq
      _ = kptFullUpperAtCut b cut := hUpperB.symm
  refine ⟨T,U,V,hPairA,?_,hNextDiff⟩
  simpa only [hSameType] using hPairB

/-- Precise no-(I1) equivalence: a genuine competing I2 cut-level
meet exists iff the canonical complete physical L+ crossing relation
is NOT the graph of a function. The reverse physical-fork-to-meet
direction was verified independently by Track E. -/
theorem kpt_no_I1_I2_iff_physical_crossing_nonfunctional
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family))
    (cut : Nat)
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ Z ∧ LevelTree.lev z = cut) :
    (∃ a : AdmissibleKptNode family, a ∈ Z ∧
      ∃ b : AdmissibleKptNode family, b ∈ Z ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) ↔
    (∃ T : PartialTypeWithE cut db du dd,
      ∃ U V : PartialTypeWithE (cut+1) db du dd,
        (T,U) ∈ FullPhysicalClosureCrossing family Z cut ∧
        (T,V) ∈ FullPhysicalClosureCrossing family Z cut ∧
        U ≠ V) := by
  constructor
  · intro hMeet
    exact kpt_full_fork_forces_physical_crossing_nonfunctional
      family Z cut
      ((kpt_no_I1_I2_iff_complete_full_fork
        family Z cut hNoI1).mp hMeet)
  · rintro ⟨T,U,V,hU,hV,hDifferent⟩
    exact full_physical_crossing_nonfunctional_forces_I2
      family Z cut T U V hU hV hDifferent

/-- Concrete Track C → E interface: in one genuine finite numerical
H+ AlgorithmRun without I1 at cut, the exact two-index active
complete-L+ fork certificate is equivalent to nonfunctionality of
the choice-free FULL physical crossing relation.

The finite index and its masks can be constructed by the existing
Track C run-index theorem. We do not assert cross-occurrence
synchronization, a monoid source orbit, or corrected B3. -/
theorem finiteNumericH_run_indexed_I2_iff_physical_nonfunctional
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Set (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hSeeds : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid U)
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (params : Finset (AdmissibleKptNode family))
    (hParams : ∀ z : AdmissibleKptNode family,
      z ∈ params ↔
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I 0) X)
    (presentAt : Nat → Fin params.card → Bool)
    (hPresent : ∀ cut : Nat, ∀ i : Fin params.card,
      presentAt cut i = true ↔
        (params.equivFin.symm i).val ∈
          SMTree.Envelope.closure (admissibleKptSTree family)
            (R.I (cut+1)) X)
    (cut : Nat) (hCut : cut < top)
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X ∧
      LevelTree.lev z = cut) :
    let Z : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1)) X
    (∃ i j : Fin params.card,
      presentAt cut i = true ∧ presentAt cut j = true ∧
      cut < LevelTree.lev (params.equivFin.symm i).val ∧
      cut < LevelTree.lev (params.equivFin.symm j).val ∧
      kptFullOldAtCut (params.equivFin.symm i).val cut =
        kptFullOldAtCut (params.equivFin.symm j).val cut ∧
      kptFullUpperAtCut (params.equivFin.symm i).val cut ≠
        kptFullUpperAtCut (params.equivFin.symm j).val cut) ↔
    (∃ T : PartialTypeWithE cut db du dd,
      ∃ U V : PartialTypeWithE (cut+1) db du dd,
        (T,U) ∈ FullPhysicalClosureCrossing family Z cut ∧
        (T,V) ∈ FullPhysicalClosureCrossing family Z cut ∧
        U ≠ V) := by
  let Z : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (R.I (cut+1)) X
  calc
    (∃ i j : Fin params.card,
      presentAt cut i = true ∧ presentAt cut j = true ∧
      cut < LevelTree.lev (params.equivFin.symm i).val ∧
      cut < LevelTree.lev (params.equivFin.symm j).val ∧
      kptFullOldAtCut (params.equivFin.symm i).val cut =
        kptFullOldAtCut (params.equivFin.symm j).val cut ∧
      kptFullUpperAtCut (params.equivFin.symm i).val cut ≠
        kptFullUpperAtCut (params.equivFin.symm j).val cut) ↔
      (∃ a : AdmissibleKptNode family, a ∈ Z ∧
        ∃ b : AdmissibleKptNode family, b ∈ Z ∧
          SMTree.Envelope.SameComponent a b ∧
          LevelTree.lev (LevelTree.meet a b) = cut) :=
        (finiteNumericH_run_no_I1_I2_iff_indexed_full_fork
          family K k N hAvoid U X hSeeds top R
          params hParams presentAt hPresent cut hCut hNoI1).symm
    _ ↔ (∃ T : PartialTypeWithE cut db du dd,
      ∃ U V : PartialTypeWithE (cut+1) db du dd,
        (T,U) ∈ FullPhysicalClosureCrossing family Z cut ∧
        (T,V) ∈ FullPhysicalClosureCrossing family Z cut ∧
        U ≠ V) :=
          kpt_no_I1_I2_iff_physical_crossing_nonfunctional
            family Z cut hNoI1

#print axioms Kk.kpt_actual_crossing_has_physical_full_pair
#print axioms Kk.kpt_full_fork_forces_physical_crossing_nonfunctional
#print axioms Kk.kpt_no_I1_I2_iff_physical_crossing_nonfunctional
#print axioms Kk.finiteNumericH_run_indexed_I2_iff_physical_nonfunctional

end Kk
