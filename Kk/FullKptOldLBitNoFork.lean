import Kk.NumericHStructuralCutClassifier
import Kk.NumericHI2FullFork
import Mathlib.Tactic

/-!
# Track D: OLD ordinary-L bit certificates exclude FULL dependent Kpt I2

English-first proof and 19 hostile checks committed first:
docs/audits/2026-11-16-track-d-full-kpt-old-L-bit-no-fork-english.md

A full old Kpt raw record is an Option (RawPartialTypeNode),
not a selected graph age. We use a concrete old ordinary-L bit
at a genuine coordinate Fin cut to separate the entire full
dependent old L+ records of two ACTUAL Kpt source nodes.

Under NO full I1 endpoint, the already kernel-checked I2/fork
equivalence converts exhaustive OLD-ordinary-bit certificates
for EVERY pair of genuine active upper-distinct nodes into NO I2.
The finite-index version uses the real final Kpt node index
and true pre-cut presence mask.

This is a sufficient full-(I2) exclusion *interface*, not
verification of the pairwise hypotheses for the proposed resolved
independent-set Q. In particular the selected-vs-negative-auxiliary
generation-zero separator is not automatically exhaustive.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- An explicit OLD ordinary-L bit distinguishing the complete
dependent L+ source records of two genuine Kpt nodes crossing
one cut. Both old records are actual complete raw prefix types,
not a chosen diary shadow. The same old coordinate q<cut has
different directed old-to-future L binary atoms.

This predicate is stronger than mere inequality of full old
records, because auxiliary E (or other atoms) may distinguish
old records even if ordinary L does not. -/
def KptOldOrdinaryBitSeparation
    {family : List (NormalizedForbidden 1 0 1)}
    (a b : AdmissibleKptNode family) (cut : Nat) : Prop :=
  ∃ T U : PartialTypeWithE cut 1 0 1,
    kptFullOldAtCut a cut =
      some (⟨cut,T⟩ : RawPartialTypeNode 1 0 1) ∧
    kptFullOldAtCut b cut =
      some (⟨cut,U⟩ : RawPartialTypeNode 1 0 1) ∧
    ∃ q : Fin cut,
      T.lReduct.binary (some q) none (0 : Fin 1) ≠
        U.lReduct.binary (some q) none (0 : Fin 1)

/-- One explicit old ordinary bit separator forces the two
COMPLETE full dependent L+ raw OLD records to differ.
The full auxiliary E components remain present in each record. -/
theorem kpt_old_ordinary_bit_separation_forces_full_old_distinct
    {family : List (NormalizedForbidden 1 0 1)}
    (a b : AdmissibleKptNode family) (cut : Nat)
    (hSep : KptOldOrdinaryBitSeparation a b cut) :
    kptFullOldAtCut a cut ≠ kptFullOldAtCut b cut := by
  rintro hOld
  obtain ⟨T,U,hA,hB,q,hBit⟩ := hSep
  have hSome :
      (some (⟨cut,T⟩ : RawPartialTypeNode 1 0 1)) =
      some (⟨cut,U⟩ : RawPartialTypeNode 1 0 1) :=
    hA.symm.trans (hOld.trans hB)
  have hRaw :
      (⟨cut,T⟩ : RawPartialTypeNode 1 0 1) =
        ⟨cut,U⟩ := Option.some.inj hSome
  have hTU : T = U := by
    cases hRaw
    rfl
  exact hBit (congrArg
    (fun R : PartialTypeWithE cut 1 0 1 =>
      R.lReduct.binary (some q) none (0 : Fin 1)) hTU)

/-- If there is no genuine I1 endpoint in a FULL Kpt source Z,
and every pair of its ACTUAL crossing Kpt nodes whose complete
next-L+ records differ is already separated by a concrete OLD
ordinary-L bit, then NO same-component I2 meet occurs at cut.

The universal quantifier includes all generated Kpt meet and
auxiliary parameter nodes; selected diary branches alone do
not satisfy the premise. -/
theorem kpt_no_I2_of_all_upper_mismatches_have_old_L_bit
    (family : List (NormalizedForbidden 1 0 1))
    (Z : Set (AdmissibleKptNode family)) (cut : Nat)
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ Z ∧ LevelTree.lev z = cut)
    (hAllOldSeparated :
      ∀ a : AdmissibleKptNode family, a ∈ Z →
      ∀ b : AdmissibleKptNode family, b ∈ Z →
        cut < LevelTree.lev a →
        cut < LevelTree.lev b →
        kptFullUpperAtCut a cut ≠
          kptFullUpperAtCut b cut →
        KptOldOrdinaryBitSeparation a b cut) :
    ¬ KptI2MeetAtCut family Z cut := by
  intro hI2
  obtain ⟨a,ha,b,hb,hCa,hCb,hOld,hUpper⟩ :=
    (kpt_no_I1_I2_iff_complete_full_fork
      family Z cut hNoI1).mp hI2
  have hSep := hAllOldSeparated a ha b hb hCa hCb hUpper
  exact (kpt_old_ordinary_bit_separation_forces_full_old_distinct
    a b cut hSep) hOld

/-- In the true finite numerical-H AlgorithmRun, a single EXACT
final full-Kpt node index and its REAL per-cut membership masks
turn the OLD ordinary-L bit separation criterion into a finite
check on all active strictly crossing upper-distinct node pairs.

The source index is of closure(R.I 0,X); the actual pre-cut source
is closure(R.I(cut+1),X). The fully qualified uniform index and
mask hypotheses must not be weakened to selected graph ages.

No I1 is still required: trivial I1 self-meets do not make a
strictly crossing two-upper-type fork. -/
theorem finiteNumericH_run_no_I2_of_indexed_old_L_bit_separators
    (family : List (NormalizedForbidden 1 0 1))
    (K : AgeTestModel 1 0 1) (k N : Nat)
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
          SMTree.Envelope.closure
            (admissibleKptSTree family) (R.I (cut+1)) X)
    (cut : Nat) (hCut : cut < top)
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X ∧
      LevelTree.lev z = cut)
    (hAllActiveSeparated :
      ∀ i j : Fin params.card,
        presentAt cut i = true →
        presentAt cut j = true →
        cut < LevelTree.lev (params.equivFin.symm i).val →
        cut < LevelTree.lev (params.equivFin.symm j).val →
        kptFullUpperAtCut (params.equivFin.symm i).val cut ≠
          kptFullUpperAtCut (params.equivFin.symm j).val cut →
        KptOldOrdinaryBitSeparation
          (params.equivFin.symm i).val
          (params.equivFin.symm j).val cut) :
    ¬ KptI2MeetAtCut family
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X) cut := by
  classical
  intro hI2
  obtain ⟨i,j,hi,hj,hCi,hCj,hOld,hUpper⟩ :=
    (finiteNumericH_run_no_I1_I2_iff_indexed_full_fork
      family K k N hAvoid U X hSeeds top R
      params hParams presentAt hPresent cut hCut hNoI1).mp hI2
  have hSep :=
    hAllActiveSeparated i j hi hj hCi hCj hUpper
  exact (kpt_old_ordinary_bit_separation_forces_full_old_distinct
    (params.equivFin.symm i).val (params.equivFin.symm j).val
    cut hSep) hOld

#print axioms kpt_old_ordinary_bit_separation_forces_full_old_distinct
#print axioms kpt_no_I2_of_all_upper_mismatches_have_old_L_bit
#print axioms finiteNumericH_run_no_I2_of_indexed_old_L_bit_separators

end Kk
