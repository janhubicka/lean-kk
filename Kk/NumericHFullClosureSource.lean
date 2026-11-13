import Kk.NumericHTopParameterClosure
import Kk.NumericHFullSelectedColumn
import SuccessorTree.V10.KptStageClosureNormalForm
import SuccessorTree.V10.HPositiveFreeLevelOdd
import Mathlib.Tactic

/-!
# Track C: first exact finite dependent H+ source record

English mathematical proof and adversarial checks were committed FIRST:
`docs/track_c_full_source_english_audit.md`.

We assemble an actual numerical-H+ top original's COMPLETE incoming auxiliary
E cut (including fake coordinates), its canonical free level, and the
complete, two-direction L and incoming E columns from EVERY earlier genuine
original at EVERY generation, including generation zero.

A separate theorem packages a real AlgorithmRun-selected generation-one
parameter with the actual positive free-level tests and its membership in
the lower full Kpt meet-and-parameter closure.

These are *restricted* source records. We do NOT identify all fake/parameter
crossing types, their upper L+ assignments, the complete corrected B3
profile, or any common labelled inverse-source orbit.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A physically realized top H+ source record, with an exact E column
on ALL numerical coordinates, canonical free level, all previous REAL
generations and both directed binary L bits. The earlier coordinate
is explicitly certified to be inside the finite H+ carrier.

The incoming E bit is independent of the base L bit. This is not a
claim that every fake E-predecessor lies in Kpt parameter closure. -/
theorem finiteNumericH_top_full_original_source_record
    (e : Nat → Nat → Bool)
    (hSym : ∀ i j, e i j = e j i)
    (k N j : Nat) (hk : 0 < k) (hj : 0 < j)
    (hTop : hPosition k j k < N) :
    (∀ u : Nat,
      (finiteNumericH (normalizedGraphModel e) k N).E
          u (hPosition k j k) = true ↔
        u < hPosition k (j-1) k + 1) ∧
    (finiteNumericH (normalizedGraphModel e) k N).freeLevel
        (hPosition k j k) = hPosition k (j-1) k + 1 ∧
    (∀ i q : Nat, i < j → q ≤ k →
      hPosition k i q < N ∧
      (finiteNumericH (normalizedGraphModel e) k N).L.binary
        (hPosition k i q) (hPosition k j k) (0 : Fin 1) = e i j ∧
      (finiteNumericH (normalizedGraphModel e) k N).L.binary
        (hPosition k j k) (hPosition k i q) (0 : Fin 1) = e j i ∧
      (finiteNumericH (normalizedGraphModel e) k N).E
        (hPosition k i q) (hPosition k j k) = true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u
    exact finiteNumericH_top_auxE_true_iff
      (normalizedGraphModel e) k N j u hk hj hTop
  · exact finiteNumericH_top_freeLevel_exact
      (normalizedGraphModel e) k N j hk hj hTop
  · intro i q hij hq
    have hOld : hPosition k i q < N :=
      (hPosition_lt_of_block_lt k i j q k hq hij).trans hTop
    have hL :=
      numericH_henson_top_full_column_both e hSym k i j q hij hq
    have hEBit :
        (finiteNumericH (normalizedGraphModel e) k N).E
          (hPosition k i q) (hPosition k j k) = true := by
      change finiteNumericHE k N
        (hPosition k i q) (hPosition k j k) = true
      exact (finiteNumericHE_true_iff k N _ _).2
        ⟨hTop, numericH_top_auxE_all_earlier_real
          k i j q hk hj hij hq⟩
    exact ⟨hOld, hL.1, hL.2, hEBit⟩

/-- Any odd fake numerical coordinate below the REAL top free cut has
a positive incoming E bit while being distinct from every real H
coordinate (at any block/generation). Such E-positive fake locations
cannot be silently discarded when auditing full dependent sources. -/
theorem finiteNumericH_top_fake_E_positive_not_real
    {db du dd : Nat} (K : AgeTestModel db du dd)
    (k N j a : Nat) (hk : 0 < k) (hj : 0 < j)
    (hTop : hPosition k j k < N)
    (hBelow : 2*a+1 < hPosition k (j-1) k + 1) :
    (finiteNumericH K k N).E (2*a+1) (hPosition k j k) = true ∧
      (∀ i q : Nat, 2*a+1 ≠ hPosition k i q) := by
  constructor
  · exact (finiteNumericH_top_auxE_true_iff
      K k N j (2*a+1) hk hj hTop).2 hBelow
  · intro i q heq
    obtain ⟨t, ht⟩ := hPosition_even k i q
    omega


/-- A fake odd numerical coordinate can lie below the true incoming
auxiliary E cut while carrying ZERO directed binary L atoms in EVERY
sort and BOTH orientations. Its positive E bit neither creates a graph
edge nor identifies it as a genuine original or a closure parameter. -/
theorem finiteNumericH_top_fake_full_L_plus
    {db du dd : Nat} (K : AgeTestModel db du dd)
    (k N j a : Nat) (hk : 0 < k) (hj : 0 < j)
    (hTop : hPosition k j k < N)
    (hBelow : 2*a+1 < hPosition k (j-1) k + 1) :
    (finiteNumericH K k N).E (2*a+1) (hPosition k j k) = true ∧
    (∀ r : Fin db,
      (finiteNumericH K k N).L.binary
        (2*a+1) (hPosition k j k) r = false ∧
      (finiteNumericH K k N).L.binary
        (hPosition k j k) (2*a+1) r = false) ∧
    (∀ i q : Nat, 2*a+1 ≠ hPosition k i q) := by
  obtain ⟨hE,hFake⟩ := finiteNumericH_top_fake_E_positive_not_real
    K k N j a hk hj hTop hBelow
  refine ⟨hE, ?_, hFake⟩
  intro r
  constructor
  · change hNumericBinary K.binary k
      (2*a+1) (hPosition k j k) r = false
    exact hNumericBinary_odd_left_false K.binary k a (hPosition k j k) r
  · change hNumericBinary K.binary k
      (hPosition k j k) (2*a+1) r = false
    exact hNumericBinary_odd_right_false K.binary k (hPosition k j k) a r

/-- In a genuine AlgorithmRun, a selected earlier generation-one
source below a seeded TOP original has both necessary numerical
free-level inequalities AND a true Kpt original in every lower
full parameter-closed source. A positive E bit alone is NOT sufficient:
the run-selection and genuine seed hypotheses are retained. -/
theorem finiteNumericH_run_selected_genOne_full_source_eligibility
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N i j : Nat)
    (hk : 1 < k) (hi : 0 < i) (hij : i < j)
    (hTop : hPosition k j k < N)
    (hFiniteAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (X : Set (AdmissibleKptNode family))
    (hSeed :
      (finiteNumericH K k N).kptOriginal family hFiniteAvoid
        (⟨hPosition k j k, by
          change hPosition k j k < N
          exact hTop⟩ : Fin (finiteNumericH K k N).size) ∈ X)
    (runHeight : Nat) (hScan : hPosition k i 1 < runHeight)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X runHeight)
    (hSelected : hPosition k i 1 ∈ R.I (hPosition k i 1))
    (p : Nat) (hp : p < hPosition k i 1) :
    0 < (finiteNumericH K k N).freeLevel (hPosition k i 1) ∧
      hPosition k i 1 <
        (finiteNumericH K k N).freeLevel (hPosition k j k) ∧
      ∃ hiCarrier : hPosition k i 1 < (finiteNumericH K k N).size,
        (finiteNumericH K k N).kptOriginal family hFiniteAvoid
          (⟨hPosition k i 1, hiCarrier⟩ :
            Fin (finiteNumericH K k N).size) ∈
          SMTree.Envelope.closure
            (admissibleKptSTree family) (R.I (p+1)) X := by
  have hPos :
      0 < (finiteNumericH K k N).freeLevel (hPosition k i 1) :=
    (finiteNumericH_earlier_generation_one_positive_freeLevel
      K k N i j hk hi hij hTop).2
  have hBelow :
      hPosition k i 1 <
        (finiteNumericH K k N).freeLevel (hPosition k j k) :=
    finiteNumericH_generation_one_before_top_freeLevel
      K k N i j hk hi hij hTop
  obtain ⟨hiCarrier, hSource⟩ :=
    finiteNumericH_run_selected_genOne_in_lower_closure
      family K k N i j hk hi hij hTop hFiniteAvoid
      X hSeed runHeight hScan R hSelected p hp
  exact ⟨hPos, hBelow, hiCarrier, hSource⟩


/-- The ACTUAL numerical-H+ meet-and-parameter closure has no fourth
sort of node: each closure source is a seed, a selected positive
original parameter, or a meet of two full ambient original types
from the maintained stage pool.

The seed pool must have a genuine ambient original-prefix
representation. This theorem does NOT identify the actual assigned
upper L+ type of each cut-crossing source. -/
theorem finiteNumericH_all_closure_nodes_seed_parameter_or_meet
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (I : Set Nat) (X : Set (AdmissibleKptNode family))
    (U : Set (Fin (finiteNumericH K k N).size))
    (hSeeds : X ⊆
      ambientPrefixPool family (finiteNumericH K k N) hAvoid U)
    (z : AdmissibleKptNode family)
    (hz : z ∈ SMTree.Envelope.closure
      (admissibleKptSTree family) I X) :
    z ∈ X ∨
    (∃ v : Fin (finiteNumericH K k N).size,
      v.val ∈ I ∧
      0 < (finiteNumericH K k N).freeLevel v.val ∧
      z = (finiteNumericH K k N).kptOriginal family hAvoid v) ∨
    (∃ v : Fin (finiteNumericH K k N).size,
      v ∈ ambientStagePool (finiteNumericH K k N) U I ∧
      ∃ w : Fin (finiteNumericH K k N).size,
        w ∈ ambientStagePool (finiteNumericH K k N) U I ∧
        SMTree.Envelope.SameComponent
          ((finiteNumericH K k N).kptOriginal family hAvoid v)
          ((finiteNumericH K k N).kptOriginal family hAvoid w) ∧
        z = LevelTree.meet
          ((finiteNumericH K k N).kptOriginal family hAvoid v)
          ((finiteNumericH K k N).kptOriginal family hAvoid w)) := by
  exact admissibleKpt_actual_stage_closure_normalForm
    family (finiteNumericH K k N) hAvoid I X U hSeeds hz

/-- A non-SEED closure node at any genuine even numerical H level
cannot be a selected positive original parameter (whose canonical
free level is necessarily odd). Consequently it is a MEET of two
full actual ambient originals from the maintained stage pool.

This is an all-closure-node I1 source classification, conditional on
representation of the seed pool. It proves neither that an I1 event
occurs nor that the two originals lie in a smaller selected-front pool. -/
theorem finiteNumericH_even_real_level_nonseed_is_original_meet
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (I : Set Nat) (X : Set (AdmissibleKptNode family))
    (U : Set (Fin (finiteNumericH K k N).size))
    (hSeeds : X ⊆
      ambientPrefixPool family (finiteNumericH K k N) hAvoid U)
    (z : AdmissibleKptNode family)
    (i q : Nat) (hLevel : LevelTree.lev z = hPosition k i q)
    (hz : z ∈ SMTree.Envelope.closure
      (admissibleKptSTree family) I X)
    (hNotSeed : z ∉ X) :
    ∃ v : Fin (finiteNumericH K k N).size,
      v ∈ ambientStagePool (finiteNumericH K k N) U I ∧
      ∃ w : Fin (finiteNumericH K k N).size,
        w ∈ ambientStagePool (finiteNumericH K k N) U I ∧
        SMTree.Envelope.SameComponent
          ((finiteNumericH K k N).kptOriginal family hAvoid v)
          ((finiteNumericH K k N).kptOriginal family hAvoid w) ∧
        z = LevelTree.meet
          ((finiteNumericH K k N).kptOriginal family hAvoid v)
          ((finiteNumericH K k N).kptOriginal family hAvoid w) := by
  apply admissibleKpt_actual_closure_node_original_meet
    family (finiteNumericH K k N) hAvoid I X U
    hSeeds z hz hNotSeed
  rintro ⟨v, _, hPos, hEq⟩
  have hActualLevel :
      LevelTree.lev z =
        (finiteNumericH K k N).freeLevel v.val := by
    rw [hEq]
    rfl
  have hEvenFree :
      (finiteNumericH K k N).freeLevel v.val = hPosition k i q :=
    hActualLevel.symm.trans hLevel
  exact (finiteNumericH_positive_freeLevel_ne_realPosition
    K k N v.val i q v.isLt hPos) hEvenFree

#print axioms Kk.finiteNumericH_top_full_original_source_record
#print axioms Kk.finiteNumericH_top_fake_E_positive_not_real
#print axioms Kk.finiteNumericH_top_fake_full_L_plus
#print axioms Kk.finiteNumericH_all_closure_nodes_seed_parameter_or_meet
#print axioms Kk.finiteNumericH_even_real_level_nonseed_is_original_meet
#print axioms Kk.finiteNumericH_run_selected_genOne_full_source_eligibility

end Kk
