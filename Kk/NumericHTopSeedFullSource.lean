import Kk.NumericHFullClosureCrossing
import SuccessorTree.V10.HTopGenerationSeeds
import Mathlib.Tactic

/-!
# Track C: actual top-generation Kpt seeds yield full H+ source records

English proof and hostile review COMMITTED FIRST:
 docs/track_c_top_seed_full_source_english_audit.md

These results remove the free-standing original-prefix seed-pool
hypothesis of the previous Track C full crossing theorem for the
ACTUAL top-generation numeric H+ seed construction. Such seeds are
one genuine finite H+ root and its prescribed top-generation prefixes.

The canonical stage-pool invariant contains all Kpt meet/parameter
closure nodes. Under the precise no-competing-(I2) meet at the tested
cut, we obtain BOTH directions of the real closure crossing graph
and complete assigned old and upper L+ source records, with a
genuine nonfake numerical H target for each source input.

Neither the recursively prescribed multi-stage resolved diary nor
the common labelled inverse-source orbit is proved here.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- For the ACTUAL finite numerical H+ top-generation seed family,
the full meet-and-parameter closure at ANY selected level set I
is represented by the root original and the selected positive
parameter originals. The seed-pool hypothesis has been discharged
using the genuine top-generation source lemma, and finite forbidden
avoidance is transferred from the original age model K. -/
theorem finiteNumericH_topSeeds_closure_inside_root_stage_pool
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N : Nat) (c : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ i : Nat, i ∈ blocks →
      hPosition k i k ≤ (finiteNumericH K k N).freeLevel c.val)
    (I : Set Nat) :
    SMTree.Envelope.closure (admissibleKptSTree family) I
      (numericHTopGenerationSeeds family K k N
        (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
        c blocks hWithin : Set (AdmissibleKptNode family)) ⊆
      ambientPrefixPool family (finiteNumericH K k N)
        (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
        (ambientStagePool (finiteNumericH K k N)
          ({c} : Set (Fin N)) I) := by
  let hAvoidA : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L :=
    finiteNumericH_avoids_family family K hCarrier k N hAvoidK
  have hSeeds :
      (numericHTopGenerationSeeds family K k N hAvoidA c blocks hWithin :
        Set (AdmissibleKptNode family)) ⊆
      ambientPrefixPool family (finiteNumericH K k N) hAvoidA
        ({c} : Set (Fin N)) :=
    numericHTopGenerationSeeds_subset_rootPool
      family K k N hAvoidA c blocks hWithin
  exact admissibleKpt_stage_closure_subset_pool family
    (finiteNumericH K k N) hAvoidA
    ({c} : Set (Fin N)) I
    (numericHTopGenerationSeeds family K k N hAvoidA c blocks hWithin :
      Set (AdmissibleKptNode family)) hSeeds

/-- For the genuine top-generation seed construction at a full
finite numerical H+ stage, no arbitrary original-prefix pool
hypothesis remains. At every cut with NO actual I2 competing meet:
  1. the chosen source F covers every parameter-closed crossing;
  2. every F input corresponds to a genuine closure node;
  3. its complete old and upper L+ types come from one REAL numeric H
     original with positive enough canonical E free cut.

The only remaining local condition is the displayed real no-I2
test on the entire meet-and-parameter closure, not a shadow. -/
theorem finiteNumericH_topSeeds_full_cut_crossing_and_upper_types
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N : Nat) (c : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ i : Nat, i ∈ blocks →
      hPosition k i k ≤ (finiteNumericH K k N).freeLevel c.val)
    (I : Set Nat) (cut : Nat)
    (hNoMeet : ¬ ∃ a : AdmissibleKptNode family,
      a ∈ SMTree.Envelope.closure (admissibleKptSTree family) I
        (numericHTopGenerationSeeds family K k N
          (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
          c blocks hWithin : Set (AdmissibleKptNode family)) ∧
      ∃ b : AdmissibleKptNode family,
        b ∈ SMTree.Envelope.closure (admissibleKptSTree family) I
          (numericHTopGenerationSeeds family K k N
            (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
            c blocks hWithin : Set (AdmissibleKptNode family)) ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :
    let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
    let hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L :=
      finiteNumericH_avoids_family family K hCarrier k N hAvoidK
    let X : Set (AdmissibleKptNode family) :=
      numericHTopGenerationSeeds family K k N hAvoidA c blocks hWithin
    let Z : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family) I X
    let original : Fin A.size → Fin A.size := fun v => v
    let F : PrescribedBoringData cut db du dd :=
      closureSelectedBoringData family A hAvoidA original Z cut
    CoversClosureCrossing family Z cut F ∧
    IsCrossingGraphOf family Z cut F ∧
    (∀ T, T ∈ F.source →
      ∃ v : Fin A.size, ∃ i q : Nat,
        q ≤ k ∧ v.val = hPosition k i q ∧
        cut+1 ≤ A.freeLevel v.val ∧
        T = A.partialTypeAt cut v.val ∧
        F.target T = A.partialTypeAt (cut+1) v.val) := by
  let hAvoidA : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L :=
    finiteNumericH_avoids_family family K hCarrier k N hAvoidK
  have hSeeds :
      (numericHTopGenerationSeeds family K k N hAvoidA c blocks hWithin :
        Set (AdmissibleKptNode family)) ⊆
      ambientPrefixPool family (finiteNumericH K k N) hAvoidA
        ({c} : Set (Fin N)) :=
    numericHTopGenerationSeeds_subset_rootPool
      family K k N hAvoidA c blocks hWithin
  exact finiteNumericH_full_cut_crossing_and_upper_types
    family K k N hAvoidA ({c} : Set (Fin N))
    (numericHTopGenerationSeeds family K k N hAvoidA c blocks hWithin :
      Set (AdmissibleKptNode family))
    hSeeds I cut hNoMeet

/-- Same physical full-source correspondence at the TRUE
pre-cut closure of an AlgorithmRun on the actual top-generation
seed family. A real scan bound and a genuine no-I2 hypothesis are
retained; this is not a claim that every run passes no-I2. -/
theorem finiteNumericH_topSeeds_run_cut_crossing_and_upper_types
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N : Nat) (c : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ i : Nat, i ∈ blocks →
      hPosition k i k ≤ (finiteNumericH K k N).freeLevel c.val)
    (runHeight : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
      (numericHTopGenerationSeeds family K k N
        (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
        c blocks hWithin)
      runHeight)
    (cut : Nat) (_hScan : cut < runHeight)
    (hNoMeet : ¬ ∃ a : AdmissibleKptNode family,
      a ∈ SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1))
        (numericHTopGenerationSeeds family K k N
          (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
          c blocks hWithin : Set (AdmissibleKptNode family)) ∧
      ∃ b : AdmissibleKptNode family,
        b ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (R.I (cut+1))
          (numericHTopGenerationSeeds family K k N
            (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
            c blocks hWithin : Set (AdmissibleKptNode family)) ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :
    let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
    let hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L :=
      finiteNumericH_avoids_family family K hCarrier k N hAvoidK
    let X : Set (AdmissibleKptNode family) :=
      numericHTopGenerationSeeds family K k N hAvoidA c blocks hWithin
    let Z : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family) (R.I (cut+1)) X
    let original : Fin A.size → Fin A.size := fun v => v
    let F : PrescribedBoringData cut db du dd :=
      closureSelectedBoringData family A hAvoidA original Z cut
    CoversClosureCrossing family Z cut F ∧
    IsCrossingGraphOf family Z cut F ∧
    (∀ T, T ∈ F.source →
      ∃ v : Fin A.size, ∃ i q : Nat,
        q ≤ k ∧ v.val = hPosition k i q ∧
        cut+1 ≤ A.freeLevel v.val ∧
        T = A.partialTypeAt cut v.val ∧
        F.target T = A.partialTypeAt (cut+1) v.val) := by
  exact finiteNumericH_topSeeds_full_cut_crossing_and_upper_types
    family K hCarrier hAvoidK k N c blocks hWithin
    (R.I (cut+1)) cut hNoMeet

#print axioms Kk.finiteNumericH_topSeeds_closure_inside_root_stage_pool
#print axioms Kk.finiteNumericH_topSeeds_full_cut_crossing_and_upper_types
#print axioms Kk.finiteNumericH_topSeeds_run_cut_crossing_and_upper_types

end Kk
