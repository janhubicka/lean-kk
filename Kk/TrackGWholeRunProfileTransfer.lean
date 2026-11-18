import Kk.TrackGFullEventProfileTransport
import Mathlib.Tactic

/-!
# Track G: a whole ACTUAL Kpt AlgorithmRun can be transported to
# a DIFFERENT seed set using the exact complete terminal+L+/E crossing
# profiles along its selected tails.

English proof and 18 hostile checks committed before Lean:
docs/track_g_whole_run_transport_full_profile_english_audit_20261118.md

More than agreement of selected level decisions: the same I and
the same TOTAL MMap-valued F are a genuine AlgorithmRun on the
other source. At a boring stage the SAME actual skip-only D from
the first source satisfies the second source's full ancestor
constraints by the verified G347 physical crossing-pair transport.

No source-node overlap, finite index bijection, E1, no-I2 or source
inclusion is assumed. Profiles are tested along the GIVEN run's I,
not along an unknown other run. This is existence of a synchronized
run, NOT equality of arbitrary runs' F maps, a common labelled
inverse source orbit or a global Kk-free BRD characterization.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

/-- Transport ONE entire genuine AlgorithmRun from X to Y,
keeping its selected-level function I and its total monoid map
function F LITERALLY unchanged, assuming that all ACTUAL full
parameter-closed pre-cut Kpt sources along the X-run I sequence
have the same I1 terminal flag and complete old/upper dependent
L+/E crossing relation when evaluated on X versus Y.

No preexisting AlgorithmRun on Y is an input. -/
theorem kpt_transport_whole_actualRun_of_full_profile_eq
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (hTerminal : ∀ cut : Nat, cut < top →
      (KptI1AtCut family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) X) cut ↔
       KptI1AtCut family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) Y) cut))
    (hCrossing : ∀ cut : Nat, cut < top →
      FullPhysicalClosureCrossing family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) X) cut =
      FullPhysicalClosureCrossing family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) Y) cut) :
    ∃ RY : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family) Y top,
      RY.I = RX.I ∧ RY.F = RX.F := by
  have hLocal (cut : Nat) (hCut : cut < top) :
      SMTree.Envelope.IsInterestingAt (normalizedKptSMTree family)
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) X) cut ↔
      SMTree.Envelope.IsInterestingAt (normalizedKptSMTree family)
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) Y) cut :=
    kpt_IsInterestingAt_iff_of_terminal_and_full_crossing_eq
      family
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (RX.I (cut+1)) X)
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (RX.I (cut+1)) Y)
      cut (hTerminal cut hCut) (hCrossing cut hCut)
  let RY : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y top :=
    { I := RX.I
      F := RX.F
      topI := RX.topI
      topF := RX.topF
      interesting_step := by
        intro cut hCut hInterestingY
        have hInterestingX :
            SMTree.Envelope.IsInterestingAt
              (normalizedKptSMTree family)
              (SMTree.Envelope.closure (admissibleKptSTree family)
                (RX.I (cut+1)) X) cut :=
          (hLocal cut hCut).mpr hInterestingY
        exact RX.interesting_step cut hCut hInterestingX
      noninteresting_step := by
        intro cut hCut hBoringY
        have hBoringX :
            ¬ SMTree.Envelope.IsInterestingAt
              (normalizedKptSMTree family)
              (SMTree.Envelope.closure (admissibleKptSTree family)
                (RX.I (cut+1)) X) cut := by
          intro hInterestingX
          exact hBoringY ((hLocal cut hCut).mp hInterestingX)
        obtain ⟨D,hSkip,hCrossX,hIX,hFX⟩ :=
          RX.noninteresting_step cut hCut hBoringX
        refine ⟨D,hSkip,?_,hIX,hFX⟩
        exact (kpt_actual_skipLaw_iff_of_full_crossing_eq
          family
          (SMTree.Envelope.closure (admissibleKptSTree family)
            (RX.I (cut+1)) X)
          (SMTree.Envelope.closure (admissibleKptSTree family)
            (RX.I (cut+1)) Y)
          cut (hCrossing cut hCut) D).mp hCrossX }
  exact ⟨RY, rfl, rfl⟩

/-- Any separately chosen actual Y-run has the same selected I sets,
because an EXACT synchronized Y-run exists (above) and the genuine
successor-tree same-seed AlgorithmRun.I_eq theorem makes I independent
of skip-map choices. No equality of arbitrary Y-run total F maps. -/
theorem kpt_any_target_actualRun_selected_levels_eq_of_source_profile
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (RY : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y top)
    (hTerminal : ∀ cut : Nat, cut < top →
      (KptI1AtCut family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) X) cut ↔
       KptI1AtCut family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) Y) cut))
    (hCrossing : ∀ cut : Nat, cut < top →
      FullPhysicalClosureCrossing family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) X) cut =
      FullPhysicalClosureCrossing family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) Y) cut) :
    ∀ i : Nat, i ≤ top → RX.I i = RY.I i := by
  obtain ⟨Rsync,hSameI,_hSameF⟩ :=
    kpt_transport_whole_actualRun_of_full_profile_eq
      family X Y top RX hTerminal hCrossing
  intro i hi
  have hEq := Rsync.I_eq RY i hi
  rw [hSameI] at hEq
  exact hEq

/-- Two independently exhaustive finite Kpt source indices with
possibly DIFFERENT sizes supply a concrete sufficient criterion
for transporting one actual full AlgorithmRun I AND F to another
seed set. At every cut the masks must index the TRUE closures
formed using the ORIGINAL RX.I tail. The full dependent L+/E
paired relation and terminal flag must match.

No index bijection, shared physical node, new-height cut map,
or global source orbit is assumed or constructed. -/
theorem kpt_transport_whole_actualRun_of_indexed_full_profiles
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (nodeX : Fin P → AdmissibleKptNode family)
    (nodeY : Fin Q → AdmissibleKptNode family)
    (liveX : Nat → Fin P → Bool)
    (liveY : Nat → Fin Q → Bool)
    (hExactX : ∀ cut : Nat, cut < top →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (RX.I (cut+1)) X ↔
        ∃ j : Fin P, nodeX j = z ∧ liveX cut j = true)
    (hExactY : ∀ cut : Nat, cut < top →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (RX.I (cut+1)) Y ↔
        ∃ j : Fin Q, nodeY j = z ∧ liveY cut j = true)
    (hTerminal : ∀ cut : Nat, cut < top →
      ((∃ j : Fin P, liveX cut j = true ∧
        LevelTree.lev (nodeX j) = cut) ↔
       (∃ j : Fin Q, liveY cut j = true ∧
        LevelTree.lev (nodeY j) = cut)))
    (hCrossing : ∀ cut : Nat, cut < top →
      IndexedPhysicalCrossing family nodeX liveX cut =
        IndexedPhysicalCrossing family nodeY liveY cut) :
    ∃ RY : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family) Y top,
      RY.I = RX.I ∧ RY.F = RX.F := by
  apply kpt_transport_whole_actualRun_of_full_profile_eq
    family X Y top RX
  · intro cut hCut
    have hI1X :=
      (physical_I1_I2_iff_indexed_active_nodes
        family nodeX liveX
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) X)
        cut (hExactX cut hCut)).1
    have hI1Y :=
      (physical_I1_I2_iff_indexed_active_nodes
        family nodeY liveY
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) Y)
        cut (hExactY cut hCut)).1
    exact hI1X.trans ((hTerminal cut hCut).trans hI1Y.symm)
  · intro cut hCut
    calc
      FullPhysicalClosureCrossing family
          (SMTree.Envelope.closure (admissibleKptSTree family)
            (RX.I (cut+1)) X) cut =
        IndexedPhysicalCrossing family nodeX liveX cut :=
        (indexed_physical_crossing_eq_full_closure_relation
          family nodeX liveX
          (SMTree.Envelope.closure (admissibleKptSTree family)
            (RX.I (cut+1)) X)
          cut (hExactX cut hCut)).symm
      _ = IndexedPhysicalCrossing family nodeY liveY cut :=
        hCrossing cut hCut
      _ = FullPhysicalClosureCrossing family
          (SMTree.Envelope.closure (admissibleKptSTree family)
            (RX.I (cut+1)) Y) cut :=
        indexed_physical_crossing_eq_full_closure_relation
          family nodeY liveY
          (SMTree.Envelope.closure (admissibleKptSTree family)
            (RX.I (cut+1)) Y)
          cut (hExactY cut hCut)

end Kk
