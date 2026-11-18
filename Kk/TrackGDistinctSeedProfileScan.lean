import Kk.TrackGFullEventProfileTransport
import Mathlib.Tactic

/-!
# Track G: complete local full-Kpt event profiles synchronize actual
# Algorithm 5.4 selected-level scans for DISTINCT seed sets.

English proof and 18 hostile checks FIRST:
docs/track_g_distinct_seed_full_profile_scan_english_audit_20261118.md

G347 proves one-cut true I1/I2/I3 interestingness invariance from
complete physical old/upper L+/E crossing RELATION and terminal flag,
even for disjoint physical source sets. Here the actual descending
AlgorithmRun recursion turns that exact per-cut comparison into
equality of selected I-level sets at ALL scan levels.

The two different seed sets share the SAME numeric top/cut coordinates
and the same normalized Kpt tree. Neither chosen total monoid map F,
complete multi-cut labelled inverse-source orbit, nor uniform bounded
diary carrier is identified. Global BRDs remain pending.
-/

namespace Kk

universe u v

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

/-- Generic successor-tree reduction: if two ACTUAL AlgorithmRuns
with potentially DIFFERENT seed sets make the same genuine full-source
interestingness decision at every cut of one common finite scan top,
then the entire selected I-level recursion is identical.

No OneLevelPullback/E1, source inclusion, monoid F equality, or
same-seed run-choice independence is needed. -/
theorem actualAlgorithmRuns_selected_levels_eq_of_stagewise_decisions
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    {S : STree T Label}
    (H : SMTree S) (X Y : Set T) (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun H X top)
    (RY : SMTree.Envelope.AlgorithmRun H Y top)
    (hDecision : ∀ i : Nat, i < top →
      (SMTree.Envelope.IsInterestingAt H
        (SMTree.Envelope.closure S (RX.I (i+1)) X) i ↔
       SMTree.Envelope.IsInterestingAt H
        (SMTree.Envelope.closure S (RY.I (i+1)) Y) i)) :
    ∀ i : Nat, i ≤ top → RX.I i = RY.I i := by
  have main :
      ∀ d : Nat, ∀ i : Nat, top - i = d →
        i ≤ top → RX.I i = RY.I i := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro i hdi hi
        by_cases hieq : i = top
        · subst i
          rw [RX.topI, RY.topI]
        · have hilt : i < top := lt_of_le_of_ne hi hieq
          have hNext : RX.I (i+1) = RY.I (i+1) :=
            ih (top-(i+1)) (by omega) (i+1) rfl (by omega)
          by_cases hinter :
              SMTree.Envelope.IsInterestingAt H
                (SMTree.Envelope.closure S (RX.I (i+1)) X) i
          · have hinterY : SMTree.Envelope.IsInterestingAt H
                (SMTree.Envelope.closure S (RY.I (i+1)) Y) i :=
              (hDecision i hilt).mp hinter
            have hIX := (RX.interesting_step i hilt hinter).1
            have hIY := (RY.interesting_step i hilt hinterY).1
            rw [hIX,hIY,hNext]
          · have hinterY : ¬ SMTree.Envelope.IsInterestingAt H
                (SMTree.Envelope.closure S (RY.I (i+1)) Y) i := by
              intro h
              exact hinter ((hDecision i hilt).mpr h)
            obtain ⟨_,_,_,hIX,_⟩ :=
              RX.noninteresting_step i hilt hinter
            obtain ⟨_,_,_,hIY,_⟩ :=
              RY.noninteresting_step i hilt hinterY
            rw [hIX,hIY,hNext]
  intro i hi
  exact main (top-i) i rfl hi

/-- The first ACTUAL different-source multi-cut comparison theorem:
terminal I1 flags and complete dependent full old/upper Kpt
crossing relations at EACH aligned pre-cut closure of two genuine
runs force equality of ALL selected I sets.

The complete per-cut profiles are hypotheses, not consequences of
the proposed macrodiary; no monoid embedding-type equality. -/
theorem kpt_actual_runs_selected_levels_eq_of_full_cut_profiles
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
          (RY.I (cut+1)) Y) cut))
    (hCrossing : ∀ cut : Nat, cut < top →
      FullPhysicalClosureCrossing family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) X) cut =
      FullPhysicalClosureCrossing family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RY.I (cut+1)) Y) cut) :
    ∀ i : Nat, i ≤ top → RX.I i = RY.I i := by
  apply actualAlgorithmRuns_selected_levels_eq_of_stagewise_decisions
    (normalizedKptSMTree family) X Y top RX RY
  intro cut hCut
  exact kpt_IsInterestingAt_iff_of_terminal_and_full_crossing_eq
    family
    (SMTree.Envelope.closure (admissibleKptSTree family)
      (RX.I (cut+1)) X)
    (SMTree.Envelope.closure (admissibleKptSTree family)
      (RY.I (cut+1)) Y)
    cut (hTerminal cut hCut) (hCrossing cut hCut)

/-- Independently EXHAUSTIVE finite Kpt indices, with different
sizes and WITHOUT any source-name bijection, suffice to compare the
entire selected-level scan of two genuine different-seed runs.

The index masks must enumerate the complete true parameter-closed
pre-cut source at EVERY cut, and both terminal flags and paired full
L+/E relation must match at EACH aligned source coordinate.
Neither equality of monoid factors nor the global diary orbit follows. -/
theorem kpt_actual_runs_selected_levels_eq_of_independent_indexed_profiles
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (RY : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y top)
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
          (admissibleKptSTree family) (RY.I (cut+1)) Y ↔
        ∃ j : Fin Q, nodeY j = z ∧ liveY cut j = true)
    (hTerminal : ∀ cut : Nat, cut < top →
      ((∃ j : Fin P, liveX cut j = true ∧
        LevelTree.lev (nodeX j) = cut) ↔
       (∃ j : Fin Q, liveY cut j = true ∧
        LevelTree.lev (nodeY j) = cut)))
    (hCrossing : ∀ cut : Nat, cut < top →
      IndexedPhysicalCrossing family nodeX liveX cut =
        IndexedPhysicalCrossing family nodeY liveY cut) :
    ∀ i : Nat, i ≤ top → RX.I i = RY.I i := by
  apply actualAlgorithmRuns_selected_levels_eq_of_stagewise_decisions
    (normalizedKptSMTree family) X Y top RX RY
  intro cut hCut
  exact kpt_two_independent_indices_same_full_event_profile_implies_interesting
    family
    (SMTree.Envelope.closure (admissibleKptSTree family)
      (RX.I (cut+1)) X)
    (SMTree.Envelope.closure (admissibleKptSTree family)
      (RY.I (cut+1)) Y)
    nodeX nodeY liveX liveY cut
    (hExactX cut hCut) (hExactY cut hCut)
    (hTerminal cut hCut) (hCrossing cut hCut)

end Kk
