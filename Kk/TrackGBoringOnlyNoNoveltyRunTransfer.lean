import Kk.TrackGWholeRunProfileTransfer
import Kk.TrackECanonicalBadCutSupport
import Mathlib.Tactic

/-!
# Track G: only OLD-BORING cuts require physical no-novelty for whole-run transport.

English proof and 20 adversarial checks were committed FIRST:
docs/track_g_boring_only_no_novelty_run_transfer_english_audit_20261118.md

For nested actual source seed sets X ⊆ Y in one normalized Kpt tree, a
genuinely interesting cut of the old full source stays interesting
when the source is enlarged. At an OLD-BORING cut, the genuine physical
no-novelty certificate ensures the full terminal and paired dependent
old/upper L+/E Kpt profiles match, so the SAME actual one-level
skip-only monoid map remains valid.

Thus the entire old AlgorithmRun's I and TOTAL F can be used on Y,
without requiring no-novelty at old interesting cuts. Both source
closures are computed using the OLD run's selected I tails. No
new Y-run is assumed; no E1, full source bijection, chronological
cut reindexing, cross-diary source orbit or global BRD is claimed.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

universe u v

/-- The genuine successor-tree I1/I2/I3 test is MONOTONE in its
COMPLETE source set. Its negative skip existence clause is
monotone because the constraints only get stronger.

This does not assert that boringness is preserved by extension. -/
theorem kpt_generic_IsInterestingAt_mono_of_source_subset
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    {S : STree T Label}
    (H : SMTree S) (C D : Set T) (cut : Nat)
    (hCD : C ⊆ D) :
    SMTree.Envelope.IsInterestingAt H C cut →
      SMTree.Envelope.IsInterestingAt H D cut := by
  intro h
  unfold SMTree.Envelope.IsInterestingAt at h ⊢
  rcases h with hI1 | hI2 | hI3
  · obtain ⟨z,hz,hlev⟩ := hI1
    exact Or.inl ⟨z,hCD hz,hlev⟩
  · obtain ⟨a,ha,b,hb,hSame,hLev⟩ := hI2
    exact Or.inr (Or.inl ⟨a,hCD ha,b,hCD hb,hSame,hLev⟩)
  · right
    right
    rintro ⟨M,hSkip,hCross⟩
    apply hI3
    refine ⟨M,hSkip,?_⟩
    intro z hz hzc
    exact hCross (hCD hz) hzc

/-- For actual Kpt source inclusion Z ⊆ W, physical no novelty
is EQUIVALENT to equality of the terminal I1 existence flag and
the COMPLETE SAME-NODE paired old/upper L+/E crossing relation.

The old -> new inclusions follow from literal source inclusion;
the new -> old inclusions are exactly the no-novelty certificate.
No source bijection or no-I2 assumption. -/
theorem kpt_noNovelty_iff_full_profile_eq_of_source_subset
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z W : Set (AdmissibleKptNode family))
    (cut : Nat) (hZW : Z ⊆ W) :
    NewRootNoNoveltyAtCut family Z W cut ↔
      (KptI1AtCut family Z cut ↔ KptI1AtCut family W cut) ∧
      FullPhysicalClosureCrossing family Z cut =
        FullPhysicalClosureCrossing family W cut := by
  constructor
  · intro hQuiet
    constructor
    · constructor
      · rintro ⟨z,hz,hlev⟩
        exact ⟨z,hZW hz,hlev⟩
      · exact hQuiet.1
    · apply Set.Subset.antisymm
      · exact full_physical_crossing_mono_of_source_subset
          family Z W hZW cut
      · exact hQuiet.2
  · rintro ⟨hTerminal,hCrossing⟩
    constructor
    · exact hTerminal.mpr
    · intro p hp
      simpa only [← hCrossing] using hp

/-- Complete physical quietness needs to be checked ONLY where
the original genuine AlgorithmRun on X was BORING. In a literal
nested-seed extension X ⊆ Y, all OLD interesting cuts remain
interesting automatically by source monotonicity; at an
OLD boring cut the no-novelty witness makes the same actual
skip-only MMap satisfy the new complete Kpt crossing constraints.

Consequently, there EXISTS a genuine target AlgorithmRun on Y
with the EXACT old selected I and total monoid-valued F functions.
No target run, inverse source, E1 or source-index bijection is assumed. -/
theorem kpt_transport_actualRun_of_boring_only_noNovelty
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (hNoNovelty : ∀ cut : Nat, cut < top →
      ¬ SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family)
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) X) cut →
      NewRootNoNoveltyAtCut family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) X)
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) Y) cut) :
    ∃ RY : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family) Y top,
      RY.I = RX.I ∧ RY.F = RX.F := by
  have hSourceIncl (cut : Nat) :
      SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) X ⊆
      SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) Y :=
    envelope_closure_mono_seeds_and_levels
      (admissibleKptSTree family)
      (RX.I (cut+1)) (RX.I (cut+1)) X Y
      (by intro i hi; exact hi) hXY
  have hLocal (cut : Nat) (hCut : cut < top) :
      SMTree.Envelope.IsInterestingAt (normalizedKptSMTree family)
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) X) cut ↔
      SMTree.Envelope.IsInterestingAt (normalizedKptSMTree family)
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) Y) cut := by
    constructor
    · intro hInteresting
      exact kpt_generic_IsInterestingAt_mono_of_source_subset
        (normalizedKptSMTree family)
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) X)
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) Y)
        cut (hSourceIncl cut) hInteresting
    · intro hInterestingY
      by_contra hBoringOld
      have hProfiles :=
        (kpt_noNovelty_iff_full_profile_eq_of_source_subset
          family
          (SMTree.Envelope.closure (admissibleKptSTree family)
            (RX.I (cut+1)) X)
          (SMTree.Envelope.closure (admissibleKptSTree family)
            (RX.I (cut+1)) Y)
          cut (hSourceIncl cut)).mp
          (hNoNovelty cut hCut hBoringOld)
      exact hBoringOld
        ((kpt_IsInterestingAt_iff_of_terminal_and_full_crossing_eq
          family
          (SMTree.Envelope.closure (admissibleKptSTree family)
            (RX.I (cut+1)) X)
          (SMTree.Envelope.closure (admissibleKptSTree family)
            (RX.I (cut+1)) Y)
          cut hProfiles.1 hProfiles.2).mpr hInterestingY)
  let RY : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y top :=
    { I := RX.I
      F := RX.F
      topI := RX.topI
      topF := RX.topF
      interesting_step := by
        intro cut hCut hInterestingY
        exact RX.interesting_step cut hCut
          ((hLocal cut hCut).mpr hInterestingY)
      noninteresting_step := by
        intro cut hCut hBoringY
        have hBoringX :
            ¬ SMTree.Envelope.IsInterestingAt
              (normalizedKptSMTree family)
              (SMTree.Envelope.closure (admissibleKptSTree family)
                (RX.I (cut+1)) X) cut := by
          intro hInterestingX
          exact hBoringY ((hLocal cut hCut).mp hInterestingX)
        obtain ⟨D,hSkip,hCrossOld,hIX,hFX⟩ :=
          RX.noninteresting_step cut hCut hBoringX
        have hProfiles :=
          (kpt_noNovelty_iff_full_profile_eq_of_source_subset
            family
            (SMTree.Envelope.closure (admissibleKptSTree family)
              (RX.I (cut+1)) X)
            (SMTree.Envelope.closure (admissibleKptSTree family)
              (RX.I (cut+1)) Y)
            cut (hSourceIncl cut)).mp
            (hNoNovelty cut hCut hBoringX)
        refine ⟨D,hSkip,?_,hIX,hFX⟩
        exact (kpt_actual_skipLaw_iff_of_full_crossing_eq
          family
          (SMTree.Envelope.closure (admissibleKptSTree family)
            (RX.I (cut+1)) X)
          (SMTree.Envelope.closure (admissibleKptSTree family)
            (RX.I (cut+1)) Y)
          cut hProfiles.2 D).mp hCrossOld }
  exact ⟨RY,rfl,rfl⟩

/-- An independently EXHAUSTIVE finite old/new Kpt index can certify
physical no-novelty only at cuts BORING for the old actual run;
there is no need to certify the new source at old interesting cuts.
The finite mask must index the complete source closure on the
ORIGINAL run's I tail, including all parameters and meets.

This constructs a genuine Y-run with exactly the same total I/F.
The index types can have unrelated cardinalities. -/
theorem kpt_transport_actualRun_of_boring_only_indexed_quiet
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool)
    (hExactOld : ∀ cut : Nat, cut < top →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (RX.I (cut+1)) X ↔
        ∃ i : Fin P, oldNode i = z ∧ oldLive cut i = true)
    (hExactNew : ∀ cut : Nat, cut < top →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (RX.I (cut+1)) Y ↔
        ∃ j : Fin Q, newNode j = z ∧ newLive cut j = true)
    (hIndexedQuiet : ∀ cut : Nat, cut < top →
      ¬ SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family)
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) X) cut →
      KptIndexedQuietAtCut family
        oldNode newNode oldLive newLive cut) :
    ∃ RY : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family) Y top,
      RY.I = RX.I ∧ RY.F = RX.F := by
  apply kpt_transport_actualRun_of_boring_only_noNovelty
    family X Y hXY top RX
  intro cut hCut hBoring
  exact (kptIndexedQuietAtCut_iff_physical
    family
    (SMTree.Envelope.closure (admissibleKptSTree family)
      (RX.I (cut+1)) X)
    (SMTree.Envelope.closure (admissibleKptSTree family)
      (RX.I (cut+1)) Y)
    oldNode newNode oldLive newLive cut
    (hExactOld cut hCut) (hExactNew cut hCut)).mp
    (hIndexedQuiet cut hCut hBoring)

end Kk
