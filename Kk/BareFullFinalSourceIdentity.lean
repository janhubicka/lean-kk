import Kk.BareFullRunSelectedEquivalence
import Mathlib.Tactic

/-!
# Track C: actual bare/full new-root full sources, not only selected levels

English-first proof and adversarial audit:
  docs/track_c_bare_full_final_source_english_audit.md

The genuine bare and inherited-full new-root AlgorithmRuns choose the same
selected levels under the precise verified-source hypotheses in the parent
Track C theorem. At their FINAL selected-level set, the old selected
levels are all retained, and ordinary closure absorption is therefore
EXACT on the whole Kpt node set, not just at/above a cut.

At each earlier cut only the cut-visible source need coincide; it
suffices to transport the complete local I1/I2/I3 and physical
old/upper L+/E crossing, even with genuinely branching I2 data.

No claim about different base models, inverse monoid orbits or BRDs.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

universe u v

/-- The TWO actual new-root presentations have IDENTICAL FINAL complete
meet/parameter closure nodes, not merely identical selected I sets.

The old source has a REAL top-level seed and both new AlgorithmRuns
have the SAME newer top at least oldTop. The old selected levels are
all retained in the bare run by the verified cross-height theorem;
hence the ordinary full closure-absorption identity applies at the
final selected level set, even when old I0 contains zero.

This is equality of Kpt nodes in ONE successor tree, not equality of
monoid F maps or of sources from different physical occurrences. -/
theorem envelope_bare_full_runs_final_closure_eq
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    {S : STree T Label}
    (H : SMTree S)
    (X O : Set T)
    (oldTop newTop : Nat)
    (hTopLe : oldTop ≤ newTop)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = oldTop)
    (Rold : SMTree.Envelope.AlgorithmRun H X oldTop)
    (Rbare : SMTree.Envelope.AlgorithmRun H (X ∪ O) newTop)
    (Rfull : SMTree.Envelope.AlgorithmRun H
      (SMTree.Envelope.closure S (Rold.I 0) X ∪ O) newTop) :
    SMTree.Envelope.closure S (Rbare.I 0) (X ∪ O) =
      SMTree.Envelope.closure S (Rfull.I 0)
        (SMTree.Envelope.closure S (Rold.I 0) X ∪ O) := by
  have hSeeds : X ⊆ X ∪ O := by
    intro z hz
    exact Or.inl hz
  have hRetained : Rold.I 0 ⊆ Rbare.I 0 :=
    envelope_algorithmRun_selected_levels_mono_seed_height
      H X (X ∪ O) hSeeds oldTop newTop hTopLe hTopSeed
      Rold Rbare 0 (Nat.zero_le oldTop)
  have hSame :
      Rbare.I 0 = Rfull.I 0 :=
    envelope_bare_full_new_runs_same_selected_levels
      H X O oldTop newTop hTopLe hTopSeed
      Rold Rbare Rfull 0 (Nat.zero_le newTop)
  have hAbsorb :
      SMTree.Envelope.closure S (Rbare.I 0)
          (SMTree.Envelope.closure S (Rold.I 0) X ∪ O) =
        SMTree.Envelope.closure S (Rbare.I 0) (X ∪ O) :=
    envelope_closure_absorbs_old_closure_of_levels
      S (Rold.I 0) (Rbare.I 0) X O hRetained
  rw [← hSame]
  exact hAbsorb.symm

/-- At EVERY level cut below the common new top, the true bare and
inherited-full runs' actual full closures have the same nodes AT OR
ABOVE the cut.

Their closures can still differ below the cut; lower inherited
parameters are not thrown away. The theorem does NOT require that
ALL old selected levels lie above the tested cut. -/
theorem envelope_bare_full_runs_cut_visible_eq
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    {S : STree T Label}
    (H : SMTree S)
    (X O : Set T)
    (oldTop newTop : Nat)
    (hTopLe : oldTop ≤ newTop)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = oldTop)
    (Rold : SMTree.Envelope.AlgorithmRun H X oldTop)
    (Rbare : SMTree.Envelope.AlgorithmRun H (X ∪ O) newTop)
    (Rfull : SMTree.Envelope.AlgorithmRun H
      (SMTree.Envelope.closure S (Rold.I 0) X ∪ O) newTop)
    (cut : Nat) (hCut : cut < newTop) :
    ∀ z : T, cut ≤ LevelTree.lev z →
      (z ∈ SMTree.Envelope.closure S
          (Rbare.I (cut+1)) (X ∪ O) ↔
       z ∈ SMTree.Envelope.closure S
          (Rfull.I (cut+1))
            (SMTree.Envelope.closure S (Rold.I 0) X ∪ O)) := by
  have hSeeds : X ⊆ X ∪ O := by
    intro z hz
    exact Or.inl hz
  have hTail :
      ∀ q : Nat, q ∈ Rold.I 0 → cut < q →
        q ∈ Rbare.I (cut+1) := by
    intro q hOld hAbove
    by_cases hBefore : cut < oldTop
    · exact envelope_algorithmRun_retains_old_selected_tail
        H X (X ∪ O) hSeeds
        oldTop newTop hTopLe hTopSeed
        Rold Rbare cut hBefore q hOld hAbove
    · have hBound :=
        Rold.I_mem_bounds 0 (Nat.zero_le oldTop) q hOld
      omega
  have hSame :
      Rbare.I (cut+1) = Rfull.I (cut+1) :=
    envelope_bare_full_new_runs_same_selected_levels
      H X O oldTop newTop hTopLe hTopSeed
      Rold Rbare Rfull (cut+1) (by omega)
  intro z hz
  have hAbsorb :=
    envelope_closure_high_absorbs_old_closure
      S (Rold.I 0) (Rbare.I (cut+1)) X O cut
      hTail z hz
  rw [← hSame]
  exact hAbsorb.symm

/-- Numerically genuine H+ source of new roots; exact equality of
the FINAL complete Kpt meet-and-dependent-parameter closure for
the bare and inherited-full new-root AlgorithmRuns.

Both sets of original new nodes are the ACTUAL admissible Kpt
originals of the same physically forbidden-free finite H+ model.
No arbitrary assigned E source or full ancestor-prefix initial seed
set appears. -/
theorem finiteNumericH_bare_full_runs_final_source_eq
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (X : Set (AdmissibleKptNode family))
    (W : Set (Fin M))
    (oldTop newTop : Nat)
    (hTopLe : oldTop ≤ newTop)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = oldTop)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (Rbare : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
      (X ∪ ((fun w : Fin M =>
        (finiteNumericH L k M).kptOriginal family hAvoid w) '' W))
      newTop)
    (Rfull : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (Rold.I 0) X ∪
        ((fun w : Fin M =>
          (finiteNumericH L k M).kptOriginal family hAvoid w) '' W))
      newTop) :
    SMTree.Envelope.closure (admissibleKptSTree family)
      (Rbare.I 0)
      (X ∪ ((fun w : Fin M =>
        (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)) =
    SMTree.Envelope.closure (admissibleKptSTree family)
      (Rfull.I 0)
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (Rold.I 0) X ∪
        ((fun w : Fin M =>
          (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)) := by
  exact envelope_bare_full_runs_final_closure_eq
    (normalizedKptSMTree family)
    X ((fun w : Fin M =>
      (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)
    oldTop newTop hTopLe hTopSeed Rold Rbare Rfull

/-- Full physical data at EVERY actual new-root tested cut coincide
for genuine bare and inherited-full source runs in the SAME finite
H+ model: I1, I2, complete nonfunctional old/upper L+/E crossing,
and the actual I3 skip-map interestingness test.

This is NOT a common-orbit or source-coordinate theorem across
distinct Henson occurrences. -/
theorem finiteNumericH_bare_full_runs_all_cut_events_eq
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (X : Set (AdmissibleKptNode family))
    (W : Set (Fin M))
    (oldTop newTop : Nat)
    (hTopLe : oldTop ≤ newTop)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = oldTop)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (Rbare : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
      (X ∪ ((fun w : Fin M =>
        (finiteNumericH L k M).kptOriginal family hAvoid w) '' W))
      newTop)
    (Rfull : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (Rold.I 0) X ∪
        ((fun w : Fin M =>
          (finiteNumericH L k M).kptOriginal family hAvoid w) '' W))
      newTop)
    (cut : Nat) (hCut : cut < newTop) :
    let O : Set (AdmissibleKptNode family) :=
      ((fun w : Fin M =>
        (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)
    let Zbare : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (Rbare.I (cut+1)) (X ∪ O)
    let Zfull : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (Rfull.I (cut+1))
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (Rold.I 0) X ∪ O)
    (∀ z : AdmissibleKptNode family, cut ≤ LevelTree.lev z →
      (z ∈ Zbare ↔ z ∈ Zfull)) ∧
    (KptI1AtCut family Zbare cut ↔ KptI1AtCut family Zfull cut) ∧
    (KptI2MeetAtCut family Zbare cut ↔
      KptI2MeetAtCut family Zfull cut) ∧
    (FullPhysicalClosureCrossing family Zbare cut =
      FullPhysicalClosureCrossing family Zfull cut) ∧
    (SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family) Zbare cut ↔
     SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family) Zfull cut) := by
  let O : Set (AdmissibleKptNode family) :=
    ((fun w : Fin M =>
      (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)
  let Zbare : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (Rbare.I (cut+1)) (X ∪ O)
  let Zfull : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (Rfull.I (cut+1))
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (Rold.I 0) X ∪ O)
  have hVisible :
      ∀ z : AdmissibleKptNode family,
        cut ≤ LevelTree.lev z → (z ∈ Zbare ↔ z ∈ Zfull) :=
    envelope_bare_full_runs_cut_visible_eq
      (normalizedKptSMTree family)
      X O oldTop newTop hTopLe hTopSeed
      Rold Rbare Rfull cut hCut
  have hStruct :=
    kpt_cut_visible_same_structural_and_full_crossing
      family Zbare Zfull cut hVisible
  have hInteresting :=
    envelope_IsInterestingAt_iff_of_cut_visible
      (normalizedKptSMTree family) Zbare Zfull cut hVisible
  dsimp only
  exact ⟨hVisible, hStruct.1, hStruct.2.1,
    hStruct.2.2, hInteresting⟩

end Kk
