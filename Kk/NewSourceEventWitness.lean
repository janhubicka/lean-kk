import Kk.ActualRunSeedMonotonicity
import Kk.PhysicalI3CrossingInvariance
import Mathlib.Tactic

/-!
# Track E: a NEW selected cut has a NEW complete Kpt source witness

This is a genuine physical diagnostic for growing seed sets, not an
assumed synchronized diary comparison.

Let X ⊆ Y and take two actual Kpt AlgorithmRuns on X,Y with the
same source-level top. Our kernel-checked generic monotonicity proves
the old selected levels and actual pre-cut closure are included in
the new ones.

If the larger run chooses cut i but the smaller run skips i,
the actual generic AlgorithmRun branch laws imply:
  * i is boring for the smaller genuine full source;
  * i is interesting for the larger genuine full source.

The monoid-level full crossing invariance then proves that the
source enlargement MUST introduce either
  (I) a new genuine terminal Kpt node at i, absent from the old
      complete closure; or
  (II) a new genuinely physical COMPLETE old/upper L+ crossing
      pair (including auxiliary E and all negative graph atoms).

This is a *necessary witness*, not yet a proof that the proposed
resolved KK macrodiary prevents such extra witnesses.

English proof/adversarial audit committed before Lean:
  docs/track_e_monotone_seed_growth_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The canonical physical full old/upper L+ crossing relation
is monotone under literal inclusion of genuine Kpt source nodes.
It works at true competing I2 cuts, since the relation can have
multiple upper types over the same old type. -/
theorem full_physical_crossing_mono_of_source_subset
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z W : Set (AdmissibleKptNode family))
    (hZW : Z ⊆ W) (cut : Nat) :
    FullPhysicalClosureCrossing family Z cut ⊆
      FullPhysicalClosureCrossing family W cut := by
  intro p hp
  obtain ⟨z,hZ,hCut,hOld,hUpper⟩ := hp
  exact ⟨z,hZW hZ,hCut,hOld,hUpper⟩

/-- The exact two-way NEW-CUT WITNESS theorem in two actual finite
or infinite Kpt AlgorithmRuns. No chosen mono-map equality, no
relative graph age and no extra B3 profile matching is assumed.

At any cut selected by the larger run but NOT by the smaller
run (at its actual AlgorithmRun step), at least ONE new physical
source event is forced:
  * terminal I1 at a genuinely newly added closure node, OR
  * an old/upper COMPLETE dependent L+ crossing pair not present
    in the smaller pre-cut closure.

The two pre-cut closure sources come from their ACTUAL different
selected-level sets, not from an artificially fixed I.
All shape maps in the I3 proof belong to the genuine Kpt monoid. -/
theorem new_selected_Kpt_cut_has_new_terminal_or_full_crossing
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y) (top cut : Nat)
    (RunX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (RunY : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y top)
    (hCut : cut < top)
    (hSelectedNew : cut ∈ RunY.I cut)
    (hNotSelectedOld : cut ∉ RunX.I cut) :
    let ZX : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (RunX.I (cut+1)) X
    let ZY : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (RunY.I (cut+1)) Y
    (∃ z : AdmissibleKptNode family,
      z ∈ ZY ∧ z ∉ ZX ∧ LevelTree.lev z = cut) ∨
    (∃ p : PartialTypeWithE cut db du dd ×
        PartialTypeWithE (cut+1) db du dd,
      p ∈ FullPhysicalClosureCrossing family ZY cut ∧
      p ∉ FullPhysicalClosureCrossing family ZX cut) := by
  classical
  let H := normalizedKptSMTree family
  let ZX : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (RunX.I (cut+1)) X
  let ZY : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (RunY.I (cut+1)) Y
  have hLevels := actual_AlgorithmRun_selected_levels_mono_of_seed_growth
    H X Y hXY top RunX RunY
  have hNext : RunX.I (cut+1) ⊆ RunY.I (cut+1) :=
    hLevels (cut+1) (by omega)
  have hSource : ZX ⊆ ZY :=
    envelope_closure_mono_both
      (RunX.I (cut+1)) (RunY.I (cut+1)) X Y hNext hXY
  have hFullSub :
      FullPhysicalClosureCrossing family ZX cut ⊆
      FullPhysicalClosureCrossing family ZY cut :=
    full_physical_crossing_mono_of_source_subset
      family ZX ZY hSource cut
  have hOldBoring : ¬ SMTree.Envelope.IsInterestingAt H ZX cut := by
    intro hOldInteresting
    have hStep := (RunX.interesting_step cut hCut hOldInteresting).1
    have hSelected : cut ∈ RunX.I cut := by
      rw [hStep]
      exact Set.mem_insert_iff.mpr (Or.inl rfl)
    exact hNotSelectedOld hSelected
  have hNewInteresting : SMTree.Envelope.IsInterestingAt H ZY cut := by
    by_contra hBoring
    obtain ⟨D,hSkip,hCross,hNoInsert,hMap⟩ :=
      RunY.noninteresting_step cut hCut hBoring
    have hAtNext : cut ∈ RunY.I (cut+1) := by
      rw [←hNoInsert]
      exact hSelectedNew
    have hBounds := RunY.I_mem_bounds
      (cut+1) (by omega) cut hAtNext
    omega
  have hNoI1Old : ¬ KptI1AtCut family ZX cut := by
    intro hNode
    exact hOldBoring (Or.inl hNode)
  by_cases hNewI1 : KptI1AtCut family ZY cut
  · obtain ⟨z,hZ,hLevel⟩ := hNewI1
    left
    refine ⟨z,hZ,?_,hLevel⟩
    intro hOldZ
    exact hNoI1Old ⟨z,hOldZ,hLevel⟩
  · right
    by_contra hNoNewPair
    have hReverse :
        FullPhysicalClosureCrossing family ZY cut ⊆
        FullPhysicalClosureCrossing family ZX cut := by
      intro p hp
      by_contra hNotOld
      exact hNoNewPair ⟨p,hp,hNotOld⟩
    have hFullEq :
        FullPhysicalClosureCrossing family ZX cut =
        FullPhysicalClosureCrossing family ZY cut :=
      Set.Subset.antisymm hFullSub hReverse
    have hTerminalEq : KptI1AtCut family ZX cut ↔
        KptI1AtCut family ZY cut := by
      constructor
      · intro h
        exact False.elim (hNoI1Old h)
      · intro h
        exact False.elim (hNewI1 h)
    have hInterestingEq :=
      kpt_actual_interesting_iff_of_terminal_and_crossing_eq
        family ZX ZY cut hTerminalEq hFullEq
    exact hOldBoring (hInterestingEq.mpr hNewInteresting)

/-- Genuine NEW ROOTS in the actual Kpt source are constructed as
Y=closure I X ∪ W: inherited closure nodes plus new original-root
prefixes. X⊆Y is PROVED, not assumed.

When the new actual run selects an extra cut, that cut has one of
the two precise NEW PHYSICAL L+ source witnesses above, computed
from the actual stage pre-cut closures of the two runs.

This applies to the SOURCE shape of Track C's new-root construction
once its finite numerical H+ realisation, avoidance and same-top
AlgorithmRun witnesses are discharged. -/
theorem actual_Kpt_new_root_extra_cut_has_physical_witness
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X W : Set (AdmissibleKptNode family))
    (I : Set Nat) (top cut : Nat)
    (RunOld : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (RunNew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
      (SMTree.Envelope.closure (admissibleKptSTree family) I X ∪ W) top)
    (hCut : cut < top)
    (hNew : cut ∈ RunNew.I cut)
    (hOld : cut ∉ RunOld.I cut) :
    let ZX : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (RunOld.I (cut+1)) X
    let ZY : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (RunNew.I (cut+1))
        (SMTree.Envelope.closure (admissibleKptSTree family) I X ∪ W)
    (∃ z : AdmissibleKptNode family,
      z ∈ ZY ∧ z ∉ ZX ∧ LevelTree.lev z = cut) ∨
    (∃ p : PartialTypeWithE cut db du dd ×
        PartialTypeWithE (cut+1) db du dd,
      p ∈ FullPhysicalClosureCrossing family ZY cut ∧
      p ∉ FullPhysicalClosureCrossing family ZX cut) := by
  have hSeeds : X ⊆
      (SMTree.Envelope.closure (admissibleKptSTree family) I X ∪ W) := by
    intro z hz
    exact Or.inl (SMTree.Envelope.subset_closure
      (admissibleKptSTree family) I X hz)
  exact new_selected_Kpt_cut_has_new_terminal_or_full_crossing
    family X _ hSeeds top cut RunOld RunNew hCut hNew hOld

end Kk
