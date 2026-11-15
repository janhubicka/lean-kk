import Kk.PhysicalOffPlanFiniteIndex
import Mathlib.Tactic

/-!
# Track G: eliminate old-boring terminal matching from finite Kpt source tests

This is a genuinely new simplification of the already VERIFIED Track E
PhysicalOffPlanFiniteIndex result, NOT a duplicate of its finite
old-range sandwich. At a cut omitted by the OLD actual AlgorithmRun,
an old full pre-cut terminal is impossible by (I1). Thus any
new-terminal-to-old-terminal coverage certificate at such a cut is
equivalent to the ABSENCE of a new live terminal.

The complete same-node old/upper dependent L+ pair condition is
retained unchanged, including auxiliary E and I2 forks.

English-first proof and hostile audit:
 docs/track_g_old_boring_terminal_elimination_english_audit.md

This does NOT prove either remaining physical condition from a
resolved diary, a global source orbit, or a uniform finite BRD.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The full PRE-CUT parameter closure of a genuine old AlgorithmRun
cannot have an (I1) terminal at a cut which the run skipped.
This statement is NOT merely about the initial seed family. -/
theorem actual_Kpt_old_boring_cut_no_terminal
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (RunOld : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (cut : Nat) (hCut : cut < top)
    (hBoring : cut ∉ RunOld.I cut) :
    ¬ KptI1AtCut family
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (RunOld.I (cut+1)) X) cut := by
  intro hTerm
  have hInteresting :
      SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family)
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RunOld.I (cut+1)) X) cut :=
    Or.inl hTerm
  have hStep := (RunOld.interesting_step cut hCut hInteresting).1
  have hOldCut : cut ∈ RunOld.I cut := by
    rw [hStep]
    exact Set.mem_insert_iff.mpr (Or.inl rfl)
  exact hBoring hOldCut

/-- Simplified two-index off-plan source certificate.
At OLD-BORING off-plan cuts NO NEW live terminal may occur.
The full old/upper L+ same-node crossing pair cover stays unchanged.
This predicate is equivalent to the already merged Track E one under
old full source index exactness and an ACTUAL old AlgorithmRun. -/
def KptTwoIndexOffPlanTerminalFree
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldSelected : Nat → Set Nat)
    (oldTop : Nat) (Allowed : Set Nat)
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool) : Prop :=
  (∀ cut : Nat, cut < oldTop →
    cut ∉ oldSelected cut → cut ∉ Allowed →
    ∀ j : Fin Q, newLive cut j = true →
      LevelTree.lev (newNode j) ≠ cut) ∧
  (∀ cut : Nat, cut < oldTop →
    cut ∉ oldSelected cut → cut ∉ Allowed →
    ∀ j : Fin Q, newLive cut j = true →
      ∀ T : PartialTypeWithE cut db du dd,
        ∀ U : PartialTypeWithE (cut+1) db du dd,
          kptFullOldAtCut (newNode j) cut =
            some (⟨cut,T⟩ : RawPartialTypeNode db du dd) →
          kptFullUpperAtCut (newNode j) cut =
            some (⟨cut+1,U⟩ : RawPartialTypeNode db du dd) →
          ∃ i : Fin P, oldLive cut i = true ∧
            kptFullOldAtCut (oldNode i) cut =
              some (⟨cut,T⟩ : RawPartialTypeNode db du dd) ∧
            kptFullUpperAtCut (oldNode i) cut =
              some (⟨cut+1,U⟩ : RawPartialTypeNode db du dd))

/-- Under exact OLD source indexing, the verified Track E
off-plan existence-matching terminal condition is equivalent to
plain non-existence of NEW cut-level terminals at old-boring cuts.
No new source indexing hypothesis is required for this equivalence;
the complete same-node L+ crossing-pair certificate is unchanged. -/
theorem kpt_twoIndex_offplan_iff_terminalFree_of_old_exact
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (oldTop : Nat)
    (RunOld : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (Allowed : Set Nat)
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool)
    (hExactOld : ∀ cut : Nat, cut < oldTop →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (RunOld.I (cut+1)) X ↔
        ∃ i : Fin P, oldNode i = z ∧ oldLive cut i = true) :
    KptTwoIndexOffPlanNoNovelty family
      RunOld.I oldTop Allowed oldNode newNode oldLive newLive ↔
    KptTwoIndexOffPlanTerminalFree family
      RunOld.I oldTop Allowed oldNode newNode oldLive newLive := by
  classical
  constructor
  · intro hCertificate
    constructor
    · intro cut hCut hBoring hOffPlan j hLive hLev
      obtain ⟨i,hOldLive,hOldLev⟩ :=
        hCertificate.1 cut hCut hBoring hOffPlan
          j hLive hLev
      have hOldTerminal :
          KptI1AtCut family
            (SMTree.Envelope.closure (admissibleKptSTree family)
              (RunOld.I (cut+1)) X) cut :=
        ⟨oldNode i,
          (hExactOld cut hCut (oldNode i)).mpr
            ⟨i,rfl,hOldLive⟩,
          hOldLev⟩
      exact (actual_Kpt_old_boring_cut_no_terminal
        family X oldTop RunOld cut hCut hBoring) hOldTerminal
    · exact hCertificate.2
  · intro hStrict
    constructor
    · intro cut hCut hBoring hOffPlan j hLive hLev
      exact False.elim
        ((hStrict.1 cut hCut hBoring hOffPlan j hLive) hLev)
    · exact hStrict.2


/-- At a cut boring for a GENUINE old Kpt AlgorithmRun, failure of
full actual source no-novelty has EXACTLY two possible causes:
a NEW cut-level terminal, or a NEW complete old/upper dependent L+
crossing PAIR absent from the old source. Both are physical Kpt
closure tests, not selected graph-age shadow conditions.

This does not assert either type of obstruction is absent and does
not bound the number of cuts where one occurs. -/
theorem actual_Kpt_old_boring_novelty_iff_terminal_or_missing_pair
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (RunOld : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (ZNew : Set (AdmissibleKptNode family))
    (cut : Nat) (hCut : cut < top)
    (hBoring : cut ∉ RunOld.I cut) :
    (¬ NewRootNoNoveltyAtCut family
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (RunOld.I (cut+1)) X) ZNew cut) ↔
    (KptI1AtCut family ZNew cut ∨
      ∃ p, p ∈ FullPhysicalClosureCrossing family ZNew cut ∧
        p ∉ FullPhysicalClosureCrossing family
          (SMTree.Envelope.closure (admissibleKptSTree family)
            (RunOld.I (cut+1)) X) cut) := by
  classical
  let ZOld : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (RunOld.I (cut+1)) X
  change (¬ NewRootNoNoveltyAtCut family ZOld ZNew cut) ↔
    (KptI1AtCut family ZNew cut ∨
      ∃ p, p ∈ FullPhysicalClosureCrossing family ZNew cut ∧
        p ∉ FullPhysicalClosureCrossing family ZOld cut)
  have hNoOld : ¬ KptI1AtCut family ZOld cut :=
    actual_Kpt_old_boring_cut_no_terminal
      family X top RunOld cut hCut hBoring
  constructor
  · intro hNot
    by_cases hTerminal : KptI1AtCut family ZNew cut
    · exact Or.inl hTerminal
    · right
      by_contra hNoPair
      have hCross : FullPhysicalClosureCrossing family ZNew cut ⊆
          FullPhysicalClosureCrossing family ZOld cut := by
        intro p hNewPair
        by_contra hOldMissing
        exact hNoPair ⟨p,hNewPair,hOldMissing⟩
      exact False.elim (hNot
        ⟨(by intro hNewTerminal
             exact (hTerminal hNewTerminal).elim),hCross⟩)
  · intro hWitness hQuiet
    rcases hWitness with hNewTerminal | ⟨p,hNewPair,hNotOld⟩
    · exact hNoOld (hQuiet.1 hNewTerminal)
    · exact hNotOld (hQuiet.2 hNewPair)

end Kk
