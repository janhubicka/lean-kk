import Kk.TrackDZeroFullColumn
import Kk.TrackDPreCutStageSource
import Kk.TrackECandidateSourceResidualFrontier
import Mathlib.Tactic

/-!
# Track E E72: full dependent old/upper Kpt crossings from zero-column old socles

English-first mathematical proof and 23 adversarial checks:
docs/track_e_zero_column_socle_full_crossing_english_audit_20261119.md

For ONE genuine old normalized-Kpt AlgorithmRun R on X, the candidate
new pre-cut closure is computed on Y using the SAME OLD R.I(c+1).
When every eligible actual ORIGINAL in the full stage pool has zero
ordinary L cut bit and every new-live crossing has an old-live source
with the SAME COMPLETE OLD Kpt ancestor, the checked Track D
six-field next-column uniqueness forces equality of the COMPLETE
UPPER dependent L+/E ancestors. Hence every new physical full
crossing pair already appears in the old closure, even at I2 forks.

The entire result is source-exact and local at one cut. It does not
assert the required old-socle coverage for the resolved Q construction,
or eliminate I1 terminals, or prove a diary-uniform upper BRD bound.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- For a TRUE numerical-H+ source cut in one old AlgorithmRun,
full stage-original zero L columns and an old-live SAME OLD Kpt
ancestor force the SAME upper Kpt ancestor. This includes dependent
auxiliary E and negative ordinary L (not just graph-age shadows).

The two actual original representatives need not themselves lie in
the old/new closures: only z and its old witness w do. -/
theorem finiteNumericH_candidate_zero_column_old_socle_upper_covered
    (family : List (NormalizedForbidden 1 0 1))
    (K : AgeTestModel 1 0 1) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hSym : ∀ i j : Nat,
      (finiteNumericH K k N).L.binary i j (0 : Fin 1) =
        (finiteNumericH K k N).L.binary j i (0 : Fin 1))
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid (U : Set (Fin N)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (cut : Nat)
    (hZeroStage : ∀ v : Fin N,
      v ∈ hStageOriginals K k N U (R.I (cut+1)) →
      cut+1 ≤ (finiteNumericH K k N).freeLevel v.val →
      (finiteNumericH K k N).L.binary
        cut v.val (0 : Fin 1) = false)
    (z w : AdmissibleKptNode family)
    (hZ : z ∈ SMTree.Envelope.closure
      (admissibleKptSTree family) (R.I (cut+1)) Y)
    (hW : w ∈ SMTree.Envelope.closure
      (admissibleKptSTree family) (R.I (cut+1)) X)
    (hZCross : cut < LevelTree.lev z)
    (hWCross : cut < LevelTree.lev w)
    (hOldAncestor :
      LevelTree.ancestor z cut (Nat.le_of_lt hZCross) =
        LevelTree.ancestor w cut (Nat.le_of_lt hWCross)) :
    kpt_actual_run_node_upper_covered
      family X top R z cut := by
  let A : EnumeratedPartialStructure 1 0 1 :=
    finiteNumericH K k N
  have hX : X ⊆ ambientPrefixPool family A hAvoid
      (U : Set (Fin N)) := by
    intro x hx
    exact hY (hXY hx)
  obtain ⟨v,hStageV,hBelowV⟩ :=
    finiteNumericH_stage_closure_represented_by_stage_originals
      family K k N hAvoid U Y hY (R.I (cut+1)) z hZ
  obtain ⟨u,hStageU,hBelowU⟩ :=
    finiteNumericH_stage_closure_represented_by_stage_originals
      family K k N hAvoid U X hX (R.I (cut+1)) w hW
  have hLevV : LevelTree.lev z ≤ A.freeLevel v.val := by
    have h := LevelTree.level_le_of_le hBelowV
    change LevelTree.lev z ≤ A.freeLevel v.val at h
    exact h
  have hLevU : LevelTree.lev w ≤ A.freeLevel u.val := by
    have h := LevelTree.level_le_of_le hBelowU
    change LevelTree.lev w ≤ A.freeLevel u.val at h
    exact h
  have hFreeV : cut+1 ≤ A.freeLevel v.val := by omega
  have hFreeU : cut+1 ≤ A.freeLevel u.val := by omega
  have hZeroV : A.L.binary cut v.val (0 : Fin 1) = false :=
    hZeroStage v hStageV hFreeV
  have hZeroU : A.L.binary cut u.val (0 : Fin 1) = false :=
    hZeroStage u hStageU hFreeU
  have hRawZ :
      (LevelTree.ancestor z cut (Nat.le_of_lt hZCross)).val =
        (⟨cut,A.partialTypeAt cut v.val⟩ :
          RawPartialTypeNode 1 0 1) :=
    kptBelowOriginal_ancestor_raw family A hAvoid v z
      hBelowV cut (Nat.le_of_lt hZCross)
  have hRawW :
      (LevelTree.ancestor w cut (Nat.le_of_lt hWCross)).val =
        (⟨cut,A.partialTypeAt cut u.val⟩ :
          RawPartialTypeNode 1 0 1) :=
    kptBelowOriginal_ancestor_raw family A hAvoid u w
      hBelowU cut (Nat.le_of_lt hWCross)
  have hOldType : A.partialTypeAt cut v.val =
      A.partialTypeAt cut u.val := by
    have hRaw :
        (⟨cut,A.partialTypeAt cut v.val⟩ :
          RawPartialTypeNode 1 0 1) =
        (⟨cut,A.partialTypeAt cut u.val⟩ :
          RawPartialTypeNode 1 0 1) := by
      calc
        (⟨cut,A.partialTypeAt cut v.val⟩ :
            RawPartialTypeNode 1 0 1) =
            (LevelTree.ancestor z cut
              (Nat.le_of_lt hZCross)).val := hRawZ.symm
        _ = (LevelTree.ancestor w cut
              (Nat.le_of_lt hWCross)).val :=
          congrArg Subtype.val hOldAncestor
        _ = (⟨cut,A.partialTypeAt cut u.val⟩ :
            RawPartialTypeNode 1 0 1) := hRawW
    exact eq_of_heq (Sigma.mk.inj_iff.mp hRaw).2
  have hNextType : A.partialTypeAt (cut+1) v.val =
      A.partialTypeAt (cut+1) u.val :=
    full_zero_ordinary_cut_column_determines_next_type
      A hSym cut v u hFreeV hFreeU hZeroV hZeroU hOldType
  have hRawUpperZ :
      (LevelTree.ancestor z (cut+1)
        (Nat.succ_le_iff.mpr hZCross)).val =
        (⟨cut+1,A.partialTypeAt (cut+1) v.val⟩ :
          RawPartialTypeNode 1 0 1) :=
    kptBelowOriginal_ancestor_raw family A hAvoid v z
      hBelowV (cut+1) (Nat.succ_le_iff.mpr hZCross)
  have hRawUpperW :
      (LevelTree.ancestor w (cut+1)
        (Nat.succ_le_iff.mpr hWCross)).val =
        (⟨cut+1,A.partialTypeAt (cut+1) u.val⟩ :
          RawPartialTypeNode 1 0 1) :=
    kptBelowOriginal_ancestor_raw family A hAvoid u w
      hBelowU (cut+1) (Nat.succ_le_iff.mpr hWCross)
  have hUpperAncestor :
      LevelTree.ancestor z (cut+1)
        (Nat.succ_le_iff.mpr hZCross) =
      LevelTree.ancestor w (cut+1)
        (Nat.succ_le_iff.mpr hWCross) := by
    apply Subtype.ext
    calc
      (LevelTree.ancestor z (cut+1)
          (Nat.succ_le_iff.mpr hZCross)).val =
          (⟨cut+1,A.partialTypeAt (cut+1) v.val⟩ :
            RawPartialTypeNode 1 0 1) := hRawUpperZ
      _ = (⟨cut+1,A.partialTypeAt (cut+1) u.val⟩ :
            RawPartialTypeNode 1 0 1) := by rw [hNextType]
      _ = (LevelTree.ancestor w (cut+1)
          (Nat.succ_le_iff.mpr hWCross)).val := hRawUpperW.symm
  exact ⟨w,hW,hZCross,hWCross,hUpperAncestor⟩

/-- Every actual NEW complete paired old/upper dependent Kpt
crossing is present in the old source if the COMPLETE candidate
stage has zero ordinary L at cut and every crossing new node
has an old-live source with the SAME COMPLETE OLD Kpt ancestor.

No I2 functionality, new AlgorithmRun, auxiliary source-node
enumeration, raw positive-L projection or guessed E symmetry. -/
theorem finiteNumericH_candidate_zero_stage_old_socle_covers_full_crossings
    (family : List (NormalizedForbidden 1 0 1))
    (K : AgeTestModel 1 0 1) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hSym : ∀ i j : Nat,
      (finiteNumericH K k N).L.binary i j (0 : Fin 1) =
        (finiteNumericH K k N).L.binary j i (0 : Fin 1))
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid (U : Set (Fin N)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (cut : Nat)
    (hZeroStage : ∀ v : Fin N,
      v ∈ hStageOriginals K k N U (R.I (cut+1)) →
      cut+1 ≤ (finiteNumericH K k N).freeLevel v.val →
      (finiteNumericH K k N).L.binary
        cut v.val (0 : Fin 1) = false)
    (hOldSocle : ∀ (z : AdmissibleKptNode family),
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y →
      ∀ (hZCross : cut < LevelTree.lev z),
        ∃ w : AdmissibleKptNode family,
          w ∈ SMTree.Envelope.closure
            (admissibleKptSTree family) (R.I (cut+1)) X ∧
          ∃ (hWCross : cut < LevelTree.lev w),
          LevelTree.ancestor z cut (Nat.le_of_lt hZCross) =
            LevelTree.ancestor w cut (Nat.le_of_lt hWCross)) :
    FullPhysicalClosureCrossing family
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y) cut ⊆
    FullPhysicalClosureCrossing family
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X) cut := by
  intro p hp
  obtain ⟨z,hZ,hZCross,hOld,hUpper⟩ := hp
  obtain ⟨w,hW,hWCross,hOldEq⟩ :=
    hOldSocle z hZ hZCross
  have hCoveredZ :=
    finiteNumericH_candidate_zero_column_old_socle_upper_covered
      family K k N hAvoid hSym U X Y hXY hY
      top R cut hZeroStage z w
      hZ hW hZCross hWCross hOldEq
  exact kpt_actual_run_upper_cover_gives_full_old_crossing_pair
    family X top R z cut p hCoveredZ hZCross hOld hUpper

/-- At a zero ordinary-L candidate stage with OLD complete
source-socle coverage, one still needs the independent I1
terminal condition. Under that condition the full exact
terminal/crossing NO-NOVELTY predicate follows. -/
theorem finiteNumericH_candidate_zero_stage_noNovelty_of_socle_and_noI1
    (family : List (NormalizedForbidden 1 0 1))
    (K : AgeTestModel 1 0 1) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hSym : ∀ i j : Nat,
      (finiteNumericH K k N).L.binary i j (0 : Fin 1) =
        (finiteNumericH K k N).L.binary j i (0 : Fin 1))
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid (U : Set (Fin N)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (cut : Nat)
    (hZeroStage : ∀ v : Fin N,
      v ∈ hStageOriginals K k N U (R.I (cut+1)) →
      cut+1 ≤ (finiteNumericH K k N).freeLevel v.val →
      (finiteNumericH K k N).L.binary
        cut v.val (0 : Fin 1) = false)
    (hOldSocle : ∀ (z : AdmissibleKptNode family),
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y →
      ∀ (hZCross : cut < LevelTree.lev z),
        ∃ w : AdmissibleKptNode family,
          w ∈ SMTree.Envelope.closure
            (admissibleKptSTree family) (R.I (cut+1)) X ∧
          ∃ (hWCross : cut < LevelTree.lev w),
          LevelTree.ancestor z cut (Nat.le_of_lt hZCross) =
            LevelTree.ancestor w cut (Nat.le_of_lt hWCross))
    (hNoTerminal : ¬ KptI1AtCut family
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y) cut) :
    NewRootNoNoveltyAtCut family
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X)
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y)
      cut := by
  constructor
  · intro hI1
    exact False.elim (hNoTerminal hI1)
  · exact finiteNumericH_candidate_zero_stage_old_socle_covers_full_crossings
      family K k N hAvoid hSym U X Y hXY hY top R
      cut hZeroStage hOldSocle

end Kk
