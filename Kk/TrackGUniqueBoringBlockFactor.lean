import Kk.TrackGGenuineBoringBlockFactor
import Mathlib.Tactic

/-!
# Track G: genuine boring-block monoid factor is UNIQUE for one run.

The merged G305 block theorem constructs one total MMap factor
D from complete actual boring-stage semantics. Injectivity of
the genuine outer shape map makes this D uniquely determined
by its endpoint total monoid maps. This corrects an earlier
too-pessimistic English qualification.

English proof and hostile audit FIRST:
docs/track_g_unique_actual_boring_factor_english_audit_20261117.md

NOT proved: equality of factors between unrelated diary occurrences,
any bound on the factor's total labelled complexity, a coherent
inverse source orbit or a global Kk-free BRD characterization.
-/

namespace Kk

universe u v

open SuccessorTree
open SuccessorTree.SMTree

/-- Cancellation on the LEFT by a genuine injective MMap:
if F∘D=F∘E then D=E as TOTAL MMaps, not just their
graph-age shadows or actions on a selected finite subfamily. -/
theorem kpt_MMap_comp_left_cancel
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    {S : STree T Label}
    (H : SMTree S)
    (F D E : MMap H)
    (hEq : MMap.comp H F D = MMap.comp H F E) :
    D = E := by
  apply MMap.ext_apply
  intro x
  have hAt : F (D x) = F (E x) := by
    have hxEq :=
      congrArg (fun G : MMap H => G x) hEq
    simpa only [MMap.comp_apply] using hxEq
  exact F.map.injective hAt

/-- A finite block genuinely boring at EVERY complete Kpt
pre-cut stage has unchanged selected levels and precisely ONE
aggregate total monoid factor. It need not be identity or
a single-gap skip map, nor match factors of another diary
occurrence without equality of the actual endpoint maps. -/
theorem actualAlgorithmRun_genuinely_boring_block_unique_factor
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    {S : STree T Label}
    (H : SMTree S) (X : Set T)
    (top low high : Nat)
    (R : SMTree.Envelope.AlgorithmRun H X top)
    (hLowHigh : low ≤ high) (hHigh : high ≤ top)
    (hBoring : ∀ i : Nat, low ≤ i → i < high →
      ¬ SMTree.Envelope.IsInterestingAt H
        (SMTree.Envelope.closure S (R.I (i+1)) X) i) :
    R.I low = R.I high ∧
      ∃! D : MMap H,
        R.F low = MMap.comp H (R.F high) D := by
  obtain ⟨hI, D, hD⟩ :=
    actualAlgorithmRun_genuinely_boring_block_factors
      H X top low high R hLowHigh hHigh hBoring
  constructor
  · exact hI
  · refine ⟨D, hD, ?_⟩
    intro E hE
    exact kpt_MMap_comp_left_cancel H (R.F high) D E
      (hD.symm.trans hE)

end Kk
