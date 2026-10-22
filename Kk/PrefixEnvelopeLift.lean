import Kk.PrefixChainOrbitTransfer
import SuccessorTree.V10.GPlusEnvelopePairLift
import Mathlib.Tactic

/-!
# Pulling a genuine G+ prefix chain through a Kpt envelope

The original diary carrier argument used to leave a separate
"source preimages form a prefix chain" hypothesis. That is
unnecessary once the target vertices are already genuine prefixes
of a common top and the envelope covers their representing pairs.

The induced G+ action reflects the ENTIRE four-table prefix order.
Consequently every actual family of preimages of a target prefix
chain forms another prefix chain. The source may be compressed,
although it need not be equal to the compressed source of a
different envelope: the cross-occurrence labelled comparison
remains the mathematical gap.

This result does not infer that unrelated finite G+ codes form a
prefix chain, and does not infer that two diary occurrences have
identical labelled preimages.
-/

namespace Kk

open SuccessorTree.V10

universe u

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}
variable {Λ : Type u}

/-- A genuine shape-map image which covers a target prefix chain
automatically has a labelled prefix-chain preimage. No separate
source-prefix or boundedness assumption is needed.

The target top may or may not be one of the labelled target points:
it is represented separately to allow nonempty auxiliary caps. -/
theorem labelled_prefix_preimages_of_range
    (F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (top : FiniteGPlusVertex family)
    (points : Λ → FiniteGPlusVertex family)
    (hPrefix : ∀ a, (points a).val.IsPrefix top.val)
    (hInjective : Function.Injective points)
    (hTopRange : top ∈ Set.range (gPlusShapeImage F.map))
    (hPointsRange : ∀ a, points a ∈ Set.range (gPlusShapeImage F.map)) :
    ∃ (sourceTop : FiniteGPlusVertex family)
      (source : Λ → FiniteGPlusVertex family),
      Function.Injective source ∧
      (∀ a, (source a).val.IsPrefix sourceTop.val) ∧
      gPlusShapeImage F.map sourceTop = top ∧
      ∀ a, gPlusShapeImage F.map (source a) = points a := by
  classical
  obtain ⟨sourceTop, hTop⟩ := hTopRange
  choose source hSource using hPointsRange
  have hSourceInjective : Function.Injective source := by
    intro a b hab
    apply hInjective
    calc
      points a = gPlusShapeImage F.map (source a) := (hSource a).symm
      _ = gPlusShapeImage F.map (source b) := congrArg _ hab
      _ = points b := hSource b
  have hSourcePrefix : ∀ a, (source a).val.IsPrefix sourceTop.val := by
    intro a
    apply gPlusShapeImage_reflects_prefix F.map (source a) sourceTop
    rw [hSource a, hTop]
    exact hPrefix a
  exact ⟨sourceTop, source, hSourceInjective,
    hSourcePrefix, hTop, hSource⟩

/-- When the target top and its labelled vertices come from actual
representing pairs whose endpoints lie in one Kpt envelope, their
preimages form a labelled genuine G+ prefix chain.

This combines the checked endpoint-envelope lift with the checked
reflection of complete finite-code prefixes. It does NOT require
the two labelled occurrences to have any diary invariant yet. -/
theorem labelled_prefix_sources_of_Kpt_envelope
    (F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (X : Set (AdmissibleKptNode family))
    (hEnvelope : SuccessorTree.SMTree.Envelope.IsEnvelope F.map X)
    (top : FiniteGPlusVertex family)
    (points : Λ → FiniteGPlusVertex family)
    (hPrefix : ∀ a, (points a).val.IsPrefix top.val)
    (hInjective : Function.Injective points)
    (topPair : GPlusRepresentingPair family)
    (hTopPair : topPair.vertex = top)
    (hTopEnds : topPair.lower ∈ X ∧ topPair.upper ∈ X)
    (pairs : Λ → GPlusRepresentingPair family)
    (hPairs : ∀ a, (pairs a).vertex = points a)
    (hEnds : ∀ a, (pairs a).lower ∈ X ∧ (pairs a).upper ∈ X) :
    ∃ (sourceTop : FiniteGPlusVertex family)
      (source : Λ → FiniteGPlusVertex family),
      Function.Injective source ∧
      (∀ a, (source a).val.IsPrefix sourceTop.val) ∧
      gPlusShapeImage F.map sourceTop = top ∧
      ∀ a, gPlusShapeImage F.map (source a) = points a := by
  have hTopRange : top ∈ Set.range (gPlusShapeImage F.map) := by
    rw [← hTopPair]
    exact gPlus_vertex_mem_image_of_Kpt_envelope
      F.map X hEnvelope topPair hTopEnds.1 hTopEnds.2
  have hPointsRange : ∀ a, points a ∈
      Set.range (gPlusShapeImage F.map) := by
    intro a
    rw [← hPairs a]
    exact gPlus_vertex_mem_image_of_Kpt_envelope
      F.map X hEnvelope (pairs a) (hEnds a).1 (hEnds a).2
  exact labelled_prefix_preimages_of_range
    F top points hPrefix hInjective hTopRange hPointsRange

end Kk
