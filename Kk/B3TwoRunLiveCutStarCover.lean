import Kk.B3TwoActualRuns
import Mathlib.Tactic

/-!
# Track B: true live Kpt-node matching across TWO actual runs

English proof and adversarial audit were committed FIRST:
  docs/track_b_live_index_cutstar_transport_english_audit.md

The cross-run matching hypothesis concerns ONLY actual, live,
CUT-CROSSING Kpt nodes with a POSITIVE ordinary-L edge to the
tested cut and equality of COMPLETE upper ordinary-L reducts.
The old dependent L+ node type, auxiliary E bits, node-index
cardinality/multiplicity, selected shadow age and all
non-cut-adjacent upper records are allowed to differ.

This is strictly weaker than matching complete old/upper
dependent L+ crossing pairs in Track E. It suffices for the
local full corrected B3 comparison, under the verified
true-AlgorithmRun full-source and same-base hypotheses.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A physical one-sided cover of the POSITIVE-CUT complete upper-L
types contributed by actually LIVE Kpt nodes from source index A
with real nodes of a different source index B.

Both old and upper full L+ values are extracted from the SAME
actual Kpt node on each side. The complete UPPER ordinary-L
reduct is preserved but the old dependent L+ type, E, node label
and number of witnesses need NOT agree.

This relation is meaningful even at I2 forks: no selected B3
partial function is being formed here. -/
def IndexedCutStarLiveCover
    (family : List (NormalizedForbidden 1 0 1))
    {ParamsA ParamsB : Type}
    (nodeA : ParamsA → AdmissibleKptNode family)
    (liveA : Nat → ParamsA → Bool)
    (nodeB : ParamsB → AdmissibleKptNode family)
    (liveB : Nat → ParamsB → Bool)
    (cut : Nat) : Prop :=
  ∀ (j : ParamsA)
    (T : PartialTypeWithE cut 1 0 1)
    (U : PartialTypeWithE (cut+1) 1 0 1),
      liveA cut j = true →
      kptFullOldAtCut (nodeA j) cut =
        some (⟨cut,T⟩ : RawPartialTypeNode 1 0 1) →
      kptFullUpperAtCut (nodeA j) cut =
        some (⟨cut+1,U⟩ : RawPartialTypeNode 1 0 1) →
      U.lReduct.binary
        (some (⟨cut,Nat.lt_succ_self cut⟩ : Fin (cut+1)))
        none (0 : Fin 1) = true →
      ∃ i : ParamsB,
        ∃ S : PartialTypeWithE cut 1 0 1,
        ∃ V : PartialTypeWithE (cut+1) 1 0 1,
          liveB cut i = true ∧
          kptFullOldAtCut (nodeB i) cut =
            some (⟨cut,S⟩ : RawPartialTypeNode 1 0 1) ∧
          kptFullUpperAtCut (nodeB i) cut =
            some (⟨cut+1,V⟩ : RawPartialTypeNode 1 0 1) ∧
          V.lReduct = U.lReduct

/-- Matching EACH true live CUT-ADJACENT source node's complete
upper ordinary-L type in the other actual finite source index
implies inclusion of their whole intrinsic positive-cut L spectra.

This proof does NOT require comparing the physical OLD L+ source
records: they can differ while B3's upper-L test remains the same. -/
theorem indexed_cutStar_upperL_of_live_cover
    (family : List (NormalizedForbidden 1 0 1))
    {ParamsA ParamsB : Type}
    (nodeA : ParamsA → AdmissibleKptNode family)
    (liveA : Nat → ParamsA → Bool)
    (nodeB : ParamsB → AdmissibleKptNode family)
    (liveB : Nat → ParamsB → Bool)
    (cut : Nat)
    (hCover : IndexedCutStarLiveCover
      family nodeA liveA nodeB liveB cut) :
    ∀ R : RelationalPrefixType (cut+1) 1 0 1,
      IndexedPhysicalCutStarUpperL family nodeA liveA cut R →
      IndexedPhysicalCutStarUpperL family nodeB liveB cut R := by
  intro R hR
  obtain ⟨T,U,⟨j,hLive,hOld,hUpper⟩,hReduct,hBit⟩ := hR
  have hBitU :
      U.lReduct.binary
        (some (⟨cut,Nat.lt_succ_self cut⟩ : Fin (cut+1)))
        none (0 : Fin 1) = true := by
    rw [hReduct]
    exact hBit
  obtain ⟨i,S,V,hLiveB,hOldB,hUpperB,hSame⟩ :=
    hCover j T U hLive hOld hUpper hBitU
  exact ⟨S,V,⟨i,hLiveB,hOldB,hUpperB⟩,
    hSame.trans hReduct,hBit⟩

/-- Two-sided physical LIVE-node matching of complete positive-cut
UPPER ordinary-L types gives EQUALITY of the projected spectra.

This is strictly weaker than a complete FULL old/upper dependent
L+ crossing relation isomorphism: no matching of old E source,
unrelated event labels, or index cardinalities is assumed. -/
theorem indexed_cutStar_iff_of_bilateral_live_cover
    (family : List (NormalizedForbidden 1 0 1))
    {ParamsA ParamsB : Type}
    (nodeA : ParamsA → AdmissibleKptNode family)
    (liveA : Nat → ParamsA → Bool)
    (nodeB : ParamsB → AdmissibleKptNode family)
    (liveB : Nat → ParamsB → Bool)
    (cut : Nat)
    (hAB : IndexedCutStarLiveCover
      family nodeA liveA nodeB liveB cut)
    (hBA : IndexedCutStarLiveCover
      family nodeB liveB nodeA liveA cut) :
    ∀ R : RelationalPrefixType (cut+1) 1 0 1,
      IndexedPhysicalCutStarUpperL family nodeA liveA cut R ↔
      IndexedPhysicalCutStarUpperL family nodeB liveB cut R := by
  intro R
  constructor
  · exact indexed_cutStar_upperL_of_live_cover
      family nodeA liveA nodeB liveB cut hAB R
  · exact indexed_cutStar_upperL_of_live_cover
      family nodeB liveB nodeA liveA cut hBA R

namespace HensonRunCutData

variable
    {ell : Nat} {hell : 2 ≤ ell}
    {k : Nat} {hK : ell ≤ k+1}
    {E : Nat → Nat → Bool}
    {hLoops : ∀ i, E i i = false}
    {hSym : ∀ x y, E x y = E y x}
    {hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true)}
    {cut : Nat}

/-- For TWO genuine finite numerical-Henson AlgorithmRuns over ONE
base E/k and source-cut c, CONSTRUCT independently exhaustive true
finite final Kpt-node indexes and per-cut live masks.

A two-sided name-by-name relation between their ACTUALLY LIVE,
genuinely cut-crossing, physically L-adjacent Kpt nodes which
preserves only complete UPPER ordinary-L type suffices for
equivalence of their FULL corrected B3 tests.

No equality of finite name universes, old dependent L+ records,
auxiliary E source columns, full event labels, seed sets, or
common labelled inverse-source monoid orbits is inferred. -/
theorem two_runs_finite_live_cutStar_cover_controls_full_B3
    (P Q : HensonRunCutData ell hell k hK E hLoops hSym hClique cut) :
    ∃ paramsP : Finset (AdmissibleKptNode (hensonForbiddenFamily ell hell)),
      ∃ liveP : Nat → Fin paramsP.card → Bool,
      ∃ paramsQ : Finset (AdmissibleKptNode (hensonForbiddenFamily ell hell)),
      ∃ liveQ : Nat → Fin paramsQ.card → Bool,
        (∀ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
          z ∈ paramsP ↔
            z ∈ SMTree.Envelope.closure
              (admissibleKptSTree (hensonForbiddenFamily ell hell))
              (P.run.I 0) P.X) ∧
        (∀ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
          z ∈ paramsQ ↔
            z ∈ SMTree.Envelope.closure
              (admissibleKptSTree (hensonForbiddenFamily ell hell))
              (Q.run.I 0) Q.X) ∧
        (∀ R : RelationalPrefixType (cut+1) 1 0 1,
          IndexedPhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
            (fun j : Fin paramsP.card => (paramsP.equivFin.symm j).val)
            liveP cut R ↔
          PhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
            P.occurrence.Z cut R) ∧
        (∀ R : RelationalPrefixType (cut+1) 1 0 1,
          IndexedPhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
            (fun j : Fin paramsQ.card => (paramsQ.equivFin.symm j).val)
            liveQ cut R ↔
          PhysicalCutStarUpperL (hensonForbiddenFamily ell hell)
            Q.occurrence.Z cut R) ∧
        ((IndexedCutStarLiveCover (hensonForbiddenFamily ell hell)
            (fun j : Fin paramsP.card => (paramsP.equivFin.symm j).val)
            liveP
            (fun j : Fin paramsQ.card => (paramsQ.equivFin.symm j).val)
            liveQ cut ∧
          IndexedCutStarLiveCover (hensonForbiddenFamily ell hell)
            (fun j : Fin paramsQ.card => (paramsQ.equivFin.symm j).val)
            liveQ
            (fun j : Fin paramsP.card => (paramsP.equivFin.symm j).val)
            liveP cut) →
          (P.occurrence.fullProfile.CorrectedB3
             (hensonForbiddenFamily ell hell) ↔
           Q.occurrence.fullProfile.CorrectedB3
             (hensonForbiddenFamily ell hell))) := by
  classical
  obtain ⟨paramsP,liveP,paramsQ,liveQ,hParamsP,hParamsQ,
    hPhysicalP,hPhysicalQ,hTransfer⟩ :=
    two_runs_finite_indexed_cutStar_controls_full_B3 P Q
  refine ⟨paramsP,liveP,paramsQ,liveQ,hParamsP,hParamsQ,
    hPhysicalP,hPhysicalQ,?_⟩
  intro hBoth
  apply hTransfer
  exact indexed_cutStar_iff_of_bilateral_live_cover
    (hensonForbiddenFamily ell hell)
    (fun j : Fin paramsP.card => (paramsP.equivFin.symm j).val)
    liveP
    (fun j : Fin paramsQ.card => (paramsQ.equivFin.symm j).val)
    liveQ cut hBoth.1 hBoth.2

end HensonRunCutData

#print axioms Kk.indexed_cutStar_upperL_of_live_cover
#print axioms Kk.indexed_cutStar_iff_of_bilateral_live_cover
#print axioms Kk.HensonRunCutData.two_runs_finite_live_cutStar_cover_controls_full_B3

end Kk
