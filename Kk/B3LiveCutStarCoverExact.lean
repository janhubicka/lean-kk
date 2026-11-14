import Kk.B3TwoRunLiveCutStarCover
import Mathlib.Tactic

/-!
# Track B: physical live-node name coverage is EXACTLY cut-star inclusion

English-first proof and twelve adversarial checks:
  docs/track_b_live_cutstar_exact_cover_english_audit.md

The Kpt cut-star live-node cover introduced in the previous Track B
module is not a hidden additional source assumption: it is precisely
equivalent to one-sided inclusion of the complete positive-cut upper
ordinary-L type spectrum of two actual Kpt live-node indexes.

No matching of old dependent L+ type, auxiliary E, node label,
multiplicity, or irrelevant non-cut-adjacent upper types is claimed.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Physical name-by-name live-index cover in one direction
is EQUIVALENT to inclusion of the corresponding complete
positive-cut upper ordinary-L spectra.

The reverse direction unwraps the ACTUAL indexed cut-star witness
from one source node j, uses the permitted type in B and recovers
a genuinely live source i with its own OLD and UPPER full Kpt
ancestor records. No no-(I2) assumption is needed at relation
level. There is no finite-index cardinality or injection premise. -/
theorem indexed_cutStar_live_cover_iff_upperL_inclusion
    (family : List (NormalizedForbidden 1 0 1))
    {ParamsA ParamsB : Type}
    (nodeA : ParamsA → AdmissibleKptNode family)
    (liveA : Nat → ParamsA → Bool)
    (nodeB : ParamsB → AdmissibleKptNode family)
    (liveB : Nat → ParamsB → Bool)
    (cut : Nat) :
    IndexedCutStarLiveCover family nodeA liveA nodeB liveB cut ↔
      ∀ R : RelationalPrefixType (cut+1) 1 0 1,
        IndexedPhysicalCutStarUpperL family nodeA liveA cut R →
        IndexedPhysicalCutStarUpperL family nodeB liveB cut R := by
  constructor
  · exact indexed_cutStar_upperL_of_live_cover
      family nodeA liveA nodeB liveB cut
  · intro hSubset j T U hLive hOld hUpper hBit
    have hInA :
        IndexedPhysicalCutStarUpperL
          family nodeA liveA cut U.lReduct :=
      ⟨T,U,⟨j,hLive,hOld,hUpper⟩,rfl,hBit⟩
    obtain ⟨S,V,⟨i,hi,hOldB,hUpperB⟩,hSame,_hPositive⟩ :=
      hSubset U.lReduct hInA
    exact ⟨i,S,V,hi,hOldB,hUpperB,hSame⟩

/-- TWO-SIDED matching of genuinely live cut-crossing source nodes
by their COMPLETE positive-cut next ordinary-L reducts is
equivalent to equality of the corresponding projected spectra.

This equivalence includes empty spectra and makes no assertion
about a bijection of full dependent Kpt source nodes or common
labelled inverse-source monoid orbit. -/
theorem indexed_cutStar_bilateral_live_cover_iff_spectra_equal
    (family : List (NormalizedForbidden 1 0 1))
    {ParamsA ParamsB : Type}
    (nodeA : ParamsA → AdmissibleKptNode family)
    (liveA : Nat → ParamsA → Bool)
    (nodeB : ParamsB → AdmissibleKptNode family)
    (liveB : Nat → ParamsB → Bool)
    (cut : Nat) :
    (IndexedCutStarLiveCover family nodeA liveA nodeB liveB cut ∧
     IndexedCutStarLiveCover family nodeB liveB nodeA liveA cut) ↔
      ∀ R : RelationalPrefixType (cut+1) 1 0 1,
        IndexedPhysicalCutStarUpperL family nodeA liveA cut R ↔
        IndexedPhysicalCutStarUpperL family nodeB liveB cut R := by
  constructor
  · rintro ⟨hAB,hBA⟩
    exact indexed_cutStar_iff_of_bilateral_live_cover
      family nodeA liveA nodeB liveB cut hAB hBA
  · intro hEq
    constructor
    · exact (indexed_cutStar_live_cover_iff_upperL_inclusion
        family nodeA liveA nodeB liveB cut).2
          (fun R hA => (hEq R).mp hA)
    · exact (indexed_cutStar_live_cover_iff_upperL_inclusion
        family nodeB liveB nodeA liveA cut).2
          (fun R hB => (hEq R).mpr hB)

#print axioms Kk.indexed_cutStar_live_cover_iff_upperL_inclusion
#print axioms Kk.indexed_cutStar_bilateral_live_cover_iff_spectra_equal

end Kk
