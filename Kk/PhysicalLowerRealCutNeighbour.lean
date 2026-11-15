import Kk.NumericPrefixGapZero
import Mathlib.Tactic

/-!
# Track D: exact later positive physical neighbours of a lower real H cut

English-first proof and 17 hostile checks:
docs/audits/2026-11-15-track-d-physical-lower-cut-neighbours-english.md

For a genuine physical numerical-H cut hPosition k i g with g<k,
a later physical positive ordinary-L neighbour is necessarily
a REAL copy of a LATER BASE j>i at a STRICTLY HIGHER GENERATION
m>g. In the Henson finite model the ordinary-L atom is exactly
the base graph E i j, including its directed tuple orientation.

The reverse generator orientation is excluded using the actual
numerical H address order. The special top-to-top gate is excluded
ONLY because g<k, not by incorrectly assuming that no such gate exists.

This does not equate physical auxiliary parameters with active
diary branches or certify a whole corrected-(B3) source.
-/

namespace Kk

open SuccessorTree.V10

/-- A true physical L atom from a non-top REAL numerical-H cut to
a STRICTLY LATER numeric address comes precisely from a
later base at a higher generation, with the SAME directed
base relation bit. No symmetry of B is assumed. -/
theorem physical_lower_real_cut_positive_generators
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k i g y : Nat) (t : Fin d)
    (hg : g < k)
    (hLater : hPosition k i g < y)
    (hPositive :
      hNumericBinary B k (hPosition k i g) y t = true) :
    ∃ j m : Nat,
      i < j ∧ g < m ∧ m ≤ k ∧
      y = hPosition k j m ∧ B i j t = true := by
  obtain ⟨u,j,q,m,huj,hq,hm,hgate,hdir⟩ :=
    (hNumericBinary_true_iff B k
      (hPosition k i g) y t).mp hPositive
  rcases hdir with ⟨hCut,hY,hB⟩ | ⟨hCut,hY,hB⟩
  · obtain ⟨hiu,hgq⟩ :=
      hPosition_injective_bounded k i g u q
        (Nat.le_of_lt hg) hq hCut
    have hGm : g < m := by
      rcases hgate with hLess | ⟨hSame,hTop⟩
      · omega
      · omega
    refine ⟨j,m,?_,hGm,hm,hY,?_⟩
    · omega
    · simpa only [hiu] using hB
  · have hSmaller :
        hPosition k u q < hPosition k j m :=
      hPosition_lt_of_block_lt k u j q m hq huj
    have hReverse : y < hPosition k i g := by
      calc
        y = hPosition k u q := hY
        _ < hPosition k j m := hSmaller
        _ = hPosition k i g := hCut.symm
    exact False.elim (by omega)

/-- Exact physical Boolean equivalence for ALL later addresses:
positive directed L bit iff y is a strictly higher-generation
real copy of a later base with the corresponding base L bit true.

The assumption cut<y excludes reversed generators and must
not be omitted for arbitrary directed Boolean base relations.
-/
theorem physical_lower_real_cut_positive_iff
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k i g y : Nat) (t : Fin d)
    (hg : g < k)
    (hLater : hPosition k i g < y) :
    hNumericBinary B k (hPosition k i g) y t = true ↔
      ∃ j m : Nat, i < j ∧ g < m ∧ m ≤ k ∧
        y = hPosition k j m ∧ B i j t = true := by
  constructor
  · exact physical_lower_real_cut_positive_generators
      B k i g y t hg hLater
  · rintro ⟨j,m,hij,hgm,hm,hY,hBit⟩
    rw [hY]
    exact (hNumericBinary_real_forward_iff
      B k i j g m t hij (Nat.le_of_lt hg) hm).2
        ⟨Or.inl hgm,hBit⟩

/-- For a real lower-generation physical cut c, a genuine
cut-ELIGIBLE selected original with positive L(c,v) must
be a later base j>i in a STRICTLY higher generation m>g,
with actual positive original base atom E(i,j).

This applies to any actual original name, including an
auxiliary full-closure parameter name; no no-I2 or
selected-diary projection is assumed.
-/
theorem finiteNumericH_eligible_lower_cut_neighbour_is_higher
    (E : Nat → Nat → Bool)
    (k N i g : Nat)
    (hg : g < k)
    (hCut : hPosition k i g < N)
    (v : Fin N)
    (hFree : hPosition k i g + 1 ≤
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val)
    (hPositive :
      (finiteNumericHL (normalizedGraphModel E) k N).binary
        (hPosition k i g) v.val (0 : Fin 1) = true) :
    ∃ j m : Nat, i < j ∧ g < m ∧ m ≤ k ∧
      v.val = hPosition k j m ∧ E i j = true := by
  have hAfter : hPosition k i g < v.val := by
    have hBound :=
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel_le v.val
    omega
  change hNumericBinary (normalizedGraphModel E).binary k
    (hPosition k i g) v.val (0 : Fin 1) = true at hPositive
  obtain ⟨j,m,hij,hgm,hm,hAddress,hBit⟩ :=
    physical_lower_real_cut_positive_generators
      (normalizedGraphModel E).binary k i g v.val
      (0 : Fin 1) hg hAfter hPositive
  refine ⟨j,m,hij,hgm,hm,hAddress,?_⟩
  change E i j = true at hBit
  exact hBit

#print axioms physical_lower_real_cut_positive_generators
#print axioms physical_lower_real_cut_positive_iff
#print axioms finiteNumericH_eligible_lower_cut_neighbour_is_higher

end Kk
