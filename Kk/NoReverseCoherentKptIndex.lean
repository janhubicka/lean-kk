import Kk.ConstructedCoherentIndexAdapter
import Mathlib.Tactic

/-!
# Track C: a genuine new Kpt source node forbids OLD←NEW literal transport

English-first proof and adversarial scope audit:
  docs/track_c_no_reverse_source_english_audit.md

The verified physical root construction produces a coherent source
map OLD→NEW. The two-way equivalence theorem from Track C PR #304
is CONDITIONAL on a separately supplied reverse map.

A genuinely new full Kpt source node not represented among the old
index nodes makes such a reverse map mathematically impossible.
This result must not be read as constructing a fresh source node
for every root stage: that requires its own physical hypotheses.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

namespace CoherentKptIndex

/-- If the new finite source index contains a genuine complete Kpt
node not equal to ANY old indexed Kpt node, no coherent reverse
NEW→OLD source map can exist. The reverse map's same_node field
would give the forbidden old representative immediately.

The obstruction concerns literal FULL Kpt nodes with dependent E
and upper/old L+ data, not selected ordinary-L graph-age values.
It holds at ANY cut horizon and with arbitrary Boolean live masks. -/
theorem no_reverse_of_fresh_source
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    {P Q : Nat}
    {nodeOld : Fin P → AdmissibleKptNode family}
    {nodeNew : Fin Q → AdmissibleKptNode family}
    {oldLive : Nat → Fin P → Bool}
    {newLive : Nat → Fin Q → Bool}
    (hFresh : ∃ j : Fin Q,
      ∀ i : Fin P, nodeNew j ≠ nodeOld i)
    (horizon : Nat) :
    ¬ CoherentKptIndex family nodeNew nodeOld
        newLive oldLive horizon := by
  intro reverse
  obtain ⟨j, hNotOld⟩ := hFresh
  exact (hNotOld (reverse.map j))
    ((reverse.same_node j).symm)

/-- A coherent reverse source-map between complete Fin-indexed
Kpt universes is injective. Hence strict growth of the number
of new index names is itself an obstruction to NEW→OLD transport.

This does NOT assert actual physical root growth always increases
source cardinality. It is a conditional finite-count certificate. -/
theorem no_reverse_of_strict_cardinality
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    {P Q : Nat}
    {nodeOld : Fin P → AdmissibleKptNode family}
    {nodeNew : Fin Q → AdmissibleKptNode family}
    {oldLive : Nat → Fin P → Bool}
    {newLive : Nat → Fin Q → Bool}
    (hCard : P < Q)
    (horizon : Nat) :
    ¬ CoherentKptIndex family nodeNew nodeOld
        newLive oldLive horizon := by
  intro reverse
  have hImpossible : Q ≤ P := by
    simpa only [Fintype.card_fin] using
      (Fintype.card_le_of_injective
        reverse.map reverse.map_injective)
  omega

end CoherentKptIndex

end Kk
