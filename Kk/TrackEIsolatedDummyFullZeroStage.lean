import Kk.TrackDZeroStageActualRunSkip
import Mathlib.Tactic

/-!
# Track E E81: genuine isolated original-Q bases have ZERO physical L cut columns

English proof and 21 hostile checks committed FIRST:
docs/track_e_isolated_dummy_zero_stage_transport_english_audit_20261121.md

For a literal lower-real H+ source cut c=hPosition(k,idx,g) with
g<k, c<N, if base idx is isolated in the ACTUAL original-Q graph
E, then EVERY genuine physical original v:Fin N whose canonical
auxiliary E-free level extends beyond c has ordinary L(c,v)=0.

This is a DIRECT consequence of the independently verified exact
numerical-H+ eligible lower-cut positive neighbour theorem used
by Track D. It is valid for ALL eligible originals, not merely
selected graph-age or proposed stage Plan names. No AlgorithmRun
is needed and auxiliary directed E is not symmetrized.

Once the E80 whole-run theorem is verified, the isolated-dummy
class automatically supplies E80's zero-stage hypothesis; maximal
OLD Kpt prefix witnesses and other physical cut classes remain
independent and unresolved for the global diary.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A genuinely ISOLATED original-Q base idx has no positive
ordinary-L bit at the lower REAL numerical-H+ source cut
c=hPosition(k,idx,g) to ANY physical original crossing c.

The numerical carrier bound c<N, lower generation g<k and
actual free E-cut crossing are essential. This proof uses
real original-Q adjacency E(idx,j), not an artificial E bit
on a pure graph L continuation, and needs no AlgorithmRun,
old/new Kpt source enumeration or intended diary Plan. -/
theorem finiteNumericH_isolated_base_all_eligible_lower_real_L_zero
    (E : Nat → Nat → Bool)
    (k N idx g : Nat) (hg : g < k)
    (hCut : hPosition k idx g < N)
    (hIsolated : ∀ j : Nat, E idx j = false)
    (v : Fin N)
    (hFree : hPosition k idx g + 1 ≤
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val) :
    (finiteNumericH (normalizedGraphModel E) k N).L.binary
      (hPosition k idx g) v.val (0 : Fin 1) = false := by
  by_cases hp :
      (finiteNumericH (normalizedGraphModel E) k N).L.binary
        (hPosition k idx g) v.val (0 : Fin 1) = true
  · obtain ⟨j,m,_hij,_hgm,_hm,_hAddress,hBase⟩ :=
      finiteNumericH_eligible_lower_cut_neighbour_is_higher
        E k N idx g hg hCut v hFree hp
    have hZero : E idx j = false := hIsolated j
    rw [hZero] at hBase
    cases hBase
  · cases h :
      (finiteNumericH (normalizedGraphModel E) k N).L.binary
        (hPosition k idx g) v.val (0 : Fin 1) with
      | false => rfl
      | true => exact False.elim (hp h)

/-- Every TRUE physical original stage pool U∪positiveSelected(J)
inherits the isolated-Q-base zero column, for ANY finite U and
ANY source-level set J. Stage originals are not selected original
fronts: meets and dependent parameters may have genuine original
representatives inside this full stage pool. This result needs no
equality between a proposed resolved-Q Plan and an actual run. -/
theorem finiteNumericH_isolated_base_full_stage_zero
    (E : Nat → Nat → Bool)
    (k N idx g : Nat) (hg : g < k)
    (hCut : hPosition k idx g < N)
    (hIsolated : ∀ j : Nat, E idx j = false)
    (U : Finset (Fin N)) (J : Set Nat) :
    ∀ v : Fin N,
      v ∈ hStageOriginals (normalizedGraphModel E) k N U J →
      hPosition k idx g + 1 ≤
        (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val →
      (finiteNumericH (normalizedGraphModel E) k N).L.binary
        (hPosition k idx g) v.val (0 : Fin 1) = false := by
  intro v _hStage hFree
  exact finiteNumericH_isolated_base_all_eligible_lower_real_L_zero
    E k N idx g hg hCut hIsolated v hFree

end Kk
