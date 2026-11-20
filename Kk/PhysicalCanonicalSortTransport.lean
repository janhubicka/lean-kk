import Kk.CanonicalAgeSortPullback
import Kk.K4SingletonOldNeighbour
import Kk.ProtectedActivePivotBudget
import Mathlib.Tactic

/-!
# Track B: canonical age transport for complete physical passing columns

English proof and independent audit preceded this source in
`docs/track_b_physical_canonical_sort_transport_english_audit.md`.

The sort map is arbitrary, including duplication and deletion. The complete
old original pool supplies support monotonicity, rather than requiring a new
application hypothesis. This closes the finite dimension-change gap left by
SupportImageAge; it does not identify full dependent Kpt source records.
-/

namespace Kk

/-- Canonicalization of complete original passing columns commutes with ANY
sort map. All protected originals in P contribute, including active gaps.
No injectivity, surjectivity, graph symmetry or raw-age consistency is needed. -/
theorem finiteOldColumnCanonical_reindex {e d ell : Nat}
    (E : Nat → Nat → Bool) (P : Finset Nat)
    (c : Nat → Fin d → Bool) (pi : Fin e → Fin d)
    (hell : 0 < ell) (U : IntegerGraphSupport e ell) :
    integerGraphAgeCanonical e ell
        (finiteOldColumnRawBound E ell e P (fun p u => c p (pi u))) U =
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d P c)
        (integerGraphSupportImage pi U) := by
  have hRaw :
      finiteOldColumnRawBound E ell e P (fun p u => c p (pi u)) =
        fun V => finiteOldColumnRawBound E ell d P c
          (integerGraphSupportImage pi V) := by
    funext V
    exact finiteOldColumnRawBound_reindex E P c pi V
  rw [hRaw]
  exact integerGraphAgeCanonical_pullback_mono pi hell
    (finiteOldColumnRawBound E ell d P c)
    (fun S T hST => finiteOldColumnRawBound_support_mono E ell d P c S T hST) U

/-- Two successive, possibly noninjective, changes of active sorts have the
canonical age obtained by the two actual support images. This includes a
split followed by deletion and deletion followed by a split. -/
theorem finiteOldColumnCanonical_reindex_twice {f e d ell : Nat}
    (E : Nat → Nat → Bool) (P : Finset Nat)
    (c : Nat → Fin d → Bool)
    (pi : Fin e → Fin d) (sigma : Fin f → Fin e)
    (hell : 0 < ell) (U : IntegerGraphSupport f ell) :
    integerGraphAgeCanonical f ell
        (finiteOldColumnRawBound E ell f P
          (fun p u => c p (pi (sigma u)))) U =
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d P c)
        (integerGraphSupportImage pi (integerGraphSupportImage sigma U)) := by
  calc
    _ = integerGraphAgeCanonical e ell
        (finiteOldColumnRawBound E ell e P (fun p u => c p (pi u)))
        (integerGraphSupportImage sigma U) :=
      finiteOldColumnCanonical_reindex E P (fun p u => c p (pi u)) sigma hell U
    _ = _ := finiteOldColumnCanonical_reindex E P c pi hell
      (integerGraphSupportImage sigma U)

/-- A full mutual-neighbour budget survives a dimension change and the next
actual original. The output is the OLD canonical age on the actual parent
image, rather than an equality solely within the new dimension. -/
theorem finiteOldColumnCanonical_neutral_reindex {e d ell : Nat}
    (E : Nat → Nat → Bool) (b : Nat)
    (c : Nat → Fin d → Bool) (pi : Fin e → Fin d)
    (hell : 0 < ell)
    (hBudget : ∀ V : IntegerGraphSupport d ell,
      (∀ t ∈ V.1, c b t = true) →
      1 + finiteDirectedCliqueCapacity E
        (mutualLinkedNeighbours E
          (oldSupportCommonNeighbourPool (Finset.range b) c V.1) b) ≤
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b) c V.1))
    (U : IntegerGraphSupport e ell) :
    integerGraphAgeCanonical e ell
        (finiteOldColumnRawBound E ell e (Finset.range (b + 1))
          (fun p u => c p (pi u))) U =
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range b) c)
        (integerGraphSupportImage pi U) := by
  rw [integerGraphAgeCanonical_next_prefix_neutral_reindex E b c pi hBudget]
  exact finiteOldColumnCanonical_reindex E (Finset.range b) c pi hell U

/-- The previously proved active-pivot budget test applies to a genuine old
age after ANY change of sorts. Its new graph-age consistency is constructed
by explicit witness transport, rather than added as a hypothesis. This does
not discharge the displayed budgets for a prescribed diary event. -/
theorem protectedPivot_pulledBackAge_iff_budgets {e d ell : Nat}
    (E : Nat → Nat → Bool) (v H : Nat) (hvH : v < H)
    (a : Nat → Fin e → Bool) (beta : Fin e → Bool)
    (pi : Fin e → Fin d) (hell : 0 < ell)
    (F : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell F) :
    AgeLe (fun U => F (integerGraphSupportImage pi U))
      (integerGraphAgeCanonical e ell
        (finiteOldColumnRawBound E ell e (Finset.range H)
          (protectedPivotColumn v a beta))) ↔
    ∀ U : IntegerGraphSupport e ell,
      let X := oldSupportCommonNeighbourPool
        ((Finset.range H).erase v) a U.1
      finiteDirectedCliqueCapacity E X +
          F (integerGraphSupportImage pi U) ≤ ell - 1 ∧
        ((∀ u ∈ U.1, beta u = true) →
          1 + finiteDirectedCliqueCapacity E
            (mutualLinkedNeighbours E X v) +
              F (integerGraphSupportImage pi U) ≤ ell - 1) := by
  exact protectedPivot_targetAge_le_canonical_iff_budgets
    E ell v H hvH a beta
    (fun U => F (integerGraphSupportImage pi U))
    (isIntegerGraphAge_pullback pi hell F hAge)

end Kk
