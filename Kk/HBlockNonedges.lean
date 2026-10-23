import SuccessorTree.V10.HInfiniteBaseEmbedding
import Mathlib.Tactic

/-!
# Nonadjacency of reserved original blocks survives every H generation

The resolved-copy proof reserves auxiliary clique blocks in the original
K_ell-free graph and makes different blocks mutually nonadjacent.
For the ACTUAL numerical H construction, every directed L atom on
a real-real generation pair is copied from the corresponding
original pair, when the generation gate permits it, and otherwise
it is absent.

Thus a forbidden original directed relation remains absent
between ALL generation copies of that original pair. This is a
genuine numerical H fact, not an abstract block-template axiom.

It supplies only the cross-block nonedge part of the missing (B3)
projection. Intra-block auxiliary type incidences and all E/parameter
closure tests still require the diary-specific witness argument.
-/

namespace Kk

open SuccessorTree.V10

/-- No positive directed relation can be introduced by H's
generation gate between two distinct original indices whose
original directed relation bit is absent. -/
theorem numericH_preserves_original_nonedge
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k i j q m : Nat)
    (hij : i < j) (hq : q ≤ k) (hm : m ≤ k)
    (hNonedge : ∀ t : Fin db, K.binary i j t = false) :
    ∀ t : Fin db,
      (infiniteNumericHL K k).binary
        (hPosition k i q) (hPosition k j m) t = false := by
  intro t
  change hNumericBinary K.binary k
      (hPosition k i q) (hPosition k j m) t = false
  cases h : hNumericBinary K.binary k
      (hPosition k i q) (hPosition k j m) t with
  | false => rfl
  | true =>
      have hB := ((hNumericBinary_real_forward_iff K.binary
        k i j q m t hij hq hm).mp h).2
      rw [hNonedge t] at hB
      cases hB

/-- The identical absence statement for the finite constructed H
L-reduct. Truncating the carrier changes no binary table values. -/
theorem finiteNumericH_preserves_original_nonedge
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N i j q m : Nat)
    (hij : i < j) (hq : q ≤ k) (hm : m ≤ k)
    (hNonedge : ∀ t : Fin db, K.binary i j t = false) :
    ∀ t : Fin db,
      (finiteNumericHL K k N).binary
        (hPosition k i q) (hPosition k j m) t = false := by
  intro t
  exact numericH_preserves_original_nonedge K k i j q m
    hij hq hm hNonedge t

end Kk
