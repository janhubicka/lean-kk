import Kk.IntegerAgeSmallFunction
import Mathlib.Tactic

/-!
# Track F: complete pre-code profile rigidity from the legal zero-code law

The mathematical proof and 16 hostile checks were committed FIRST:
docs/track_f_zero_code_preprofile_rigidity_english_audit_20261121.md

A true pre-code INTEGER age P bounded above by the planned age F
cannot lose any hidden mixed-support capacity when:
  * all survivor supports already have the same P and F values;
  * the deleted singleton has the prescribed common rank-one bound;
  * the full zero-code legality F(T) = F(T \ {j}) holds for every
    admissible NONSINGLETON support containing the coded sort j.

The proof uses verified physical-domain monotonicity of actual
normalized integer graph ages, and handles the singleton separately
so it never invents an empty support value.

This is ONLY the algebraic "pre-code sandwich" of the manuscript.
It neither chooses the actual coded vertex nor synchronizes survivors,
and it does not establish full diary unavoidability or BRDs.
-/

namespace Kk

/-- Exact domain-safe zero-code rigidity: if a genuine normalized
integer graph age P lies below the prescribed pre-code profile F,
agrees with F on all nonempty supports without j and on the
singleton {j}, and F obeys the zero-code equality on every mixed
admissible support T, then P is equal to F on ALL supports.

In particular no new strict mixed triple-support profile decrease
can be hidden immediately before the independent code.

The singleton hypotheses are stated as rank-one values, so they
match the manuscript's independent-code condition. No empty-support
graph-age value is ever introduced. -/
theorem integerGraphAge_zeroCode_preprofile_rigidity
    (d ell : Nat) (j : Fin d)
    (F P : IntegerGraphSupport d ell → Nat)
    (hPAge : IsIntegerGraphAge d ell P)
    (hPLe : AgeLe P F)
    (hSurvivors : ∀ S : IntegerGraphSupport d ell,
      j ∉ S.1 → P S = F S)
    (hPOne : ∀ T : IntegerGraphSupport d ell,
      T.1 = {j} → P T = 1)
    (hFOne : ∀ T : IntegerGraphSupport d ell,
      T.1 = {j} → F T = 1)
    (hLegal : ∀ T : IntegerGraphSupport d ell,
      j ∈ T.1 →
      ∀ S : IntegerGraphSupport d ell,
        S.1 = T.1.erase j → F T = F S) :
    P = F := by
  classical
  funext T
  by_cases hjT : j ∈ T.1
  · by_cases hSingleton : T.1 = {j}
    · exact (hPOne T hSingleton).trans
        (hFOne T hSingleton).symm
    · have hSNonempty : (T.1.erase j).Nonempty := by
        by_contra hEmpty
        have hSEmpty : T.1.erase j = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hEmpty
        have hSub : T.1 ⊆ {j} := by
          intro x hx
          by_cases hxj : x = j
          · simp [hxj]
          · have hxErase : x ∈ T.1.erase j :=
              Finset.mem_erase.mpr ⟨hxj, hx⟩
            simp [hSEmpty] at hxErase
        have hTEq : T.1 = {j} :=
          Finset.Subset.antisymm hSub
            (Finset.singleton_subset_iff.mpr hjT)
        exact hSingleton hTEq
      let S : IntegerGraphSupport d ell :=
        ⟨T.1.erase j,
          ⟨hSNonempty,
            (Finset.card_le_card (Finset.erase_subset j T.1)).trans
              T.2.2⟩⟩
      have hjS : j ∉ S.1 := by
        simp [S]
      have hST : S.1 ⊆ T.1 :=
        Finset.erase_subset j T.1
      have hMono : P S ≤ P T :=
        integerGraphAge_monotone d ell P hPAge S T hST
      have hLegalT : F T = F S :=
        hLegal T hjT S rfl
      have hSurv : P S = F S :=
        hSurvivors S hjS
      apply Nat.le_antisymm (hPLe T)
      calc
        F T = F S := hLegalT
        _ = P S := hSurv.symm
        _ ≤ P T := hMono
  · exact hSurvivors T hjT

end Kk
