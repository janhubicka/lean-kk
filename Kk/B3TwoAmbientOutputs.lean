import Kk.B3TwoGapCrossing
import SuccessorTree.V10.I3AmbientPrescribedPool
import SuccessorTree.V10.M2BoundaryPrescribedB2
import Mathlib.Tactic

/-!
# Genuine Kpt gap boundaries with two outputs in one ambient socle

The actual K4 first-clique-gadget obstruction uses two COMPLETE
future L-types, one auxiliary q2 and one selected x. The generic
two-boundary result in B3TwoGapCrossing requires their deleted
boundary SOURCE records to have the same ordinary L+ socle.

This file discharges that compatibility from a much simpler and
geometrically intrinsic hypothesis: each complete boundary OUTPUT
is the (cut+1)-type of one original in the SAME actual finite L+
partial structure A. All old ordinary coordinates then coincide.
The proof uses the genuine M2 boundary B1 equation to recover its
full source type by restriction of its output; no equality of
selected source sets, guessed E-expansion of age witnesses or
unproved parameter-spectrum domination is introduced.

Consequently every one-gap Kpt map with two such actual boundary
outputs must pass corrected finite B3 for arbitrary continuations
whose upper vertices realize either complete L-reduct type.
This is the necessary interface for the K4 q2,x,x continuation.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- An actual first-gap ShapeMap boundary with two outputs realized
by original types from the same enumerated L+ structure satisfies
the FULL finite L-only B3 age test for their two complete upper
L-reduct types, with arbitrary future-future edges.

The only source-compatibility fact comes from the *actual* M2 B1
predecessor equation plus the equal ordinary socles of types
extracted from the SAME A. The output equalities are raw
dependent Kpt-record equalities, not merely graph incidences. -/
theorem genuine_gap_two_ambient_targets_B3
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (a₁ : AdmissibleKptNode family)
    (ha₁ : LevelTree.lev a₁ = LevelTree.lev a₀)
    (A : EnumeratedPartialStructure db du dd)
    (v₀ v₁ : Nat)
    (hOutput₀ :
      (F a₀).val =
        (⟨(LevelTree.lev (F a₀)-1)+1,
          A.partialTypeAt ((LevelTree.lev (F a₀)-1)+1) v₀⟩ :
          RawPartialTypeNode db du dd))
    (hOutput₁ :
      (F a₁).val =
        (⟨(LevelTree.lev (F a₀)-1)+1,
          A.partialTypeAt ((LevelTree.lev (F a₀)-1)+1) v₁⟩ :
          RawPartialTypeNode db du dd)) :
    CommonSocleAgeTest family
      (prescribedOrdinarySocle
        (A.partialTypeAt ((LevelTree.lev (F a₀)-1)+1) v₀))
      (LevelTree.lev (F a₀)-1)
      (fun R =>
        R = (A.partialTypeAt
          ((LevelTree.lev (F a₀)-1)+1) v₀).lReduct ∨
        R = (A.partialTypeAt
          ((LevelTree.lev (F a₀)-1)+1) v₁).lReduct) := by
  let m : Nat := LevelTree.lev (F a₀)-1
  let i₀ : M2BoundaryIndex family a₀ := ⟨a₀,rfl⟩
  let i₁ : M2BoundaryIndex family a₀ := ⟨a₁,ha₁⟩
  let T₀ := m2Boundary_targetType family F q₀ a₀ hprev hgap i₀
  let T₁ := m2Boundary_targetType family F q₀ a₀ hprev hgap i₁
  let S₀ := m2Boundary_sourceType family F q₀ a₀ hprev hgap i₀
  let S₁ := m2Boundary_sourceType family F q₀ a₀ hprev hgap i₁
  have hType₀ : T₀ = A.partialTypeAt (m+1) v₀ := by
    have hRaw := m2Boundary_target_raw family F q₀ a₀ hprev hgap i₀
    have hPair :
        (⟨m+1,T₀⟩ : RawPartialTypeNode db du dd) =
        (⟨m+1,A.partialTypeAt (m+1) v₀⟩ :
          RawPartialTypeNode db du dd) :=
      hRaw.symm.trans hOutput₀
    exact eq_of_heq (Sigma.mk.inj_iff.mp hPair).2
  have hType₁ : T₁ = A.partialTypeAt (m+1) v₁ := by
    have hRaw := m2Boundary_target_raw family F q₀ a₀ hprev hgap i₁
    have hPair :
        (⟨m+1,T₁⟩ : RawPartialTypeNode db du dd) =
        (⟨m+1,A.partialTypeAt (m+1) v₁⟩ :
          RawPartialTypeNode db du dd) :=
      hRaw.symm.trans hOutput₁
    exact eq_of_heq (Sigma.mk.inj_iff.mp hPair).2
  have hSource₀ : S₀ = A.partialTypeAt m v₀ := by
    calc
      S₀ = T₀.restrict (Nat.le_succ m) :=
        (m2Boundary_B1 family F q₀ a₀ hprev hgap i₀).symm
      _ = (A.partialTypeAt (m+1) v₀).restrict (Nat.le_succ m) := by
        rw [hType₀]
      _ = A.partialTypeAt m v₀ :=
        A.partialTypeAt_restrict m (m+1) v₀ (Nat.le_succ m)
  have hSource₁ : S₁ = A.partialTypeAt m v₁ := by
    calc
      S₁ = T₁.restrict (Nat.le_succ m) :=
        (m2Boundary_B1 family F q₀ a₀ hprev hgap i₁).symm
      _ = (A.partialTypeAt (m+1) v₁).restrict (Nat.le_succ m) := by
        rw [hType₁]
      _ = A.partialTypeAt m v₁ :=
        A.partialTypeAt_restrict m (m+1) v₁ (Nat.le_succ m)
  have hCompatible : SameOrdinaryAtCut S₁ S₀ := by
    rw [hSource₁,hSource₀]
    exact sameOrdinaryAtCut_sameAmbient A m v₁ v₀
  have hB3 :=
    genuine_gap_boundary_two_targets_B3
      family F q₀ a₀ hprev hgap a₁ ha₁ hCompatible
  change CommonSocleAgeTest family (prescribedOrdinarySocle T₀) m
    (fun R => R = T₀.lReduct ∨ R = T₁.lReduct) at hB3
  rw [hType₀, hType₁] at hB3
  exact hB3

/-- The contrapositive is the form useful in the first-gadget
adversarial audit. It is impossible to have a genuine first-gap
ShapeMap with two ambient-type outputs and a finite forbidden
continuation over those two complete L-types. -/
theorem bad_two_ambient_targets_contradicts_genuine_gap
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (a₁ : AdmissibleKptNode family)
    (ha₁ : LevelTree.lev a₁ = LevelTree.lev a₀)
    (A : EnumeratedPartialStructure db du dd)
    (v₀ v₁ : Nat)
    (hOutput₀ :
      (F a₀).val =
        (⟨(LevelTree.lev (F a₀)-1)+1,
          A.partialTypeAt ((LevelTree.lev (F a₀)-1)+1) v₀⟩ :
          RawPartialTypeNode db du dd))
    (hOutput₁ :
      (F a₁).val =
        (⟨(LevelTree.lev (F a₀)-1)+1,
          A.partialTypeAt ((LevelTree.lev (F a₀)-1)+1) v₁⟩ :
          RawPartialTypeNode db du dd))
    (hBad : ¬ CommonSocleAgeTest family
      (prescribedOrdinarySocle
        (A.partialTypeAt ((LevelTree.lev (F a₀)-1)+1) v₀))
      (LevelTree.lev (F a₀)-1)
      (fun R =>
        R = (A.partialTypeAt
          ((LevelTree.lev (F a₀)-1)+1) v₀).lReduct ∨
        R = (A.partialTypeAt
          ((LevelTree.lev (F a₀)-1)+1) v₁).lReduct)) :
    False :=
  hBad (genuine_gap_two_ambient_targets_B3
    family F q₀ a₀ hprev hgap a₁ ha₁ A v₀ v₁ hOutput₀ hOutput₁)

end Kk
