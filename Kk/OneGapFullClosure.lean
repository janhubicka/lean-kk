import Kk.OneGapFullB3
import Kk.TrackDResolvedQBaseRoles
import SuccessorTree.V10.KptStageClosureNormalForm
import SuccessorTree.V10.I3ClosureSelectedCrossing
import Mathlib.Tactic

/-!
# Full retained-pool geometry

Whole-block retention and chronological convexity are distinct.
Convexity rules out a retained block straddling an omitted meaningful
coordinate. All later nonselected retained originals must have zero
old columns at such a cut. This is stronger than a selected-front
fork test, and uses no numerical generation case analysis.
-/
namespace Kk
open SuccessorTree
open SuccessorTree.V10

def OneGapBlockConvex (role : Nat → ResolvedQBaseRole) : Prop :=
  ∀ a b c block : Nat, a < b → b < c →
    role a = .auxiliary block true →
    role c = .auxiliary block true →
    role b = .auxiliary block true

theorem oneGap_later_retained_aux_old_zero
    (role : Nat → ResolvedQBaseRole) (G : Nat → Nat → Bool)
    (hDummy : ∀ i j, role i = .dummy → G i j = false)
    (hCodedAux : ∀ i j (s : Bool) (block : Nat) (keep : Bool),
      i < j → role i = .coded s →
      role j = .auxiliary block keep → G i j = false)
    (hAuxDifferent : ∀ i j (p q : Nat) (a b : Bool),
      p ≠ q → role i = .auxiliary p a →
      role j = .auxiliary q b → G i j = false)
    (hBlockFlag : ∀ i j (block : Nat) (a b : Bool),
      role i = .auxiliary block a →
      role j = .auxiliary block b → a = b)
    (hConvex : OneGapBlockConvex role)
    (i cut j block : Nat) (hi : i < cut) (hj : cut < j)
    (hOmitted : ¬ ResolvedQRetainedBase (role cut))
    (hJ : role j = .auxiliary block true) :
    G i j = false := by
  cases hI : role i with
  | dummy => exact hDummy i j hI
  | coded s => exact hCodedAux i j s block true (by omega) hI hJ
  | auxiliary p keep =>
    by_cases hSame : p = block
    · subst p
      have hFlag := hBlockFlag i j block keep true hI hJ
      subst keep
      exact False.elim (hOmitted
        (Or.inr (Or.inr ⟨block,hConvex i cut j block hi hj hI hJ⟩)))
    · exact hAuxDifferent i j p block keep true hSame hI hJ

/-- All retained original names, including the cap, not only the
selected terminals. If the selected front does not split, a positive
old neighbour distinguishes it from every negative auxiliary name. -/
theorem oneGap_full_pool_column_fibre
    (G : Nat → Nat → Bool) (cut : Nat)
    (pool selected : Nat → Prop)
    (hPositive : ∀ v, pool v → cut < v → G cut v = true → selected v)
    (hSelectedFork : ∀ v w, selected v → selected w →
      cut < v → cut < w →
      (∀ p < cut, G p v = G p w) → G cut v = G cut w)
    (hOldNeighbour : ∀ v, pool v → cut < v → G cut v = true →
      ∃ p, p < cut ∧ G p v = true)
    (hOtherZero : ∀ v, pool v → ¬ selected v → cut < v →
      ∀ p < cut, G p v = false)
    (v w : Nat) (hv : pool v) (hw : pool w)
    (hvc : cut < v) (hwc : cut < w)
    (hSame : ∀ p < cut, G p v = G p w) :
    G cut v = G cut w := by
  have hDirection : ∀ v w, pool v → pool w →
      cut < v → cut < w →
      (∀ p < cut, G p v = G p w) →
      G cut v = true → G cut w = true := by
    intro v w hv hw hvc hwc hSame hPos
    have hSV := hPositive v hv hvc hPos
    by_cases hSW : selected w
    · exact (hSelectedFork v w hSV hSW hvc hwc hSame).symm.trans hPos
    · obtain ⟨p,hp,hEdge⟩ := hOldNeighbour v hv hvc hPos
      have hZero := hOtherZero w hw hSW hwc p hp
      have hEq := hSame p hp
      rw [hEdge,hZero] at hEq
      contradiction
  cases hV : G cut v <;> cases hW : G cut w
  · rfl
  · have h := hDirection w v hw hv hwc hvc (fun p hp => (hSame p hp).symm) hW
    simp [hV] at h
  · have h := hDirection v w hv hw hvc hwc hSame hV
    simp [hW] at h
  · rfl

theorem oneGap_fullType_eq_of_column
    (A : EnumeratedPartialStructure 1 0 1)
    (cut v w : Nat)
    (hv : cut ≤ A.freeLevel v) (hw : cut ≤ A.freeLevel w)
    (hSym : ∀ x y, A.L.binary x y (0 : Fin 1) = A.L.binary y x (0 : Fin 1))
    (hLoop : ∀ x, A.L.binary x x (0 : Fin 1) = false)
    (hDiag : ∀ x, A.L.diagonal x (0 : Fin 1) = false)
    (hCol : ∀ p < cut, A.L.binary p v 0 = A.L.binary p w 0) :
    A.partialTypeAt cut v = A.partialTypeAt cut w := by
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro x y t
      fin_cases t
      cases x with
      | none =>
        cases y with
        | none =>
          change A.L.binary v v 0 = A.L.binary w w 0
          rw [hLoop v,hLoop w]
        | some p =>
          change A.L.binary v p.val 0 = A.L.binary w p.val 0
          rw [hSym v p.val,hSym w p.val]
          exact hCol p.val p.isLt
      | some p =>
        cases y with
        | none => exact hCol p.val p.isLt
        | some q => rfl
    · intro x t
      exact Fin.elim0 t
    · intro x t
      fin_cases t
      cases x with
      | none =>
        change A.L.diagonal v 0 = A.L.diagonal w 0
        rw [hDiag v,hDiag w]
      | some p => rfl
  · intro x y
    cases x with
    | none =>
      cases y with
      | none =>
        rw [A.partialTypeAt_no_typeE_loop cut v,A.partialTypeAt_no_typeE_loop cut w]
      | some p =>
        rw [A.partialTypeAt_no_reverseE cut v hv p,
          A.partialTypeAt_no_reverseE cut w hw p]
    | some p =>
      cases y with
      | none =>
        rw [A.partialTypeAt_fullESocle cut v hv p,
          A.partialTypeAt_fullESocle cut w hw p]
      | some q => rfl

/-- Ordinary no-fork on the complete retained pool gives equality
of complete dependent next types, including the auxiliary columns. -/
theorem oneGap_full_nextType_eq_of_no_column_fork
    (A : EnumeratedPartialStructure 1 0 1) (cut v w : Nat)
    (hv : cut+1 ≤ A.freeLevel v) (hw : cut+1 ≤ A.freeLevel w)
    (hSym : ∀ x y, A.L.binary x y (0 : Fin 1) = A.L.binary y x (0 : Fin 1))
    (hLoop : ∀ x, A.L.binary x x (0 : Fin 1) = false)
    (hDiag : ∀ x, A.L.diagonal x (0 : Fin 1) = false)
    (hFibre : (∀ p < cut, A.L.binary p v 0 = A.L.binary p w 0) →
      A.L.binary cut v 0 = A.L.binary cut w 0)
    (hOld : A.partialTypeAt cut v = A.partialTypeAt cut w) :
    A.partialTypeAt (cut+1) v = A.partialTypeAt (cut+1) w := by
  have hCol : ∀ p < cut, A.L.binary p v 0 = A.L.binary p w 0 := by
    intro p hp
    exact congrArg (fun T : PartialTypeWithE cut 1 0 1 =>
      T.lReduct.binary (some (⟨p,hp⟩ : Fin cut)) none 0) hOld
  apply oneGap_fullType_eq_of_column A (cut+1) v w hv hw hSym hLoop hDiag
  intro p hp
  by_cases h : p = cut
  · subst p
    exact hFibre hCol
  · exact hCol p (by omega)

theorem oneGap_planned_pool_covers_closure
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (I : Set Nat) (X : Set (AdmissibleKptNode family))
    (U V : Set (Fin A.size))
    (hX : X ⊆ ambientPrefixPool family A hAvoid U)
    (hUV : U ⊆ V)
    (hRet : ∀ i : Fin A.size, i.val ∈ I → 0 < A.freeLevel i.val → i ∈ V) :
    SMTree.Envelope.closure (admissibleKptSTree family) I X ⊆
      ambientPrefixPool family A hAvoid V := by
  have hNF := admissibleKpt_stage_closure_normalForm
    family A hAvoid I X U V hX hUV hRet
  exact hNF.trans (kptStageClosureNormalForm_subset_pool
    family A hAvoid I X U V hX hUV hRet)

/-- Seed and parameter end-level checks plus no pool meet give full
I1 by the exact three-way closure normal form. -/
theorem oneGap_planned_closure_no_endpoint
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (I : Set Nat) (X : Set (AdmissibleKptNode family))
    (U V : Set (Fin A.size))
    (hX : X ⊆ ambientPrefixPool family A hAvoid U)
    (hUV : U ⊆ V)
    (hRet : ∀ i : Fin A.size, i.val ∈ I → 0 < A.freeLevel i.val → i ∈ V)
    (cut : Nat)
    (hSeed : ∀ z ∈ X, LevelTree.lev z ≠ cut)
    (hEnd : ∀ v ∈ V, A.freeLevel v.val ≠ cut)
    (hMeet : ∀ v ∈ V, ∀ w ∈ V,
      SMTree.Envelope.SameComponent
        (A.kptOriginal family hAvoid v) (A.kptOriginal family hAvoid w) →
      LevelTree.lev (LevelTree.meet
        (A.kptOriginal family hAvoid v) (A.kptOriginal family hAvoid w)) ≠ cut) :
    ¬ ∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure (admissibleKptSTree family) I X ∧
      LevelTree.lev z = cut := by
  rintro ⟨z,hz,hlev⟩
  have hNormal := admissibleKpt_stage_closure_normalForm
    family A hAvoid I X U V hX hUV hRet hz
  rcases hNormal with hS | hP | hM
  · exact hSeed z hS hlev
  · obtain ⟨v,hI,hPositive,rfl⟩ := hP
    exact hEnd v (hRet v hI hPositive) hlev
  · obtain ⟨v,hv,w,hw,hCommon,rfl⟩ := hM
    exact hMeet v hv w hw hCommon hlev

end Kk
