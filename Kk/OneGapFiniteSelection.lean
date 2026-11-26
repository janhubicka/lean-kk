import Kk.OneGapCompression
import Mathlib.Data.Finset.Sort

/-!
# Finite selections for exact one-gap compression

Construct a strictly increasing infinite extension of each finite
strictly increasing selection. The extension is canonical and the
retained code is independent of the choice of tail. No infinite
extension hypothesis is needed by the finite-code theorem.

English proof: `docs/one_gap_finite_selection_english_audit_20261126.md`.
-/

namespace Kk
open SuccessorTree.V10

def oneGapFiniteSelectionExtend {n : Nat} (f : Fin n → Nat) (k : Nat) : Nat :=
  if hk : k < n then f ⟨k,hk⟩ else Finset.univ.sup f + 1 + (k-n)

@[simp] theorem oneGapFiniteSelectionExtend_apply {n : Nat}
    (f : Fin n → Nat) (i : Fin n) :
    oneGapFiniteSelectionExtend f i.val = f i := by
  simp [oneGapFiniteSelectionExtend,i.isLt]

theorem oneGapFiniteSelectionExtend_tail {n : Nat}
    (f : Fin n → Nat) (k : Nat) (hk : n ≤ k) :
    oneGapFiniteSelectionExtend f k = Finset.univ.sup f + 1 + (k-n) := by
  simp [oneGapFiniteSelectionExtend, Nat.not_lt.mpr hk]

/-- The first tail value lies above every selected vertex, including
when the selected finite domain is empty. -/
theorem oneGapFiniteSelectionExtend_strictMono {n : Nat}
    (f : Fin n → Nat) (hf : StrictMono f) :
    StrictMono (oneGapFiniteSelectionExtend f) := by
  intro a b hab
  by_cases ha : a < n
  · by_cases hb : b < n
    · simp only [oneGapFiniteSelectionExtend,dite_eq_left ha,dite_eq_left hb]
      exact hf (show (⟨a,ha⟩ : Fin n) < ⟨b,hb⟩ from hab)
    · have hMax : f ⟨a,ha⟩ ≤ Finset.univ.sup f :=
        Finset.le_sup (f := f) (Finset.mem_univ _)
      simp only [oneGapFiniteSelectionExtend,dite_eq_left ha,dite_eq_right hb]
      omega
  · have hb : ¬ b < n := by omega
    simp only [oneGapFiniteSelectionExtend,dite_eq_right ha,dite_eq_right hb]
    omega

theorem oneGapFiniteSelection_exists_extension {n : Nat}
    (f : Fin n → Nat) (hf : StrictMono f) :
    ∃ F : Nat → Nat, StrictMono F ∧ ∀ i : Fin n, F i.val = f i :=
  ⟨oneGapFiniteSelectionExtend f,oneGapFiniteSelectionExtend_strictMono f hf,
    oneGapFiniteSelectionExtend_apply f⟩

def oneGapFiniteRetainedCode (G : Nat → Nat → Bool) {n : Nat}
    (f : Fin n → Nat) : FinitePartialCode 1 0 1 :=
  oneGapRetainedCode G (oneGapFiniteSelectionExtend f) n

/-- The complete finite retained code depends only on the finite
selection, not on how a strictly increasing extension continues. -/
theorem oneGapFiniteRetainedCode_extension_independent
    (G : Nat → Nat → Bool) {n : Nat} (f : Fin n → Nat)
    (hf : StrictMono f) (F : Nat → Nat) (hF : StrictMono F)
    (hExt : ∀ i : Fin n, F i.val = f i) :
    oneGapRetainedCode G F n = oneGapFiniteRetainedCode G f := by
  apply oneGapRetainedCode_eq_of_finite_graph G G F (oneGapFiniteSelectionExtend f)
    hF (oneGapFiniteSelectionExtend_strictMono f hf) n
  intro i hi j hj
  have hFi := hExt ⟨i,hi⟩
  have hFj := hExt ⟨j,hj⟩
  have hEi := oneGapFiniteSelectionExtend_apply f ⟨i,hi⟩
  have hEj := oneGapFiniteSelectionExtend_apply f ⟨j,hj⟩
  change F i = f ⟨i,hi⟩ at hFi
  change F j = f ⟨j,hj⟩ at hFj
  change oneGapFiniteSelectionExtend f i = f ⟨i,hi⟩ at hEi
  change oneGapFiniteSelectionExtend f j = f ⟨j,hj⟩ at hEj
  rw [hFi,hFj,hEi,hEj]

/-- Finite ordinary-table equality gives exact equality of the full
retained L+ table. Both selections and all hypotheses are finite. -/
theorem oneGapFiniteRetainedCode_eq_of_graph
    (G H : Nat → Nat → Bool) {n : Nat} (f g : Fin n → Nat)
    (hf : StrictMono f) (hg : StrictMono g)
    (hGraph : ∀ i j : Fin n, G (f i) (f j) = H (g i) (g j)) :
    oneGapFiniteRetainedCode G f = oneGapFiniteRetainedCode H g := by
  apply oneGapRetainedCode_eq_of_finite_graph G H
    (oneGapFiniteSelectionExtend f) (oneGapFiniteSelectionExtend g)
    (oneGapFiniteSelectionExtend_strictMono f hf)
    (oneGapFiniteSelectionExtend_strictMono g hg) n
  intro i hi j hj
  have h := hGraph ⟨i,hi⟩ ⟨j,hj⟩
  simpa only [← oneGapFiniteSelectionExtend_apply f ⟨i,hi⟩,
    ← oneGapFiniteSelectionExtend_apply f ⟨j,hj⟩,
    ← oneGapFiniteSelectionExtend_apply g ⟨i,hi⟩,
    ← oneGapFiniteSelectionExtend_apply g ⟨j,hj⟩] using h

/-- Sort an arbitrary finite retained set and append the explicit
increasing linear tail. -/
def oneGapFinsetSelectionExtend (S : Finset Nat) : Nat → Nat :=
  oneGapFiniteSelectionExtend (S.orderEmbOfFin rfl)

theorem oneGapFinsetSelectionExtend_strictMono (S : Finset Nat) :
    StrictMono (oneGapFinsetSelectionExtend S) :=
  oneGapFiniteSelectionExtend_strictMono _ (S.orderEmbOfFin rfl).strictMono

/-- The initial finite range is exactly the requested set. -/
theorem oneGapFinsetSelectionExtend_prefix (S : Finset Nat) (v : Nat) :
    (∃ k, k < S.card ∧ oneGapFinsetSelectionExtend S k = v) ↔ v ∈ S := by
  constructor
  · rintro ⟨k,hk,hv⟩
    have hEq := oneGapFiniteSelectionExtend_apply (S.orderEmbOfFin rfl) ⟨k,hk⟩
    change oneGapFinsetSelectionExtend S k = S.orderEmbOfFin rfl ⟨k,hk⟩ at hEq
    rw [← hv,hEq]
    exact S.orderEmbOfFin_mem rfl ⟨k,hk⟩
  · intro hv
    have hRange : v ∈ Set.range (S.orderEmbOfFin rfl) := by
      rw [S.range_orderEmbOfFin rfl]
      exact hv
    obtain ⟨i,hi⟩ := hRange
    refine ⟨i.val,i.isLt,?_⟩
    exact (oneGapFiniteSelectionExtend_apply (S.orderEmbOfFin rfl) i).trans hi

end Kk
