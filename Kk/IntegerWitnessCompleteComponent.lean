import Kk.IntegerWitnessCanonical
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# One explicit complete typed finite clique for every normalized integer witness

English proof and hostile audit were committed BEFORE this source in
docs/universal_typed_witness_gadget_english_audit.md.

An actual normalized IntegerCliqueWeights vector w determines the finite
Sigma-type of vertices (sort j, index < w_j), with EXACTLY w_j vertices
of each sort. The complete loop-free symmetric Boolean graph on this
type is K_ell-free for ell>0 and has exact sort-support multiplicities.

The height condition ell>0 is necessary: at d=ell=0 the library's
truncated-Nat bound permits a phantom empty vector, so the strict
cardinality bound would otherwise be false. This statement is for ONE
L-only witness component, not the full multi-support reserved gadget,
physical numerical-H generations, or full Kpt E/parameter closure.
-/

namespace Kk

/-- Explicitly distinct vertices of a normalized typed clique witness:
a choice of sort j and one of w_j slots. -/
abbrev IntegerWitnessVertex {d ell : Nat} (w : IntegerCliqueWeights d ell) :=
  Σ j : Fin d, Fin ((w.1 j).val)

theorem integerWitnessVertex_total {d ell : Nat}
    (w : IntegerCliqueWeights d ell) :
    Fintype.card (IntegerWitnessVertex w) =
      ∑ j : Fin d, (w.1 j).val := by
  classical
  simp [IntegerWitnessVertex, Fintype.card_sigma]

theorem integerWitnessVertex_card_lt {d ell : Nat}
    (w : IntegerCliqueWeights d ell) (hell : 0 < ell) :
    Fintype.card (IntegerWitnessVertex w) < ell := by
  rw [integerWitnessVertex_total]
  have hw : (∑ j : Fin d, (w.1 j).val) ≤ ell - 1 := w.2
  omega

/-- The dependent fiber of exact sort j is equivalent to Fin(w_j). -/
def integerWitnessVertex_fiberEquiv {d ell : Nat}
    (w : IntegerCliqueWeights d ell) (j : Fin d) :
    {v : IntegerWitnessVertex w // v.1 = j} ≃ Fin ((w.1 j).val) where
  toFun x := by
    rcases x with ⟨⟨i,t⟩,hi⟩
    change i = j at hi
    subst i
    exact t
  invFun t := ⟨⟨j,t⟩, rfl⟩
  left_inv x := by
    rcases x with ⟨⟨i,t⟩,hi⟩
    change i = j at hi
    subst i
    rfl
  right_inv t := rfl

/-- Each complete witness component has w_j actual distinct vertices
of sort j, including multiplicities greater than one. -/
theorem integerWitnessVertex_fiber_card {d ell : Nat}
    (w : IntegerCliqueWeights d ell) (j : Fin d) :
    ((Finset.univ : Finset (IntegerWitnessVertex w)).filter
        (fun v => v.1 = j)).card = (w.1 j).val := by
  classical
  have hCard : Fintype.card {v : IntegerWitnessVertex w // v.1 = j} =
      (w.1 j).val := by
    rw [Fintype.card_congr (integerWitnessVertex_fiberEquiv w j)]
    exact Fintype.card_fin _
  simpa only [Fintype.card_subtype] using hCard

/-- Exact cardinality of vertices whose sorts lie in an arbitrary support. -/
theorem integerWitnessVertex_support_card {d ell : Nat}
    (w : IntegerCliqueWeights d ell) (T : Finset (Fin d)) :
    ((Finset.univ : Finset (IntegerWitnessVertex w)).filter
        (fun v => v.1 ∈ T)).card =
      ∑ j ∈ T, (w.1 j).val := by
  classical
  have hPartition := Finset.sum_card_fiberwise_eq_card_filter
    (s := (Finset.univ : Finset (IntegerWitnessVertex w))) T
    (fun v : IntegerWitnessVertex w => v.1)
  calc
    ((Finset.univ : Finset (IntegerWitnessVertex w)).filter
        (fun v => v.1 ∈ T)).card
      = ∑ j ∈ T, ((Finset.univ : Finset (IntegerWitnessVertex w)).filter
          (fun v => v.1 = j)).card := hPartition.symm
    _ = ∑ j ∈ T, (w.1 j).val := by
      apply Finset.sum_congr rfl
      intro j hj
      exact integerWitnessVertex_fiber_card w j

/-- The actual normalized integer-graph-age support value is precisely
the multiplicity of the selected sorts in this concrete component. -/
theorem integerWitnessVertex_support_eq_integerCliqueOnSupport {d ell : Nat}
    (w : IntegerCliqueWeights d ell)
    (T : IntegerGraphSupport d ell) :
    ((Finset.univ : Finset (IntegerWitnessVertex w)).filter
      (fun v => v.1 ∈ T.1)).card =
      integerCliqueOnSupport w T := by
  change _ = T.1.sum (fun j => (w.1 j).val)
  exact integerWitnessVertex_support_card w T.1

/-- Literal complete irreflexive symmetric Boolean L table on this
finite typed set; this is not the original Henson E-incidence. -/
def integerWitnessCompleteEdge {d ell : Nat}
    (w : IntegerCliqueWeights d ell)
    (x y : IntegerWitnessVertex w) : Bool := decide (x ≠ y)

theorem integerWitnessCompleteEdge_symm {d ell : Nat}
    (w : IntegerCliqueWeights d ell)
    (x y : IntegerWitnessVertex w) :
    integerWitnessCompleteEdge w x y = integerWitnessCompleteEdge w y x := by
  simp only [integerWitnessCompleteEdge, ne_comm]

theorem integerWitnessCompleteEdge_clique {d ell : Nat}
    (w : IntegerCliqueWeights d ell)
    (s : Finset (IntegerWitnessVertex w)) :
    ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
      integerWitnessCompleteEdge w x y = true := by
  classical
  intro x hx y hy hxy
  simp [integerWitnessCompleteEdge, hxy]

/-- No ell-clique occurs in a complete component of total weight <ell.
The ell>0 premise is essential at the d=ell=0 truncated-bound edge case. -/
theorem integerWitnessCompleteEdge_clique_small {d ell : Nat}
    (w : IntegerCliqueWeights d ell) (hell : 0 < ell)
    (s : Finset (IntegerWitnessVertex w)) : s.card < ell := by
  classical
  have hSubset : s ⊆ (Finset.univ : Finset (IntegerWitnessVertex w)) :=
    Finset.subset_univ s
  have hCard : s.card ≤ Fintype.card (IntegerWitnessVertex w) := by
    simpa only [Finset.card_univ] using Finset.card_le_card hSubset
  exact lt_of_le_of_lt hCard (integerWitnessVertex_card_lt w hell)

/-- Every complete finite witness component of a B-feasible normalized
vector satisfies all raw support bounds exactly as required. -/
theorem integerWitnessVertex_respects_raw_bound {d ell : Nat}
    (B : IntegerGraphSupport d ell → Nat)
    (w : IntegerCliqueWeights d ell)
    (hw : WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell)) B w)
    (T : IntegerGraphSupport d ell) :
    ((Finset.univ : Finset (IntegerWitnessVertex w)).filter
      (fun v => v.1 ∈ T.1)).card ≤ B T := by
  rw [integerWitnessVertex_support_eq_integerCliqueOnSupport]
  exact hw T

#print axioms Kk.integerWitnessVertex_total
#print axioms Kk.integerWitnessVertex_card_lt
#print axioms Kk.integerWitnessVertex_fiber_card
#print axioms Kk.integerWitnessVertex_support_card
#print axioms Kk.integerWitnessVertex_support_eq_integerCliqueOnSupport
#print axioms Kk.integerWitnessCompleteEdge_symm
#print axioms Kk.integerWitnessCompleteEdge_clique
#print axioms Kk.integerWitnessCompleteEdge_clique_small
#print axioms Kk.integerWitnessVertex_respects_raw_bound

end Kk
