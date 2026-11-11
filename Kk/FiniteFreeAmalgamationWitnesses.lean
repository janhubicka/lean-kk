import Kk.IsolatedBlockContinuationAge
import Mathlib.Tactic

/-!
# Finite K_ell-free free amalgamation of arbitrarily many witness extensions

The English proof and hostile review were committed BEFORE this file at
docs/finite_free_amalgamation_witness_families_english_audit.md.

These results use the ACTUAL directed Boolean L-clique predicate and the
existing exact finite forbidden-clique checker. Given extensions P∪W_i of
one fixed old graph P, the cross-nonedge condition makes their free union
K_ell-free. The one-direction cross-zero hypothesis suffices because
directed cliques check every ordered pair. No pairwise-disjointness is
silently imposed: the theorem is valid without it.

This supplies the finite relative gluing mechanism but does NOT assert that
each desired typed/Kpt continuation witness exists in the first place, or
that any amalgam preserves the full auxiliary parameter-closed B3 source.
-/

namespace Kk

/-- Two-component finite free amalgamation over arbitrary P. If neither
P∪Q nor P∪R contains an ell-clique, then P∪Q∪R does not either,
provided every distinct q∈Q and r∈R is missing the forward L atom.
No artificial disjointness or graph-symmetry assumption is used. -/
theorem finitePoolCliqueCheck_freeAmalgam_two
    (E : Nat → Nat → Bool) (ell : Nat)
    (P Q R : Finset Nat)
    (hCross : ∀ q ∈ Q, ∀ r ∈ R, q ≠ r → E q r = false)
    (hPQ : finitePoolCliqueCheck E ell (P ∪ Q) = false)
    (hPR : finitePoolCliqueCheck E ell (P ∪ R) = false) :
    finitePoolCliqueCheck E ell ((P ∪ Q) ∪ R) = false := by
  classical
  apply (finitePoolCliqueCheck_false_iff E ell ((P ∪ Q) ∪ R)).2
  rintro ⟨s, hsSub, hsCard, hsClique⟩
  by_cases hS_PQ : s ⊆ P ∪ Q
  · exact ((finitePoolCliqueCheck_false_iff E ell (P ∪ Q)).1 hPQ)
      ⟨s, hS_PQ, hsCard, hsClique⟩
  · obtain ⟨r, hrS, hrNotPQ⟩ := Finset.not_subset.mp hS_PQ
    have hrR : r ∈ R := by
      rcases Finset.mem_union.mp (hsSub hrS) with h | hR
      · exact False.elim (hrNotPQ h)
      · exact hR
    have hsPR : s ⊆ P ∪ R := by
      intro x hx
      rcases Finset.mem_union.mp (hsSub hx) with hxPQ | hxR
      · rcases Finset.mem_union.mp hxPQ with hxP | hxQ
        · exact Finset.mem_union.mpr (Or.inl hxP)
        · have hxr : x ≠ r := by
            intro heq
            exact hrNotPQ (heq ▸ Finset.mem_union.mpr (Or.inr hxQ))
          have hEdge := hsClique x hx r hrS hxr
          rw [hCross x hxQ r hrR hxr] at hEdge
          cases hEdge
      · exact Finset.mem_union.mpr (Or.inr hxR)
    exact ((finitePoolCliqueCheck_false_iff E ell (P ∪ R)).1 hPR)
      ⟨s, hsPR, hsCard, hsClique⟩

/-- Heredity of the exact finite no-clique checker, with no global
symmetry assumption and including the ell=0 boundary. -/
theorem finitePoolCliqueCheck_freeAmalgam_subset_false
    (E : Nat → Nat → Bool) (ell : Nat)
    (S T : Finset Nat) (hST : S ⊆ T)
    (hT : finitePoolCliqueCheck E ell T = false) :
    finitePoolCliqueCheck E ell S = false := by
  apply (finitePoolCliqueCheck_false_iff E ell S).2
  rintro ⟨s, hsS, hsCard, hsClique⟩
  exact ((finitePoolCliqueCheck_false_iff E ell T).1 hT)
    ⟨s, hsS.trans hST, hsCard, hsClique⟩

/-- Exact K_ell-free iff for a free amalgam of two individually
K_ell-free extensions over the same base, with only the displayed
one-orientation cross nonedges. -/
theorem finitePoolCliqueCheck_freeAmalgam_two_iff
    (E : Nat → Nat → Bool) (ell : Nat)
    (P Q R : Finset Nat)
    (hCross : ∀ q ∈ Q, ∀ r ∈ R, q ≠ r → E q r = false) :
    finitePoolCliqueCheck E ell ((P ∪ Q) ∪ R) = false ↔
      finitePoolCliqueCheck E ell (P ∪ Q) = false ∧
        finitePoolCliqueCheck E ell (P ∪ R) = false := by
  constructor
  · intro hFull
    refine ⟨finitePoolCliqueCheck_freeAmalgam_subset_false E ell _ _
      (Finset.subset_union_left) hFull, ?_⟩
    apply finitePoolCliqueCheck_freeAmalgam_subset_false
      E ell (P ∪ R) ((P ∪ Q) ∪ R)
    · intro x hx
      rcases Finset.mem_union.mp hx with hxP | hxR
      · exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_union.mpr (Or.inl hxP)))
      · exact Finset.mem_union.mpr (Or.inr hxR)
    · exact hFull
  · rintro ⟨hPQ, hPR⟩
    exact finitePoolCliqueCheck_freeAmalgam_two E ell P Q R hCross hPQ hPR

/-- Entire FINITE family of individually admissible extensions P∪W_i
over the same finite base P is K_ell-free when distinct fresh components
have no cross L atoms. The base hypothesis is necessary for I=∅.
No unsupported claim about existence of compatible individual W_i. -/
theorem finitePoolCliqueCheck_freeAmalgam_family
    {ι : Type*} [DecidableEq ι]
    (E : Nat → Nat → Bool) (ell : Nat)
    (P : Finset Nat) (I : Finset ι) (W : ι → Finset Nat)
    (hBase : finitePoolCliqueCheck E ell P = false) :
    (∀ i ∈ I, finitePoolCliqueCheck E ell (P ∪ W i) = false) →
    (∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ∀ q ∈ W i, ∀ r ∈ W j, q ≠ r → E q r = false) →
    finitePoolCliqueCheck E ell (P ∪ I.biUnion W) = false := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      intro _ _
      simpa using hBase
  | @insert i I hi ih =>
      intro hEach hCross
      have hRest : finitePoolCliqueCheck E ell (P ∪ I.biUnion W) = false := by
        apply ih
        · intro j hj
          exact hEach j (Finset.mem_insert_of_mem hj)
        · intro j hj n hn hjn q hq r hr hqr
          exact hCross j (Finset.mem_insert_of_mem hj)
            n (Finset.mem_insert_of_mem hn) hjn q hq r hr hqr
      have hCurrent : finitePoolCliqueCheck E ell (P ∪ W i) = false :=
        hEach i (Finset.mem_insert_self i I)
      have hCrossRest :
          ∀ q ∈ I.biUnion W, ∀ r ∈ W i, q ≠ r → E q r = false := by
        intro q hq r hr hqr
        obtain ⟨j,hj,hqj⟩ := Finset.mem_biUnion.mp hq
        have hji : j ≠ i := by
          intro hEq
          exact hi (hEq ▸ hj)
        exact hCross j (Finset.mem_insert_of_mem hj)
          i (Finset.mem_insert_self i I) hji q hqj r hr hqr
      have hGlued := finitePoolCliqueCheck_freeAmalgam_two
        E ell P (I.biUnion W) (W i) hCrossRest hRest hCurrent
      simpa only [Finset.biUnion_insert, Finset.union_assoc,
        Finset.union_comm, Finset.union_left_comm] using hGlued

#print axioms Kk.finitePoolCliqueCheck_freeAmalgam_two
#print axioms Kk.finitePoolCliqueCheck_freeAmalgam_subset_false
#print axioms Kk.finitePoolCliqueCheck_freeAmalgam_two_iff
#print axioms Kk.finitePoolCliqueCheck_freeAmalgam_family

end Kk
