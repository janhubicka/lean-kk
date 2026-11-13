import Kk.FiniteChronologicalHensonEmbedding
import Kk.FiniteInducedOnePointExtension
import Mathlib.Tactic

/-!
# Track A: finite chronological Henson embedding over a pinned old prefix

English proof and hostile audit were committed FIRST in
  docs/pinned_prefix_henson_extension_english_audit.md

The target complete ordinary-L table A already agrees with the fixed
Henson E on ALL old coordinates [0,b), not merely selected ones.
The whole target prefix is K_ell-free. We embed its finite extension
into the unchanged left-dense E with exact induced edges, identity on
all old indices, and negative edges to ALL unnamed intervening gaps.

This is a finite compatible relative realization theorem, not a proof
that an arbitrary abstract age-feasible clique is compatible with a
fixed past or that a global resolved H+ schedule exists.
-/

namespace Kk

/-- Any finite graph pattern that is genuinely K_ell-free **together
with the entire fixed old prefix**, and which agrees with E there,
has a strictly increasing induced embedding over the identity prefix.

For each new abstract index m>=b, its actual image has zero ordinary
L edges, in BOTH directions, to EVERY earlier ambient original not
an image of an even earlier abstract index. This explicitly records
the chronology gaps, rather than merely asserting an induced copy.

The left-dense property is on the fixed actual E enumeration; no
new enumeration, relabelling of E, or hidden relative age axiom. -/
theorem onePointLeftDense_embeds_finite_KFree_over_fixed_prefix
    (A E : Nat → Nat → Bool) (ell b N : Nat)
    (hell : 0 < ell) (hbN : b ≤ N)
    (hASym : ∀ i j, A i j = A j i)
    (hALoops : ∀ i, A i i = false)
    (hOldEq : ∀ i j, i < b → j < b → i ≠ j → A i j = E i j)
    (hDense : OnePointLeftDense E ell)
    (hEFree : ∀ front, ¬ HasCliqueBelow E front ell)
    (hAFree : ¬ HasCliqueBelow A N ell) :
    ∃ f : Nat → Nat,
      (∀ i, i < b → f i = i) ∧
      (∀ i j, i < N → j < N → i < j → f i < f j) ∧
      (∀ i j, i < N → j < N → i ≠ j →
        E (f i) (f j) = A i j) ∧
      (∀ m, b ≤ m → m < N → ∀ z, z < f m →
        z ∉ (Finset.range m).image f →
        E z (f m) = false ∧ E (f m) z = false) := by
  classical
  have construct (n : Nat) (hn : n ≤ N) :
      ∃ f : Nat → Nat,
        (∀ i, i < b → f i = i) ∧
        (∀ i j, i < n → j < n → i < j → f i < f j) ∧
        (∀ i j, i < n → j < n → i ≠ j →
          E (f i) (f j) = A i j) ∧
        (∀ m, b ≤ m → m < n → ∀ z, z < f m →
          z ∉ (Finset.range m).image f →
          E z (f m) = false ∧ E (f m) z = false) := by
    induction n with
    | zero =>
        refine ⟨id, ?_, ?_, ?_, ?_⟩
        · intro i _
          rfl
        · intro i j hi _
          omega
        · intro i j hi _
          omega
        · intro m _ hm
          omega
    | succ n ih =>
        by_cases hUnderBase : n < b
        · refine ⟨id, ?_, ?_, ?_, ?_⟩
          · intro i _
            rfl
          · intro i j hi hj hij
            exact hij
          · intro i j hi hj hij
            change E i j = A i j
            exact (hOldEq i j (by omega) (by omega) hij).symm
          · intro m hm hmn
            omega
        · have hnBase : b ≤ n := by omega
          obtain ⟨f,hFix,hMono,hGraph,hGap⟩ := ih (by omega)
          have hFreeSucc : ¬ HasCliqueBelow A (n+1) ell := by
            rintro ⟨s,hsCard,hsBelow,hsClique⟩
            apply hAFree
            exact ⟨s,hsCard,
              (by intro x hx; have := hsBelow x hx; omega), hsClique⟩
          let P : Finset Nat := Finset.range n
          let S : Finset Nat := P.filter (fun x => A x n = true)
          have hSP : S ⊆ P := Finset.filter_subset _ _
          have hSafe : finitePoolCliqueCheck A (ell-1) S = false := by
            apply (finitePoolCliqueCheck_false_iff A (ell-1) S).2
            rintro ⟨s,hsS,hsCard,hsClique⟩
            have hNbr : HasNeighbourCliqueBelow A n (ell-1)
                (fun x => A x n) := by
              refine ⟨s,hsCard,?_,hsClique⟩
              intro x hx
              have h := Finset.mem_filter.mp (hsS hx)
              exact ⟨Finset.mem_range.mp h.1,h.2⟩
            exact hFreeSucc
              ((hasCliqueBelow_succ_iff_old_or_neighbour
                A n ell hell hASym hALoops).2 (Or.inr hNbr))
          let front : Nat := (P.sup f) + 1
          have hBelow : ∀ x ∈ P, f x < front := by
            intro x hx
            have hLe : f x ≤ P.sup f := Finset.le_sup (f := f) hx
            exact Nat.lt_succ_of_le hLe
          have hInj : Set.InjOn f ↑P := by
            intro x hx y hy heq
            have hxN : x < n := Finset.mem_range.mp hx
            have hyN : y < n := Finset.mem_range.mp hy
            rcases lt_trichotomy x y with hxy | hEq | hyx
            · have hLt := hMono x y hxN hyN hxy
              omega
            · exact hEq
            · have hLt := hMono y x hyN hxN hyx
              omega
          have hOldAtoms :
              ∀ x ∈ P, ∀ y ∈ P, x ≠ y →
                A x y = E (f x) (f y) := by
            intro x hx y hy hxy
            exact (hGraph x y
              (Finset.mem_range.mp hx)
              (Finset.mem_range.mp hy) hxy).symm
          have hForward : ∀ x ∈ P,
              A x n = decide (x ∈ S) := by
            intro x hx
            by_cases hb : A x n = true
            · have hs : x ∈ S := Finset.mem_filter.mpr ⟨hx,hb⟩
              simp [hb,hs]
            · have hFalse : A x n = false := by
                cases hVal : A x n with
                | false => rfl
                | true => exact False.elim (hb hVal)
              have hs : x ∉ S := by
                intro hMem
                exact hb (Finset.mem_filter.mp hMem).2
              simp [hFalse,hs]
          have hBackward : ∀ x ∈ P, A n x = A x n := by
            intro x hx
            exact hASym n x
          obtain ⟨v,hFront,hColumn,hGaps⟩ :=
            onePointLeftDense_extend_finite_induced_copy
              A E ell front n hell hDense (hEFree front)
              P S hSP f hInj hBelow hOldAtoms
              hForward hBackward hSafe
          let f' : Nat → Nat := fun i => if i = n then v else f i
          have hImageEq : ∀ m, m ≤ n →
              (Finset.range m).image f' = (Finset.range m).image f := by
            intro m hm
            apply Finset.image_congr
            intro i hi
            have hine : i ≠ n := by
              have hilt : i < m := Finset.mem_range.mp hi
              omega
            simp [f',hine]
          refine ⟨f', ?_, ?_, ?_, ?_⟩
          · intro i hi
            have hine : i ≠ n := by omega
            change (if i = n then v else f i) = i
            rw [if_neg hine]
            exact hFix i hi
          · intro i j hi hj hij
            by_cases hjn : j = n
            · have hin : i < n := by omega
              have hine : i ≠ n := by omega
              change (if i = n then v else f i) <
                (if j = n then v else f j)
              rw [if_neg hine, if_pos hjn]
              exact lt_of_lt_of_le
                (hBelow i (Finset.mem_range.mpr hin)) hFront
            · have hin : i < n := by omega
              have hjnlt : j < n := by omega
              have hine : i ≠ n := by omega
              change (if i = n then v else f i) <
                (if j = n then v else f j)
              rw [if_neg hine, if_neg hjn]
              exact hMono i j hin hjnlt hij
          · intro i j hi hj hne
            by_cases hin : i = n
            · have hjn : j ≠ n := by omega
              have hjlt : j < n := by omega
              change E (if i = n then v else f i)
                (if j = n then v else f j) = A i j
              rw [if_pos hin, if_neg hjn, hin]
              exact (hColumn j (Finset.mem_range.mpr hjlt)).2
            · by_cases hjn : j = n
              · have hilt : i < n := by omega
                change E (if i = n then v else f i)
                  (if j = n then v else f j) = A i j
                rw [if_neg hin, if_pos hjn, hjn]
                exact (hColumn i (Finset.mem_range.mpr hilt)).1
              · have hilt : i < n := by omega
                have hjlt : j < n := by omega
                change E (if i = n then v else f i)
                  (if j = n then v else f j) = A i j
                rw [if_neg hin, if_neg hjn]
                exact hGraph i j hilt hjlt hne
          · intro m hm hmn z hz hOutside
            by_cases hmnEq : m = n
            · subst m
              have hzV : z < v := by
                simpa [f'] using hz
              have hOutsideOld : z ∉ P.image f := by
                change z ∉ (Finset.range n).image f
                rw [hImageEq n (le_refl _)] at hOutside
                exact hOutside
              have hZero := hGaps z hzV hOutsideOld
              simpa [f'] using hZero
            · have hmLt : m < n := by omega
              have hzOld : z < f m := by
                simpa [f',hmnEq] using hz
              have hOutsideOld : z ∉ (Finset.range m).image f := by
                rw [hImageEq m (by omega)] at hOutside
                exact hOutside
              have hZero := hGap m hm hmLt z hzOld hOutsideOld
              simpa [f',hmnEq] using hZero
  exact construct N (le_refl _)

/-- Same anchored finite extension inside the genuine normalized
Henson graph: forbidden-family avoidance supplies K_ell-freeness
of every actual old prefix, while OnePointLeftDense remains explicit. -/
theorem henson_leftDense_embeds_finite_over_fixed_prefix
    (ell b N : Nat) (hell : 2 ≤ ell) (hbN : b ≤ N)
    (A E : Nat → Nat → Bool)
    (hASym : ∀ i j, A i j = A j i)
    (hALoops : ∀ i, A i i = false)
    (hOldEq : ∀ i j, i < b → j < b → i ≠ j → A i j = E i j)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (hAFree : ¬ HasCliqueBelow A N ell) :
    ∃ f : Nat → Nat,
      (∀ i, i < b → f i = i) ∧
      (∀ i j, i < N → j < N → i < j → f i < f j) ∧
      (∀ i j, i < N → j < N → i ≠ j →
        E (f i) (f j) = A i j) ∧
      (∀ m, b ≤ m → m < N → ∀ z, z < f m →
        z ∉ (Finset.range m).image f →
        E z (f m) = false ∧ E (f m) z = false) := by
  exact onePointLeftDense_embeds_finite_KFree_over_fixed_prefix
    A E ell b N (by omega) hbN hASym hALoops hOldEq
    hDense (hensonForbiddenFamily_no_prefix_cliques ell hell E hAvoid)
    hAFree

#print axioms Kk.onePointLeftDense_embeds_finite_KFree_over_fixed_prefix
#print axioms Kk.henson_leftDense_embeds_finite_over_fixed_prefix

end Kk
