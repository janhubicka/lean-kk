import Kk.IsolatedCliqueBlocks
import Mathlib.Tactic

/-!
# Real reserved originals from an explicit left-dense extension property

The finite isolated-block construction chooses a new abstract edge
table. To realize reserved vertices at actual indices of ONE
pre-existing enumerated graph, an existence property is needed.

The property is displayed exactly: for every finite S of fewer than
ell-1 old vertices and every cut front above S, a later original v
realizes the complete passing column E(x,v) = E(v,x) = (x in S)
for every x<v, including intervening vertices.

From this nontrivial left-density hypothesis we construct an ACTUAL
finite clique of r<ell reserved original indices, isolated from
all earlier vertices outside it. The explicit hypothesis has NOT
yet been instantiated for the manuscript's fixed Henson enumeration.
Later selected vertices and the parameter-closed B3 orbit remain open.
-/

namespace Kk

/-- Complete-column left-density for small admissible neighbour
sets. Both directed atoms and intervening coordinates are fixed. -/
def SmallCliqueLeftDense (E : Nat → Nat → Bool) (ell : Nat) : Prop :=
  ∀ (front : Nat) (S : Finset Nat),
    (∀ x ∈ S, x < front) →
    S.card < ell-1 →
    ∃ v : Nat, front ≤ v ∧
      ∀ x, x < v →
        E x v = decide (x ∈ S) ∧ E v x = decide (x ∈ S)

/-- Build a clique while tracking a cut and every nonedge from
earlier nonreserved vertices to the chosen original indices. -/
theorem smallCliqueLeftDense_build_reserved
    (E : Nat → Nat → Bool) (ell base : Nat)
    (hDense : SmallCliqueLeftDense E ell) :
    ∀ r : Nat, r < ell →
      ∃ (S : Finset Nat) (front : Nat),
        S.card = r ∧ base ≤ front ∧
        (∀ q ∈ S, base ≤ q ∧ q < front) ∧
        IsDirectedCliqueOn E S ∧
        (∀ q ∈ S, ∀ x, x < q → x ∉ S →
          E x q = false ∧ E q x = false) := by
  intro r
  induction r with
  | zero =>
    intro _
    refine ⟨∅, base, by simp, le_rfl, ?_, ?_, ?_⟩
    · intro q hq
      simp at hq
    · intro q hq
      simp at hq
    · intro q hq
      simp at hq
  | succ r ih =>
    intro hR
    obtain ⟨S, front, hCard, hBaseFront, hSupport, hClique, hIsolated⟩ :=
      ih (by omega)
    have hSmall : S.card < ell-1 := by omega
    have hBelow : ∀ q ∈ S, q < front := by
      intro q hq
      exact (hSupport q hq).2
    obtain ⟨v, hV, hAdj⟩ :=
      hDense front S hBelow hSmall
    have hFresh : v ∉ S := by
      intro hv
      have hvlt := (hSupport v hv).2
      omega
    refine ⟨insert v S, v+1, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hFresh, hCard]
    · omega
    · intro q hq
      rcases Finset.mem_insert.mp hq with hEq | hOld
      · subst q
        exact ⟨by omega, by omega⟩
      · have hq' := hSupport q hOld
        exact ⟨hq'.1, by omega⟩
    · intro x hx y hy hxy
      rcases Finset.mem_insert.mp hx with hxv | hxs
      · subst x
        rcases Finset.mem_insert.mp hy with hyv | hys
        · exact False.elim (hxy hyv.symm)
        · have hyl : y < v := by
            have ht := (hSupport y hys).2
            omega
          have he := (hAdj y hyl).2
          simpa [hys] using he
      · rcases Finset.mem_insert.mp hy with hyv | hys
        · subst y
          have hxl : x < v := by
            have ht := (hSupport x hxs).2
            omega
          have he := (hAdj x hxl).1
          simpa [hxs] using he
        · exact hClique x hxs y hys hxy
    · intro q hq x hx hOutside
      have hxNotS : x ∉ S := by
        intro hxS
        exact hOutside (Finset.mem_insert_of_mem hxS)
      rcases Finset.mem_insert.mp hq with hEq | hOld
      · subst q
        have he := hAdj x hx
        simpa [hxNotS] using he
      · exact hIsolated q hOld x hx hxNotS

/-- Genuine ambient original indices: r<ell fresh vertices form a
directed clique beyond base, and every earlier nonreserved vertex
is nonadjacent to each reserved vertex in both directions. -/
theorem smallCliqueLeftDense_exists_reserved
    (E : Nat → Nat → Bool) (ell base r : Nat)
    (hDense : SmallCliqueLeftDense E ell)
    (hR : r < ell) :
    ∃ S : Finset Nat,
      S.card = r ∧
      (∀ q ∈ S, base ≤ q) ∧
      IsDirectedCliqueOn E S ∧
      (∀ q ∈ S, ∀ x, x < q → x ∉ S →
        E x q = false ∧ E q x = false) := by
  obtain ⟨S, front, hCard, _, hSupport, hClique, hIsolated⟩ :=
    smallCliqueLeftDense_build_reserved E ell base hDense r hR
  refine ⟨S, hCard, ?_, hClique, hIsolated⟩
  intro q hq
  exact (hSupport q hq).1

/-- Graph K_ell-freeness alone cannot imply this left-density:
the empty graph cannot realize a singleton positive column. -/
theorem emptyGraph_not_smallCliqueLeftDense :
    ¬ SmallCliqueLeftDense (fun _ _ => false) 3 := by
  intro hDense
  have hBounds : ∀ x ∈ ({0} : Finset Nat), x < 1 := by
    simp
  have hSmall : ({0} : Finset Nat).card < 3-1 := by
    decide
  obtain ⟨v, hv, hAdj⟩ :=
    hDense 1 ({0} : Finset Nat) hBounds hSmall
  have hBad := (hAdj 0 (by omega)).1
  simp at hBad

end Kk
