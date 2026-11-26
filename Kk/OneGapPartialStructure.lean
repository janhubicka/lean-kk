import Kk.HensonEncoding
import Kk.FiniteOldColumnAge
import SuccessorTree.V10.CountableGPlusEmbedding
import Mathlib.Tactic

/-!
# One-gap ordinary resolution (English-first: 26 November 2026)

Replace numerical generations by a partial structure with one isolated
ordinary gap before each meaningful vertex. This module establishes the
basic padding and canonical-age transfer interface; it does not yet
construct a resolved countable diary or prove the full Kpt orbit theorem.

See docs/one_gap_successor_english_audit_20261126.md.
-/

namespace Kk

open SuccessorTree.V10

def oneGapAddress (i : Nat) : Nat := 2 * i + 2

def oneGapIndex (v : Nat) : Nat := v / 2 - 1

def oneGapReal (v : Nat) : Prop := 0 < v ∧ v % 2 = 0

instance (v : Nat) : Decidable (oneGapReal v) := by
  unfold oneGapReal
  infer_instance

theorem oneGapAddress_real (i : Nat) : oneGapReal (oneGapAddress i) := by
  unfold oneGapAddress oneGapReal
  omega

theorem oneGapIndex_address (i : Nat) :
    oneGapIndex (oneGapAddress i) = i := by
  unfold oneGapIndex oneGapAddress
  omega

theorem oneGapAddress_index {v : Nat} (hv : oneGapReal v) :
    oneGapAddress (oneGapIndex v) = v := by
  unfold oneGapReal at hv
  unfold oneGapAddress oneGapIndex
  omega

theorem oneGapAddress_strictMono : StrictMono oneGapAddress := by
  intro i j hij
  unfold oneGapAddress
  omega

/-- Ordinary edges are present only between positive even coordinates. -/
def oneGapEdge (G : Nat → Nat → Bool) (u v : Nat) : Bool :=
  if oneGapReal u ∧ oneGapReal v then G (oneGapIndex u) (oneGapIndex v)
  else false

theorem oneGapEdge_real (G : Nat → Nat → Bool) {u v : Nat}
    (h : oneGapEdge G u v = true) :
    oneGapReal u ∧ oneGapReal v := by
  by_cases hr : oneGapReal u ∧ oneGapReal v
  · exact hr
  · simp [oneGapEdge, hr] at h

theorem oneGapEdge_address (G : Nat → Nat → Bool) (i j : Nat) :
    oneGapEdge G (oneGapAddress i) (oneGapAddress j) = G i j := by
  simp [oneGapEdge, oneGapAddress_real, oneGapIndex_address]

/-- Exact free cut: v-1 for meaningful vertices, zero for all dummies. -/
def oneGapAux (u v : Nat) : Bool :=
  decide (oneGapReal v ∧ u + 1 < v)

def oneGapPartial (G : Nat → Nat → Bool) :
    CountableEnumeratedPartialStructure 1 0 1 where
  L := normalizedGraphModel (oneGapEdge G)
  fullCarrier := by intro v; trivial
  E := oneGapAux
  spaced := by
    intro u v h
    have hh : oneGapReal v ∧ u + 1 < v := by
      simpa [oneGapAux] using h
    exact hh.2
  downward := by
    intro u v h w hw
    have hh : oneGapReal v ∧ u + 1 < v := by
      simpa [oneGapAux] using h
    have hlt : w + 1 < v := by omega
    simp [oneGapAux, hh.1, hlt]
  linked_E := by
    intro u v huv h
    obtain ⟨r, hr⟩ := h
    change oneGapEdge G u v = true ∨ oneGapEdge G v u = true at hr
    have hreals : oneGapReal u ∧ oneGapReal v := by
      rcases hr with h | h
      · exact oneGapEdge_real G h
      · have hh := oneGapEdge_real G h
        exact ⟨hh.2, hh.1⟩
    have hu := hreals.1
    have hv := hreals.2
    unfold oneGapReal at hu hv
    have hlt : u + 1 < v := by omega
    simp [oneGapAux, hreals.2, hlt]

theorem oneGapPartial_freeLevel (G : Nat → Nat → Bool)
    (N v : Nat) (hv : v < N) :
    ((oneGapPartial G).finitePrefix N).freeLevel v =
      if oneGapReal v then v - 1 else 0 := by
  let C := oneGapPartial G
  change (C.finitePrefix N).freeLevel v = _
  rw [C.finitePrefix_freeLevel_eq N v hv]
  have hActual := canonicalFreeLevel_isFreeCut C.E C.spaced C.downward v
  apply freeCut_unique C.E v _ _ hActual
  by_cases hr : oneGapReal v
  · rw [if_pos hr]
    constructor
    · intro u hu
      change oneGapAux u v = true
      have hlt : u + 1 < v := by omega
      simp [oneGapAux, hr, hlt]
    · change oneGapAux (v - 1) v = false
      have hn : ¬ v - 1 + 1 < v := by omega
      simp [oneGapAux, hr, hn]
  · rw [if_neg hr]
    constructor
    · intro u hu
      omega
    · change oneGapAux 0 v = false
      simp [oneGapAux, hr]

/-- No change to the ordinary forbidden family: the inserted dummies
are isolated and any clique of size at least two uses real coordinates. -/
theorem oneGapPartial_avoids (G : Nat → Nat → Bool) (ell : Nat)
    (hell : 2 ≤ ell)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel G)) :
    ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (oneGapPartial G).L := by
  obtain ⟨hLoops, hSym, hNoClique⟩ :=
    (hensonForbiddenFamily_avoids_iff ell hell G).mp hAvoid
  change ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
    bad.Avoids (normalizedGraphModel (oneGapEdge G))
  apply (hensonForbiddenFamily_avoids_iff ell hell (oneGapEdge G)).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro v
    by_cases hr : oneGapReal v
    · simp [oneGapEdge, hr, hLoops]
    · simp [oneGapEdge, hr]
  · intro u v
    by_cases hu : oneGapReal u <;> by_cases hv : oneGapReal v <;>
      simp [oneGapEdge, hu, hv, hSym]
  · rintro ⟨f, hf, hEdges⟩
    have hOther : ∀ a : Fin ell, ∃ b : Fin ell, a ≠ b := by
      intro a
      by_cases ha : a.val = 0
      · refine ⟨⟨1, by omega⟩, ?_⟩
        intro h
        have hh : a.val = 1 := congrArg Fin.val h
        omega
      · refine ⟨⟨0, by omega⟩, ?_⟩
        intro h
        have hh : a.val = 0 := congrArg Fin.val h
        exact ha hh
    have hReal : ∀ a : Fin ell, oneGapReal (f a) := by
      intro a
      obtain ⟨b, hab⟩ := hOther a
      exact (oneGapEdge_real G (hEdges a b hab)).1
    have hm : StrictMono (fun a => oneGapIndex (f a)) := by
      intro a b hab
      have hlt := hf hab
      have ha := hReal a
      have hb := hReal b
      unfold oneGapReal at ha hb
      change f a / 2 - 1 < f b / 2 - 1
      omega
    apply hNoClique
    refine ⟨fun a => oneGapIndex (f a), hm, ?_⟩
    intro a b hab
    simpa [oneGapEdge, hReal a, hReal b] using hEdges a b hab

/-- Equality of the ENTIRE canonical old-column age suffices for a
common finite labelled continuation, with both bilateral crossing
columns fixed. This is the ordinary-age portion of the new full B3
projection. The fact that every positive chosen upper type is selected
must be proved separately from the one-gap geometry. -/
theorem oneGap_continuation_of_equal_canonical_age
    (G : Nat → Nat → Bool) (ell d : Nat)
    (P Q W : Finset Nat) (sort : Nat → Fin d)
    (col : Nat → Fin d → Bool)
    (hDisjointP : Disjoint P W) (hDisjointQ : Disjoint Q W)
    (hColumnsP : ∀ p ∈ P, ∀ w ∈ W,
      G p w = col p (sort w) ∧ G w p = col p (sort w))
    (hColumnsQ : ∀ p ∈ Q, ∀ w ∈ W,
      G p w = col p (sort w) ∧ G w p = col p (sort w))
    (hPFree : finitePoolCliqueCheck G ell P = false)
    (hQFree : finitePoolCliqueCheck G ell Q = false)
    (hEqual : ∀ T : IntegerGraphSupport d ell,
      integerGraphAgeCanonical d ell (finiteOldColumnRawBound G ell d P col) T =
      integerGraphAgeCanonical d ell (finiteOldColumnRawBound G ell d Q col) T)
    (hBefore : finitePoolCliqueCheck G ell (P ∪ W) = false) :
    finitePoolCliqueCheck G ell (Q ∪ W) = false := by
  have hP := (finiteOldFuture_free_iff_canonical_support
    G ell d P W sort col hDisjointP hColumnsP hPFree).mp hBefore
  apply (finiteOldFuture_free_iff_canonical_support
    G ell d Q W sort col hDisjointQ hColumnsQ hQFree).mpr
  refine ⟨hP.1, ?_⟩
  intro s hs hc T
  rw [← hEqual T]
  exact hP.2 s hs hc T

end Kk
