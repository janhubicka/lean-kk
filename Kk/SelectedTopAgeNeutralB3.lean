import Kk.B3SmallCliqueCore
import Kk.B3ExactCutStarWitness
import Kk.B3CutVisibleNoNonempty
import Kk.FiniteOldColumnAge
import Kk.NumericPrefixCanonicalCover
import Kk.TrackDPhysicalHSymmetry
import Kk.NumericTopNeutralPrefixAge
import Mathlib.Tactic

/-!
# Actual chosen B3 from complete finite reference-age equality

English proof and independent review were committed first in
`docs/selected_top_age_neutral_b3_english_20261124.md` and
`docs/audits/2026-11-24-selected-top-b3-independent-review.md`.

All supports and arbitrary repeated future labels are retained. The
initial ordinary socle is the entire physical prefix. Chosen outputs
are covered by actual complete physical types, not stipulated ranks.
No auxiliary E structure is invented on an age-test continuation.

The cut-visible strengthening was independently reviewed and committed in
`docs/cut_visible_neutral_age_full_b3_english_20261124.md`. Only positive
eligible names must be covered: the exact failed cut-star core contains
no other future vertices, even when the original full stage does.
-/

namespace Kk

open SuccessorTree.V10

private theorem finitePool_free_of_henson_avoidance
    (ell : Nat) (hell : 2 ≤ ell) (V : AgeTestModel 1 0 1)
    (P : Finset Nat) (hP : ∀ x ∈ P, x ∈ V.carrier)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids V) :
    finitePoolCliqueCheck (fun x y => V.binary x y (0 : Fin 1)) ell P = false := by
  classical
  have hDiagonal : ∀ x ∈ P, V.diagonal x (0 : Fin 1) = false := by
    intro x hx
    cases hBit : V.diagonal x (0 : Fin 1) with
    | false => rfl
    | true =>
      have hCopy : V.Realizes loopPattern (fun _ : Fin 1 => x) := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro a b hab
          exact False.elim ((ne_of_lt hab) (Subsingleton.elim a b))
        · intro a
          exact hP x hx
        · intro a b hab t
          exact False.elim (hab (Subsingleton.elim a b))
        · intro a t
          exact Fin.elim0 t
        · intro a t
          fin_cases t
          exact hBit
      exact False.elim ((hAvoid
        (.singleton loopPattern loopPattern_nonNeutral)
        (by simp [hensonForbiddenFamily])) ⟨_, hCopy⟩)
  apply (finitePoolCliqueCheck_false_iff _ ell P).2
  rintro ⟨s, hsP, hsCard, hsClique⟩
  let f : Fin ell ↪o Nat := s.orderEmbOfFin hsCard
  have hfMem : ∀ a : Fin ell, f a ∈ s := by
    intro a
    exact s.orderEmbOfFin_mem hsCard a
  have hCopy : V.Realizes (cliquePattern ell) f := by
    refine ⟨f.strictMono, ?_, ?_, ?_, ?_⟩
    · intro a
      exact hP (f a) (hsP (hfMem a))
    · intro a b hab t
      fin_cases t
      have hNe : f a ≠ f b := fun h => hab (f.injective h)
      simpa [cliquePattern, hab] using
        hsClique (f a) (hfMem a) (f b) (hfMem b) hNe
    · intro a t
      exact Fin.elim0 t
    · intro a t
      fin_cases t
      exact hDiagonal (f a) (hsP (hfMem a))
  exact (hAvoid
    (.nontrivial ell (cliquePattern ell) (by omega)
      (cliquePattern_irreducible ell))
    (by simp [hensonForbiddenFamily])) ⟨f, hCopy⟩

private theorem oldRaw_eq_of_same_old_graph
    (E F : Nat → Nat → Bool) (ell d : Nat)
    (P : Finset Nat) (col : Nat → Fin d → Bool)
    (hOld : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → E x y = F x y) :
    finiteOldColumnRawBound E ell d P col =
      finiteOldColumnRawBound F ell d P col := by
  funext T
  unfold finiteOldColumnRawBound
  congr 1
  exact (finiteDirectedCliqueCapacity_eq_of_offDiagonal_agreement
    E F (oldSupportCommonNeighbourPool P col T.1)
    (fun x hx y hy hxy => hOld x (Finset.mem_filter.mp hx).1
      y (Finset.mem_filter.mp hy).1 hxy)).symm

/-- Complete canonical reference-age equality on an actual finite list
of physical upper types implies the genuine chosen selected-stage K4
corrected-B3 test. Every selected eligible CUT-ADJACENT original must
occur in that list; the list may have repeated names. Uncovered zero-bit
cap/auxiliary names are allowed in the full source. The whole old prefix,
all support constraints, both directions of the chosen ordinary types,
and the arbitrary future graph are preserved.

This is an actual B3 conclusion, with no B3/no-I1/no-I2 premise. Its
age-equality premise still requires a construction-specific proof. -/
theorem k4_selectedB3_of_complete_reference_age_eq
    (k : Nat) (hK : 4 ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin 4 → Nat, StrictMono f ∧
      (∀ a b : Fin 4, a ≠ b → E (f a) (f b) = true))
    (N cut M d : Nat) (hCut : cut < N)
    (original : Fin M → Fin N) (Selected : Fin M → Prop)
    (target : Fin d → Fin N)
    (hCover : ∀ v : Fin M, Selected v →
      cut+1 ≤ (finiteNumericH (normalizedGraphModel E) k N).freeLevel
        (original v).val →
      (finiteNumericHL (normalizedGraphModel E) k N).binary
        cut (original v).val (0 : Fin 1) = true →
      ∃ t : Fin d, original v = target t)
    (hAge :
      integerGraphAgeCanonical d 4
        (finiteOldColumnRawBound
          (fun x y => (finiteNumericHL (normalizedGraphModel E) k N).binary
            x y (0 : Fin 1)) 4 d (Finset.range cut)
          (fun p t => (finiteNumericHL (normalizedGraphModel E) k N).binary
            p (target t).val (0 : Fin 1))) =
      integerGraphAgeCanonical d 4
        (finiteOldColumnRawBound
          (fun x y => (finiteNumericHL (normalizedGraphModel E) k N).binary
            x y (0 : Fin 1)) 4 d (Finset.range (cut+1))
          (fun p t => (finiteNumericHL (normalizedGraphModel E) k N).binary
            p (target t).val (0 : Fin 1)))) :
    (selectedStagePoolPrescribedData
      (finiteNumericH (normalizedGraphModel E) k N)
      cut original Selected).CorrectedB3 (hensonForbiddenFamily 4 (by decide)) := by
  classical
  let K := normalizedGraphModel E
  let A := finiteNumericH K k N
  let C := finiteNumericHL K k N
  let family := hensonForbiddenFamily 4 (by decide)
  have hCAvoid : ∀ bad, bad ∈ family → bad.Avoids C :=
    finiteNumericH_avoids_family family K (by intro i; trivial) k N
      ((hensonForbiddenFamily_avoids_iff 4 (by decide) E).2
        ⟨hLoops, hSym, hClique⟩)
  have hCSym : ∀ x y : Nat,
      C.binary x y (0 : Fin 1) = C.binary y x (0 : Fin 1) := by
    intro x y
    exact hNumericBinary_symm_of_base_symm K.binary
      (fun i j _ => hSym i j) k x y (0 : Fin 1)
  by_cases hd : Nonempty (Fin d)
  · let defaultSort : Fin d := Classical.choice hd
    by_contra hFail
    obtain ⟨V,e,hFinite,hSocle,hDelete,hCopy,_hAt,_hFuture,hUpper⟩ :=
      henson_failed_selectedB3_has_exact_full_cut_star_core
        4 (by decide) k hK E hLoops hSym hClique
        N cut M hCut original Selected hFail
    obtain ⟨bound,hBound⟩ := hFinite
    let W : Finset Nat := (Finset.range bound).filter
      (fun x => x ∈ V.carrier ∧ cut < x)
    let P0 : Finset Nat := Finset.range cut
    let P1 : Finset Nat := Finset.range (cut+1)
    let L : Nat → Nat → Bool := fun x y => V.binary x y (0 : Fin 1)
    let col : Nat → Fin d → Bool :=
      fun p t => C.binary p (target t).val (0 : Fin 1)
    have hNamed : ∀ x : Nat, x ∈ V.carrier ∧ cut < x →
        ∃ t : Fin d,
          RelationalPrefixType.ofAgeModel V (cut+1) x =
            RelationalPrefixType.ofAgeModel C (cut+1) (target t).val := by
      intro x hx
      obtain ⟨v,hSel,hEligible,hPositive,hType⟩ := hUpper x hx.1 hx.2
      obtain ⟨t,ht⟩ := hCover v hSel hEligible hPositive
      exact ⟨t, by simpa only [ht] using hType⟩
    let sort : Nat → Fin d := fun x =>
      if hx : x ∈ V.carrier ∧ cut < x then Classical.choose (hNamed x hx)
      else defaultSort
    have hNamedSort : ∀ x ∈ W,
        RelationalPrefixType.ofAgeModel V (cut+1) x =
          RelationalPrefixType.ofAgeModel C (cut+1) (target (sort x)).val := by
      intro x hx
      have hxV : x ∈ V.carrier ∧ cut < x := (Finset.mem_filter.mp hx).2
      simpa only [sort, dite_eq_left hxV] using Classical.choose_spec (hNamed x hxV)
    have hColumns1 : ∀ p ∈ P1, ∀ w ∈ W,
        L p w = col p (sort w) ∧ L w p = col p (sort w) := by
      intro p hp w hw
      have hpCut : p < cut+1 := Finset.mem_range.mp hp
      have hType := hNamedSort w hw
      have hForward := congrArg
        (fun T : RelationalPrefixType (cut+1) 1 0 1 =>
          T.binary (some ⟨p,hpCut⟩) none (0 : Fin 1)) hType
      have hBackward := congrArg
        (fun T : RelationalPrefixType (cut+1) 1 0 1 =>
          T.binary none (some ⟨p,hpCut⟩) (0 : Fin 1)) hType
      change L p w = col p (sort w) at hForward
      change L w p = C.binary (target (sort w)).val p (0 : Fin 1) at hBackward
      exact ⟨hForward, hBackward.trans (hCSym _ _)⟩
    have hP0P1 : P0 ⊆ P1 := by
      intro x hx
      exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega)
    have hColumns0 : ∀ p ∈ P0, ∀ w ∈ W,
        L p w = col p (sort w) ∧ L w p = col p (sort w) :=
      fun p hp w hw => hColumns1 p (hP0P1 hp) w hw
    have hDisjoint1 : Disjoint P1 W := by
      apply Finset.disjoint_left.mpr
      intro x hxP hxW
      have := Finset.mem_range.mp hxP
      have := (Finset.mem_filter.mp hxW).2.2
      omega
    have hDisjoint0 : Disjoint P0 W := hDisjoint1.mono_left hP0P1
    have hOldFree : finitePoolCliqueCheck L 4 (P0 ∪ W) = false := by
      apply finitePool_free_of_henson_avoidance 4 (by decide)
        (V.withoutVertex cut) (P0 ∪ W) _ hDelete
      intro x hx
      rcases Finset.mem_union.mp hx with hxP | hxW
      · have hxlt : x < cut := Finset.mem_range.mp hxP
        have hxCarrier : x ∈ V.carrier :=
          (hSocle.1 x (by omega)).2 (by change x < N; omega)
        exact ⟨hxCarrier, by omega⟩
      · have hxV := (Finset.mem_filter.mp hxW).2
        exact ⟨hxV.1, by omega⟩
    have hPast1 : finitePoolCliqueCheck L 4 P1 = false := by
      have hPhysical : finitePoolCliqueCheck
          (fun x y => C.binary x y (0 : Fin 1)) 4 P1 = false :=
        finitePool_free_of_henson_avoidance 4 (by decide) C P1
          (by intro x hx; change x < N; have := Finset.mem_range.mp hx; omega)
          hCAvoid
      apply (finitePoolCliqueCheck_false_iff_capacity_lt L 4 P1).2
      rw [finiteDirectedCliqueCapacity_eq_of_offDiagonal_agreement
        (fun x y => C.binary x y (0 : Fin 1)) L P1
        (by
          intro x hx y hy _hxy
          exact (hSocle.2.1 x y
            (by have := Finset.mem_range.mp hx; omega)
            (by have := Finset.mem_range.mp hy; omega) (0 : Fin 1)).symm)]
      exact (finitePoolCliqueCheck_false_iff_capacity_lt _ 4 P1).1 hPhysical
    have hPast0 : finitePoolCliqueCheck L 4 P0 = false := by
      apply (finitePoolCliqueCheck_false_iff_capacity_lt L 4 P0).2
      exact lt_of_le_of_lt (finiteDirectedCliqueCapacity_mono L P0 P1 hP0P1)
        ((finitePoolCliqueCheck_false_iff_capacity_lt L 4 P1).1 hPast1)
    have hRaw0 : finiteOldColumnRawBound L 4 d P0 col =
        finiteOldColumnRawBound (fun x y => C.binary x y (0 : Fin 1))
          4 d P0 col := by
      apply oldRaw_eq_of_same_old_graph
      intro x hx y hy _hxy
      exact hSocle.2.1 x y
        (by have := Finset.mem_range.mp hx; omega)
        (by have := Finset.mem_range.mp hy; omega) (0 : Fin 1)
    have hRaw1 : finiteOldColumnRawBound L 4 d P1 col =
        finiteOldColumnRawBound (fun x y => C.binary x y (0 : Fin 1))
          4 d P1 col := by
      apply oldRaw_eq_of_same_old_graph
      intro x hx y hy _hxy
      exact hSocle.2.1 x y
        (by have := Finset.mem_range.mp hx; omega)
        (by have := Finset.mem_range.mp hy; omega) (0 : Fin 1)
    have hAgeV : integerGraphAgeCanonical d 4
        (finiteOldColumnRawBound L 4 d P0 col) =
      integerGraphAgeCanonical d 4
        (finiteOldColumnRawBound L 4 d P1 col) := by
      rw [hRaw0, hRaw1]
      exact hAge
    obtain ⟨hWFree,hBounds⟩ :=
      (finiteOldFuture_free_iff_canonical_support L 4 d P0 W sort col
        hDisjoint0 hColumns0 hPast0).1 hOldFree
    have hAfterFree : finitePoolCliqueCheck L 4 (P1 ∪ W) = false := by
      apply (finiteOldFuture_free_iff_canonical_support L 4 d P1 W sort col
        hDisjoint1 hColumns1 hPast1).2
      refine ⟨hWFree, ?_⟩
      intro s hs hc T
      rw [← hAgeV]
      exact hBounds s hs hc T
    let s : Finset Nat := Finset.univ.image e
    have hsSub : s ⊆ P1 ∪ W := by
      intro x hx
      obtain ⟨a,_ha,rfl⟩ := Finset.mem_image.mp hx
      by_cases hle : e a ≤ cut
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_range.mpr (by omega)))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (hBound (e a) (hCopy.2.1 a)),
            hCopy.2.1 a, by omega⟩))
    have hsCard : s.card = 4 := by
      simp [s, Finset.card_image_of_injective _ hCopy.1.injective]
    have hsClique : IsDirectedCliqueOn L s := by
      intro x hx y hy hxy
      obtain ⟨a,_ha,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b,_hb,rfl⟩ := Finset.mem_image.mp hy
      have hab : a ≠ b := fun h => hxy (congrArg e h)
      have hEdge := hCopy.2.2.1 a b hab (0 : Fin 1)
      simpa [L, cliquePattern, hab] using hEdge
    exact ((finitePoolCliqueCheck_false_iff L 4 (P1 ∪ W)).1 hAfterFree)
      ⟨s,hsSub,hsCard,hsClique⟩
  · apply henson_fullB3_of_no_eligible_cut_neighbour
      4 (by decide) k hK E hLoops hSym hClique
      N cut M hCut original Selected
    intro v hSel hEligible hPositive
    obtain ⟨t,_ht⟩ := hCover v hSel hEligible hPositive
    exact hd ⟨t⟩

/-- Concrete later-TOP specialization: equality of the actual complete
base-graph reference age supplies the physical cut/delete age identity
and therefore the actual chosen B3 verdict. The genuine carrier bounds,
all positive eligible names and every support of the age are explicit. -/
theorem k4_selectedTop_B3_of_base_prefix_neutral
    (k : Nat) (hK : 4 ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin 4 → Nat, StrictMono f ∧
      (∀ a b : Fin 4, a ≠ b → E (f a) (f b) = true))
    (N b g M d : Nat) (hg : g < k)
    (hCut : hPosition k b g < N)
    (original : Fin M → Fin N) (Selected : Fin M → Prop)
    (target : Fin d → Nat) (hLater : ∀ t, b < target t)
    (hTargetBound : ∀ t, hPosition k (target t) k < N)
    (hCover : ∀ v : Fin M, Selected v →
      hPosition k b g+1 ≤
        (finiteNumericH (normalizedGraphModel E) k N).freeLevel
          (original v).val →
      (finiteNumericHL (normalizedGraphModel E) k N).binary
        (hPosition k b g) (original v).val (0 : Fin 1) = true →
      ∃ t : Fin d, (original v).val = hPosition k (target t) k)
    (hNeutral : baseTopPrefixCanonicalAge E 4 d b target =
      baseTopPrefixCanonicalAge E 4 d (b+1) target) :
    (selectedStagePoolPrescribedData
      (finiteNumericH (normalizedGraphModel E) k N)
      (hPosition k b g) original Selected).CorrectedB3
        (hensonForbiddenFamily 4 (by decide)) := by
  let targetFin : Fin d → Fin N :=
    fun t => ⟨hPosition k (target t) k,hTargetBound t⟩
  apply k4_selectedB3_of_complete_reference_age_eq
    k hK E hLoops hSym hClique N (hPosition k b g) M d hCut
    original Selected targetFin
  · intro v hSelected hEligible hPositive
    obtain ⟨t,ht⟩ := hCover v hSelected hEligible hPositive
    exact ⟨t, Fin.ext ht⟩
  · exact (numericHTop_prefix_canonical_ages_eq_of_base_neutral
      E hSym 4 d k N b g (Nat.le_of_lt hg) target hLater hNeutral).1

#print axioms k4_selectedB3_of_complete_reference_age_eq
#print axioms k4_selectedTop_B3_of_base_prefix_neutral

end Kk
