import Kk.FullBlockActualAge
import Kk.B3ExactCutStarWitness
import Kk.TrackFTypePrefixCanonicalAgeSandwich
import Kk.FiniteCliqueEmbeddingTransport
import Mathlib.Tactic

/-!
# Neutral original blocks pass the actual corrected B3 test
English-first proof: docs/neutral_block_B3_english_20261124.md.
The finite list of future TOP labels and its actual original endpoint
canonical-age equality remain explicit. No upper-upper edge of a test
witness is identified with an edge of the ambient numerical H.
-/

namespace Kk
open SuccessorTree.V10

noncomputable def resolvedQNumericTopAge
    (E : Nat → Nat → Bool) (ell d k N c : Nat) (j : Fin d → Nat) :=
  integerGraphAgeCanonical d ell
    (finiteOldColumnRawBound
      (fun x y => (finiteNumericHL (normalizedGraphModel E) k N).binary x y 0)
      ell d (Finset.range c)
      (fun p t => (finiteNumericHL (normalizedGraphModel E) k N).binary
        p (hPosition k (j t) k) 0))

theorem resolvedQNumericTopAge_antitone
    (E : Nat → Nat → Bool) (ell d k N c c' : Nat)
    (j : Fin d → Nat) (hc : c ≤ c') :
    AgeLe (resolvedQNumericTopAge E ell d k N c' j)
      (resolvedQNumericTopAge E ell d k N c j) := by
  unfold resolvedQNumericTopAge
  apply integerGraphAgeCanonical_mono_raw
  intro T
  unfold finiteOldColumnRawBound
  apply Nat.sub_le_sub_left
  apply finiteDirectedCliqueCapacity_mono
  intro x hx
  obtain ⟨hxRange,hAll⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hxRange).trans_le hc),hAll⟩

theorem resolvedQNumericTopAge_constant_on_neutral_block
    (E : Nat → Nat → Bool) (hSym : ∀ x y, E x y = E y x)
    (ell d k N b c : Nat) (j : Fin d → Nat)
    (hj : ∀ t, b < j t)
    (hc : hPosition k b 0 ≤ c)
    (hc' : c ≤ hPosition k (b+1) 0)
    (hNeutral :
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range b) (fun p t => E p (j t))) =
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range (b+1)) (fun p t => E p (j t)))) :
    resolvedQNumericTopAge E ell d k N c j =
      resolvedQNumericTopAge E ell d k N (hPosition k b 0) j := by
  have hStart := finiteNumericH_full_block_actual_canonical_age_eq_original
    E hSym ell k b N j (fun t => Nat.le_of_lt (hj t))
  have hEnd := finiteNumericH_full_block_actual_canonical_age_eq_original
    E hSym ell k (b+1) N j (fun t => hj t)
  have hEnds : resolvedQNumericTopAge E ell d k N (hPosition k b 0) j =
      resolvedQNumericTopAge E ell d k N (hPosition k (b+1) 0) j :=
    hStart.trans (hNeutral.trans hEnd.symm)
  have hUpper := resolvedQNumericTopAge_antitone E ell d k N _ _ j hc
  have hLower := resolvedQNumericTopAge_antitone E ell d k N _ _ j hc'
  funext T
  exact Nat.le_antisymm (hUpper T) (by rw [hEnds]; exact hLower T)

/-- The actual forbidden-family semantics gives the finite directed
clique checker, including the required diagonal and ordered enumeration. -/
theorem finitePoolCliqueCheck_false_of_model_avoidance
    (ell : Nat) (hell : 2 ≤ ell) (A : AgeTestModel 1 0 1)
    (P : Finset Nat) (hCarrier : ∀ p ∈ P, p ∈ A.carrier)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell → bad.Avoids A) :
    finitePoolCliqueCheck (fun x y => A.binary x y 0) ell P = false := by
  classical
  have hDiag : ∀ p ∈ P, A.diagonal p (0 : Fin 1) = false := by
    intro p hp
    cases hBit : A.diagonal p (0 : Fin 1) with
    | false => rfl
    | true =>
      exfalso
      let f : Fin 1 → Nat := fun _ => p
      have hCopy : A.Realizes loopPattern f := by
        refine ⟨?_,?_,?_,?_,?_⟩
        · intro a b hab
          exact ((ne_of_lt hab) (Subsingleton.elim a b)).elim
        · intro a
          exact hCarrier p hp
        · intro a b hab t
          exact (hab (Subsingleton.elim a b)).elim
        · intro a t
          exact Fin.elim0 t
        · intro a t
          fin_cases t
          exact hBit
      exact (hAvoid (.singleton loopPattern loopPattern_nonNeutral)
        (by simp [hensonForbiddenFamily])) ⟨f,hCopy⟩
  apply (finitePoolCliqueCheck_false_iff _ ell P).2
  rintro ⟨s,hsP,hsCard,hsClique⟩
  let f : Fin ell → Nat := s.orderEmbOfFin hsCard
  have hfMem : ∀ a, f a ∈ s := by
    intro a
    exact Finset.orderEmbOfFin_mem s hsCard a
  have hfMono : StrictMono f := (s.orderEmbOfFin hsCard).strictMono
  have hCopy : A.Realizes (cliquePattern ell) f := by
    refine ⟨hfMono,?_,?_,?_,?_⟩
    · intro a
      exact hCarrier _ (hsP (hfMem a))
    · intro a b hab t
      fin_cases t
      simpa [cliquePattern,hab] using
        hsClique (f a) (hfMem a) (f b) (hfMem b)
          (fun heq => hab (hfMono.injective heq))
    · intro a t
      exact Fin.elim0 t
    · intro a t
      fin_cases t
      exact hDiag _ (hsP (hfMem a))
  exact (hAvoid (.nontrivial ell (cliquePattern ell) (by omega)
    (cliquePattern_irreducible ell)) (by simp [hensonForbiddenFamily])) ⟨f,hCopy⟩

/-- Raw old capacities are unchanged by replacing the graph table
with one agreeing on the entire old finite pool. -/
theorem finiteOldColumnRawBound_eq_of_old_edge_eq
    (A B : Nat → Nat → Bool) (ell d : Nat) (P : Finset Nat)
    (c : Nat → Fin d → Bool)
    (hEq : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → A x y = B x y) :
    finiteOldColumnRawBound A ell d P c =
      finiteOldColumnRawBound B ell d P c := by
  funext T
  let U := oldSupportCommonNeighbourPool P c T.1
  have hSub : U ⊆ P := fun _ hx => (Finset.mem_filter.mp hx).1
  have hCap := finiteDirectedCliqueCapacity_induced_image_eq A B U id
    (fun _ _ _ _ h => h) (fun x hx y hy hne => hEq x (hSub hx) y (hSub hy) hne)
  simpa [finiteOldColumnRawBound,U] using
    congrArg (fun n : Nat => ell-1-n) hCap.symm

/-- All positive eligible selected physical names are covered by one
fixed finite tuple of later TOP names. If its ordinary original age
is neutral through this original insertion, the actual chosen B3
test passes. Repeated labels and arbitrary upper witness edges are allowed. -/
theorem henson_selectedB3_of_neutral_original_block
    (ell : Nat) (hell : 2 ≤ ell) (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool) (hLoops : ∀ x, E x x = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N b g M d : Nat) (hg : g ≤ k) (hCut : hPosition k b g < N)
    (original : Fin M → Fin N) (Selected : Fin M → Prop)
    (j : Fin d → Nat) (hj : ∀ t, b < j t)
    (hCover : ∀ v : Fin M, Selected v →
      hPosition k b g+1 ≤
        (finiteNumericH (normalizedGraphModel E) k N).freeLevel (original v).val →
      (finiteNumericHL (normalizedGraphModel E) k N).binary
        (hPosition k b g) (original v).val 0 = true →
      ∃ t : Fin d, (original v).val = hPosition k (j t) k)
    (hNeutral :
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range b) (fun p t => E p (j t))) =
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range (b+1)) (fun p t => E p (j t)))) :
    (selectedStagePoolPrescribedData
      (finiteNumericH (normalizedGraphModel E) k N)
      (hPosition k b g) original Selected).CorrectedB3
        (hensonForbiddenFamily ell hell) := by
  classical
  let c := hPosition k b g
  let C := finiteNumericHL (normalizedGraphModel E) k N
  let L : Nat → Nat → Bool := fun x y => C.binary x y 0
  let cols : Nat → Fin d → Bool := fun p t => L p (hPosition k (j t) k)
  by_contra hFail
  obtain ⟨v0,hSel0,hFree0,hEdge0⟩ :=
    henson_failedSelectedB3_has_eligible_cut_neighbour
      ell hell k hK E hLoops hSym hClique N c M hCut original Selected hFail
  obtain ⟨t0,_⟩ := hCover v0 hSel0 hFree0 hEdge0
  obtain ⟨V,e,_hFinite,hSocle,hDelete,hCopy,_hAt,_hFuture,hUpper⟩ :=
    henson_failed_selectedB3_has_exact_full_cut_star_core
      ell hell k hK E hLoops hSym hClique N c M hCut original Selected hFail
  let Vedge : Nat → Nat → Bool := fun x y => V.binary x y 0
  let P := Finset.range c
  let P' := Finset.range (c+1)
  let S : Finset Nat := Finset.univ.image e
  let W := S.filter (fun x => c < x)
  have hWCarrier : ∀ x ∈ W, x ∈ V.carrier ∧ c < x := by
    intro x hx
    obtain ⟨hxS,hxAbove⟩ := Finset.mem_filter.mp hx
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hxS
    exact ⟨ha ▸ hCopy.2.1 a,hxAbove⟩
  have hLabels : ∀ x : Nat, x ∈ W →
      ∃ t : Fin d, RelationalPrefixType.ofAgeModel V (c+1) x =
        RelationalPrefixType.ofAgeModel C (c+1) (hPosition k (j t) k) := by
    intro x hx
    obtain ⟨v,hSel,hFree,hEdge,hType⟩ :=
      hUpper x (hWCarrier x hx).1 (hWCarrier x hx).2
    obtain ⟨t,hAddr⟩ := hCover v hSel hFree hEdge
    exact ⟨t,hType.trans (congrArg (RelationalPrefixType.ofAgeModel C (c+1)) hAddr)⟩
  let sort : Nat → Fin d := fun x =>
    if hx : x ∈ W then Classical.choose (hLabels x hx) else t0
  have hCols : ∀ p ∈ P', ∀ x ∈ W,
      Vedge p x = cols p (sort x) ∧ Vedge x p = cols p (sort x) := by
    intro p hp x hx
    have hpLt : p < c+1 := Finset.mem_range.mp hp
    have hType := Classical.choose_spec (hLabels x hx)
    have hForward := congrArg (fun T : RelationalPrefixType (c+1) 1 0 1 =>
      T.binary (some (⟨p,hpLt⟩ : Fin (c+1))) none 0) hType
    have hReverse := congrArg (fun T : RelationalPrefixType (c+1) 1 0 1 =>
      T.binary none (some (⟨p,hpLt⟩ : Fin (c+1))) 0) hType
    change V.binary p x 0 = C.binary p (hPosition k (j (Classical.choose (hLabels x hx))) k) 0 at hForward
    change V.binary x p 0 = C.binary (hPosition k (j (Classical.choose (hLabels x hx))) k) p 0 at hReverse
    have hS := henson_finiteNumericH_binary_symmetric E hSym k N
      (hPosition k (j (Classical.choose (hLabels x hx))) k) p
    exact ⟨by simpa [Vedge,cols,L,sort,hx] using hForward,
      by simpa [Vedge,cols,L,sort,hx,C] using hReverse.trans hS⟩
  have hOld : ∀ p ∈ P', p ∈ V.carrier := by
    intro p hp
    have hpLe : p ≤ c := by have := Finset.mem_range.mp hp; omega
    exact (hSocle.1 p hpLe).2 (by change p < N; omega)
  have hOldEq : ∀ x ∈ P', ∀ y ∈ P', x ≠ y → Vedge x y = L x y := by
    intro x hx y hy _
    have hxLe : x ≤ c := by have := Finset.mem_range.mp hx; omega
    have hyLe : y ≤ c := by have := Finset.mem_range.mp hy; omega
    exact hSocle.2.1 x y hxLe hyLe 0
  have hSub : P ⊆ P' := by
    intro x hx
    exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega)
  have hDisj : Disjoint P' W := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have := Finset.mem_range.mp hx
    have := (hWCarrier x hy).2
    omega
  have hDisjOld : Disjoint P W := Finset.disjoint_of_subset_left hSub hDisj
  have hOldFree : finitePoolCliqueCheck Vedge ell (P ∪ W) = false := by
    apply finitePoolCliqueCheck_false_of_model_avoidance ell hell (V.withoutVertex c)
    · intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · have hpLt := Finset.mem_range.mp hp
        exact ⟨hOld p (hSub hp),by omega⟩
      · exact ⟨(hWCarrier p hp).1,by have := (hWCarrier p hp).2; omega⟩
    · exact hDelete
  have hAvoidC : ∀ bad, bad ∈ hensonForbiddenFamily ell hell → bad.Avoids C :=
    finiteNumericH_avoids_family (hensonForbiddenFamily ell hell)
      (normalizedGraphModel E) (by intro; trivial) k N
      ((hensonForbiddenFamily_avoids_iff ell hell E).2 ⟨hLoops,hSym,hClique⟩)
  have hP'FreeL : finitePoolCliqueCheck L ell P' = false :=
    finitePoolCliqueCheck_false_of_model_avoidance ell hell C P'
      (by intro p hp; change p < N; have := Finset.mem_range.mp hp; omega) hAvoidC
  have hP'Free : finitePoolCliqueCheck Vedge ell P' = false := by
    have h := finitePoolCliqueCheck_false_iff_induced_image Vedge L P' id
      (fun _ _ _ _ heq => heq) hOldEq ell
    simpa using h.mpr (by simpa using hP'FreeL)
  have hPFree : finitePoolCliqueCheck Vedge ell P = false := by
    apply (finitePoolCliqueCheck_false_iff Vedge ell P).2
    rintro ⟨T,hT,hCard,hCl⟩
    exact (finitePoolCliqueCheck_false_iff Vedge ell P').1 hP'Free
      ⟨T,hT.trans hSub,hCard,hCl⟩
  have hColsOld : ∀ p ∈ P, ∀ x ∈ W,
      Vedge p x = cols p (sort x) ∧ Vedge x p = cols p (sort x) :=
    fun p hp x hx => hCols p (hSub hp) x hx
  have hRawOld := finiteOldColumnRawBound_eq_of_old_edge_eq Vedge L ell d P cols
    (fun x hx y hy hne => hOldEq x (hSub hx) y (hSub hy) hne)
  have hRawNew := finiteOldColumnRawBound_eq_of_old_edge_eq Vedge L ell d P' cols hOldEq
  have hStart : hPosition k b 0 ≤ c := by dsimp [c,hPosition]; omega
  have hEnd : c+1 ≤ hPosition k (b+1) 0 :=
    hPosition_lt_of_block_lt k b (b+1) g 0 hg (Nat.lt_succ_self b)
  have hAge1 := resolvedQNumericTopAge_constant_on_neutral_block E hSym ell d k N b c j hj
    hStart (by omega) hNeutral
  have hAge2 := resolvedQNumericTopAge_constant_on_neutral_block E hSym ell d k N b (c+1) j hj
    (by omega) hEnd hNeutral
  have hAge : integerGraphAgeCanonical d ell (finiteOldColumnRawBound Vedge ell d P cols) =
      integerGraphAgeCanonical d ell (finiteOldColumnRawBound Vedge ell d P' cols) := by
    rw [hRawOld,hRawNew]
    exact hAge1.trans hAge2.symm
  obtain ⟨hWFree,hBounds⟩ :=
    (finiteOldFuture_free_iff_canonical_support Vedge ell d P W sort cols
      hDisjOld hColsOld hPFree).1 hOldFree
  have hNewFree := (finiteOldFuture_free_iff_canonical_support Vedge ell d P' W sort cols
      hDisj hCols hP'Free).2 ⟨hWFree,by simpa only [←hAge] using hBounds⟩
  have hSSub : S ⊆ P' ∪ W := by
    intro x hx
    by_cases h : x ≤ c
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_range.mpr (by omega)))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hx,by omega⟩))
  have hSCard : S.card = ell := by
    simp [S,Finset.card_image_of_injective _ hCopy.1.injective]
  have hSClique : IsDirectedCliqueOn Vedge S := by
    intro x hx y hy hxy
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hx
    obtain ⟨b,_,hb⟩ := Finset.mem_image.mp hy
    have hab : a ≠ b := by intro heq; subst b; exact hxy (ha.symm.trans hb)
    rw [←ha,←hb]
    simpa [Vedge,cliquePattern,hab] using hCopy.2.2.1 a b hab (0 : Fin 1)
  exact (finitePoolCliqueCheck_false_iff Vedge ell (P' ∪ W)).1 hNewFree
    ⟨S,hSSub,hSCard,hSClique⟩

end Kk
