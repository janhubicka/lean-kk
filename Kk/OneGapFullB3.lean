import Kk.OneGapPartialStructure
import Kk.FiniteCliqueEmbeddingTransport
import Kk.HensonB3Asymmetry
import SuccessorTree.V10.I3AmbientSocleBridge
import SuccessorTree.V10.I3ClosureSelectedCrossing
import Mathlib.Tactic

/-!
# Full corrected B3 from exact selected ordinary ages

The witness is an arbitrary finite L-structure, not an induced
subgraph of the resolution. Restrict to the upper vertices of a
forbidden clique through the cut. Their complete types must be
selected-terminal types (repetitions allowed). Equality of the
canonical old-column age rules out the new clique.
No numerical-H hypothesis or marked-source nonemptiness is used.
-/

namespace Kk
open SuccessorTree
open SuccessorTree.V10

theorem oneGap_diag_false_of_avoid
    (ell : Nat) (hell : 2 ≤ ell) (C : AgeTestModel 1 0 1)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell → bad.Avoids C)
    (x : Nat) (hx : x ∈ C.carrier) :
    C.diagonal x (0 : Fin 1) = false := by
  cases h : C.diagonal x (0 : Fin 1) with
  | false => rfl
  | true =>
    exfalso
    let f : Fin 1 → Nat := fun _ => x
    have hCopy : C.Realizes loopPattern f := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro a b hab
        exact ((ne_of_lt hab) (Subsingleton.elim a b)).elim
      · intro a
        exact hx
      · intro a b hab t
        exact (hab (Subsingleton.elim a b)).elim
      · intro a t
        exact Fin.elim0 t
      · intro a t
        fin_cases t
        simpa [f, loopPattern] using h
    have hm : NormalizedForbidden.singleton loopPattern
        loopPattern_nonNeutral ∈ hensonForbiddenFamily ell hell := by
      simp [hensonForbiddenFamily]
    exact hAvoid _ hm ⟨f,hCopy⟩

/-- The normalized forbidden-family certificate controls every
finite subset of the carrier. -/
theorem oneGap_pool_free_of_avoid
    (ell : Nat) (hell : 2 ≤ ell) (C : AgeTestModel 1 0 1)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell → bad.Avoids C)
    (P : Finset Nat) (hP : ∀ x ∈ P, x ∈ C.carrier) :
    finitePoolCliqueCheck (fun x y => C.binary x y (0 : Fin 1)) ell P = false := by
  classical
  apply (finitePoolCliqueCheck_false_iff _ ell P).2
  rintro ⟨s,hs,hCard,hClique⟩
  let f : Fin ell ↪o Nat := s.orderEmbOfFin hCard
  have hIn : ∀ a : Fin ell, f a ∈ C.carrier :=
    fun a => hP (f a) (hs (s.orderEmbOfFin_mem hCard a))
  have hCopy : C.Realizes (cliquePattern ell) (fun a => f a) := by
    refine ⟨f.strictMono,hIn,?_,?_,?_⟩
    · intro a b hab t
      fin_cases t
      have hEdge := hClique (f a) (s.orderEmbOfFin_mem hCard a)
        (f b) (s.orderEmbOfFin_mem hCard b)
        (fun h => hab (f.injective h))
      simpa [cliquePattern, hab] using hEdge
    · intro a t
      exact Fin.elim0 t
    · intro a t
      fin_cases t
      simpa [cliquePattern] using oneGap_diag_false_of_avoid ell hell C
        hAvoid (f a) (hIn a)
  have hm : NormalizedForbidden.nontrivial ell (cliquePattern ell)
      (by omega) (cliquePattern_irreducible ell) ∈
        hensonForbiddenFamily ell hell := by
    simp [hensonForbiddenFamily]
  exact hAvoid _ hm ⟨fun a => f a,hCopy⟩

theorem oneGap_clique_copy_checker_true
    (ell : Nat) (C : AgeTestModel 1 0 1)
    (e : Fin ell → Nat) (hCopy : C.Realizes (cliquePattern ell) e)
    (P : Finset Nat) (hP : ∀ a, e a ∈ P) :
    finitePoolCliqueCheck (fun x y => C.binary x y (0 : Fin 1)) ell P = true := by
  classical
  let s : Finset Nat := Finset.univ.image e
  apply (finitePoolCliqueCheck_true_iff _ ell P).2
  refine ⟨s,?_,?_,?_⟩
  · intro x hx
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
    exact hP a
  · have hc := Finset.card_image_of_injective (Finset.univ : Finset (Fin ell))
        hCopy.1.injective
    simpa [s] using hc
  · intro x hx y hy hxy
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hy
    have hab : a ≠ b := fun h => hxy (congrArg e h)
    simpa [cliquePattern,hab] using hCopy.2.2.1 a b hab (0 : Fin 1)

theorem oneGap_rawBound_congr_old
    (G H : Nat → Nat → Bool) (ell d : Nat)
    (P : Finset Nat) (col : Nat → Fin d → Bool)
    (hOld : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → G x y = H x y) :
    finiteOldColumnRawBound G ell d P col =
      finiteOldColumnRawBound H ell d P col := by
  classical
  funext T
  let U := oldSupportCommonNeighbourPool P col T.1
  have hSub : U ⊆ P := Finset.filter_subset _ _
  have hCap := finiteDirectedCliqueCapacity_induced_image_eq
    G H U (fun x => x) (by intro x hx y hy h; exact h)
    (fun x hx y hy hxy => hOld x (hSub hx) y (hSub hy) hxy)
  have hCap' : finiteDirectedCliqueCapacity H U =
      finiteDirectedCliqueCapacity G U := by simpa using hCap
  change ell - 1 - finiteDirectedCliqueCapacity G U =
    ell - 1 - finiteDirectedCliqueCapacity H U
  rw [hCap']

/-- Arbitrary upper-upper atoms are retained. We only label the
upper vertices of the forbidden clique by their exact selected
terminal types; the label map need not be injective. -/
theorem oneGap_no_new_clique_of_equal_selected_age
    (ell : Nat) (hell : 2 ≤ ell) (d cut : Nat) (hd : 0 < d)
    (C W : AgeTestModel 1 0 1)
    (selected : Fin d → Nat)
    (hAvoidC : ∀ bad, bad ∈ hensonForbiddenFamily ell hell → bad.Avoids C)
    (hCcarrier : ∀ x ≤ cut, x ∈ C.carrier)
    (hSym : ∀ x y, C.binary x y (0 : Fin 1) = C.binary y x (0 : Fin 1))
    (hSocle : SameInitialL W C cut)
    (hDelete : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (W.withoutVertex cut))
    (hUpperPositive : ∀ x, x ∈ W.carrier → cut < x →
      W.binary cut x (0 : Fin 1) = true →
      ∃ j : Fin d, RelationalPrefixType.ofAgeModel W (cut+1) x =
        RelationalPrefixType.ofAgeModel C (cut+1) (selected j))
    (hAge : ∀ T : IntegerGraphSupport d ell,
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound (fun x y => C.binary x y 0) ell d
          (Finset.range cut) (fun p j => C.binary p (selected j) 0)) T =
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound (fun x y => C.binary x y 0) ell d
          (Finset.range (cut+1)) (fun p j => C.binary p (selected j) 0)) T) :
    ¬ ∃ e : Fin ell → Nat, W.Realizes (cliquePattern ell) e := by
  classical
  rintro ⟨e,hCopy⟩
  have hMem : NormalizedForbidden.nontrivial ell (cliquePattern ell)
      (by omega) (cliquePattern_irreducible ell) ∈ hensonForbiddenFamily ell hell := by
    simp [hensonForbiddenFamily]
  have hAt : ∃ a : Fin ell, e a = cut := by
    by_contra hn
    exact hDelete _ hMem ⟨e,
      AgeTestModel.realizes_restrictCarrier W (fun x => x ≠ cut)
        (cliquePattern ell) e hCopy (fun a ha => hn ⟨a,ha⟩)⟩
  obtain ⟨a0,ha0⟩ := hAt
  let P := Finset.range cut
  let Q := Finset.range (cut+1)
  let U := (Finset.univ.image e).filter (fun x => cut < x)
  let gW : Nat → Nat → Bool := fun x y => W.binary x y 0
  let gC : Nat → Nat → Bool := fun x y => C.binary x y 0
  let col : Nat → Fin d → Bool := fun p j => C.binary p (selected j) 0
  have hUType : ∀ x ∈ U, ∃ j : Fin d,
      RelationalPrefixType.ofAgeModel W (cut+1) x =
        RelationalPrefixType.ofAgeModel C (cut+1) (selected j) := by
    intro x hx
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hx).1
    have hAbove := (Finset.mem_filter.mp hx).2
    have hNe : a0 ≠ a := by
      intro h
      rw [h] at ha0
      omega
    have hEdge := hCopy.2.2.1 a0 a hNe (0 : Fin 1)
    have hBit : W.binary cut x (0 : Fin 1) = true := by
      simpa [ha0,ha,cliquePattern,hNe] using hEdge
    apply hUpperPositive x
    · rw [← ha]
      exact hCopy.2.1 a
    · exact hAbove
    · exact hBit
  let sort : Nat → Fin d :=
    fun x => if hx : x ∈ U then Classical.choose (hUType x hx) else ⟨0,hd⟩
  have hSort : ∀ x ∈ U, RelationalPrefixType.ofAgeModel W (cut+1) x =
      RelationalPrefixType.ofAgeModel C (cut+1) (selected (sort x)) := by
    intro x hx
    simpa [sort,hx] using Classical.choose_spec (hUType x hx)
  have hDisjointQ : Disjoint Q U := by
    apply Finset.disjoint_left.mpr
    intro x hxQ hxU
    have h1 : x < cut+1 := Finset.mem_range.mp hxQ
    have h2 := (Finset.mem_filter.mp hxU).2
    omega
  have hDisjointP : Disjoint P U := by
    apply Finset.disjoint_left.mpr
    intro x hxP hxU
    have h1 : x < cut := Finset.mem_range.mp hxP
    have h2 := (Finset.mem_filter.mp hxU).2
    omega
  have hColumnsQ : ∀ p ∈ Q, ∀ w ∈ U,
      gW p w = col p (sort w) ∧ gW w p = col p (sort w) := by
    intro p hp w hw
    have hp' : p < cut+1 := Finset.mem_range.mp hp
    have hf := congrArg (fun T : RelationalPrefixType (cut+1) 1 0 1 =>
      T.binary (some (⟨p,hp'⟩ : Fin (cut+1))) none (0 : Fin 1))
      (hSort w hw)
    have hb := congrArg (fun T : RelationalPrefixType (cut+1) 1 0 1 =>
      T.binary none (some (⟨p,hp'⟩ : Fin (cut+1))) (0 : Fin 1))
      (hSort w hw)
    change gW p w = col p (sort w) at hf
    change gW w p = C.binary (selected (sort w)) p 0 at hb
    exact ⟨hf,hb.trans (hSym _ _)⟩
  have hPsubQ : P ⊆ Q := by
    intro x hx
    apply Finset.mem_range.mpr
    have h := Finset.mem_range.mp hx
    omega
  have hColumnsP : ∀ p ∈ P, ∀ w ∈ U,
      gW p w = col p (sort w) ∧ gW w p = col p (sort w) :=
    fun p hp => hColumnsQ p (hPsubQ hp)
  have hBefore : finitePoolCliqueCheck gW ell (P ∪ U) = false := by
    change finitePoolCliqueCheck
      (fun x y => (W.withoutVertex cut).binary x y 0) ell (P ∪ U) = false
    apply oneGap_pool_free_of_avoid ell hell (W.withoutVertex cut)
      hDelete (P ∪ U)
    intro x hx
    rcases Finset.mem_union.mp hx with hp | hu
    · have hlt : x < cut := Finset.mem_range.mp hp
      exact ⟨(hSocle.1 x (by omega)).mpr (hCcarrier x (by omega)),
        by omega⟩
    · obtain ⟨a,_,ha⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hu).1
      have hIn : x ∈ W.carrier := by rw [← ha]; exact hCopy.2.1 a
      exact ⟨hIn,by
        have hlt := (Finset.mem_filter.mp hu).2
        omega⟩
  have hQFreeC : finitePoolCliqueCheck gC ell Q = false := by
    apply oneGap_pool_free_of_avoid ell hell C hAvoidC Q
    intro x hx
    exact hCcarrier x (by
      have hlt := Finset.mem_range.mp hx
      omega)
  have hOldQ : ∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → gW x y = gC x y := by
    intro x hx y hy _
    have hx' := Finset.mem_range.mp hx
    have hy' := Finset.mem_range.mp hy
    exact hSocle.2.1 x y (by omega) (by omega) 0
  have hQFree : finitePoolCliqueCheck gW ell Q = false := by
    apply (finitePoolCliqueCheck_false_iff_induced_image
      gW gC Q (fun x => x) (by intro x hx y hy h; exact h)
      hOldQ ell).2
    simpa using hQFreeC
  have hPFree : finitePoolCliqueCheck gW ell P = false := by
    apply (finitePoolCliqueCheck_false_iff gW ell P).2
    rintro ⟨s,hs,hCard,hClique⟩
    exact ((finitePoolCliqueCheck_false_iff gW ell Q).1 hQFree)
      ⟨s,hs.trans hPsubQ,hCard,hClique⟩
  have hRawQ := oneGap_rawBound_congr_old gW gC ell d Q col hOldQ
  have hRawP := oneGap_rawBound_congr_old gW gC ell d P col
    (fun x hx y hy hxy => hOldQ x (hPsubQ hx) y (hPsubQ hy) hxy)
  have hEqual : ∀ T : IntegerGraphSupport d ell,
      integerGraphAgeCanonical d ell (finiteOldColumnRawBound gW ell d P col) T =
      integerGraphAgeCanonical d ell (finiteOldColumnRawBound gW ell d Q col) T := by
    intro T
    rw [hRawP,hRawQ]
    exact hAge T
  have hAfter := oneGap_continuation_of_equal_canonical_age
    gW ell d P Q U sort col hDisjointP hDisjointQ hColumnsP hColumnsQ
    hPFree hQFree hEqual hBefore
  have hBad := oneGap_clique_copy_checker_true ell W e hCopy (Q ∪ U)
    (by
      intro a
      by_cases ha : e a ≤ cut
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_range.mpr (by omega)))
      · apply Finset.mem_union.mpr
        right
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩,by omega⟩)
  change finitePoolCliqueCheck gW ell (Q ∪ U) = true at hBad
  rw [hAfter] at hBad
  contradiction

/-- The genuine FULL corrected B3 predicate; no assumed equality of
full and selected upper-type spectra. -/
theorem oneGap_correctedB3_of_equal_selected_age
    (ell : Nat) (hell : 2 ≤ ell) (d cut : Nat) (hd : 0 < d)
    (A : EnumeratedPartialStructure 1 0 1) (hCut : cut < A.size)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell → bad.Avoids A.L)
    (hSym : ∀ x y, A.L.binary x y (0 : Fin 1) = A.L.binary y x (0 : Fin 1))
    (F : PrescribedBoringData cut 1 0 1)
    (selected : Fin d → Nat)
    (hRepresented : ∀ T, T ∈ F.source →
      ∃ v : Nat, F.target T = A.partialTypeAt (cut+1) v ∧
        (A.L.binary cut v 0 = true → ∃ j : Fin d, v = selected j))
    (hAge : ∀ T : IntegerGraphSupport d ell,
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound (fun x y => A.L.binary x y 0) ell d
          (Finset.range cut) (fun p j => A.L.binary p (selected j) 0)) T =
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound (fun x y => A.L.binary x y 0) ell d
          (Finset.range (cut+1)) (fun p j => A.L.binary p (selected j) 0)) T) :
    F.CorrectedB3 (hensonForbiddenFamily ell hell) := by
  classical
  intro S hS W hFinite hSame hUpper hDelete bad hBad
  obtain ⟨v0,hv0,_⟩ := hRepresented S hS
  have hSocle' : SameInitialL (prescribedOrdinarySocle (F.target S)) A.L cut := by
    rw [hv0]
    exact ambient_partialType_prescribedSocle A cut v0 hCut
  have hSocle := hSame.trans hSocle'
  have hUpperNamed : ∀ x, x ∈ W.carrier → cut < x →
      ∃ v : Nat, RelationalPrefixType.ofAgeModel W (cut+1) x =
        RelationalPrefixType.ofAgeModel A.L (cut+1) v := by
    intro x hx ha
    obtain ⟨T,hT,hEq⟩ := hUpper x hx ha
    obtain ⟨v,hv,_⟩ := hRepresented T hT
    exact ⟨v, hEq.trans (congrArg PartialTypeWithE.lReduct hv)⟩
  have hPositive : ∀ x, x ∈ W.carrier → cut < x →
      W.binary cut x 0 = true →
      ∃ j : Fin d, RelationalPrefixType.ofAgeModel W (cut+1) x =
        RelationalPrefixType.ofAgeModel A.L (cut+1) (selected j) := by
    intro x hx ha hEdge
    obtain ⟨T,hT,hEq⟩ := hUpper x hx ha
    obtain ⟨v,hv,hSelected⟩ := hRepresented T hT
    have hType : RelationalPrefixType.ofAgeModel W (cut+1) x =
        RelationalPrefixType.ofAgeModel A.L (cut+1) v :=
      hEq.trans (congrArg PartialTypeWithE.lReduct hv)
    have hBit := congrArg (fun R : RelationalPrefixType (cut+1) 1 0 1 =>
      R.binary (some (⟨cut,Nat.lt_succ_self cut⟩ : Fin (cut+1)))
        none (0 : Fin 1)) hType
    change W.binary cut x 0 = A.L.binary cut v 0 at hBit
    obtain ⟨j,hj⟩ := hSelected (hBit.symm.trans hEdge)
    exact ⟨j,by rw [← hj]; exact hType⟩
  have hCarrier : ∀ x ≤ cut, x ∈ A.L.carrier :=
    fun x hx => (A.carrier_iff x).mpr (lt_of_le_of_lt hx hCut)
  have hNoClique := oneGap_no_new_clique_of_equal_selected_age
    ell hell d cut hd A.L W selected hAvoid hCarrier hSym hSocle
    hDelete hPositive hAge
  have hFM : NormalizedForbidden.nontrivial 2 forwardAsymPattern (by omega)
      forwardAsymPattern_irreducible ∈ hensonForbiddenFamily ell hell := by
    simp [hensonForbiddenFamily]
  have hBM : NormalizedForbidden.nontrivial 2 backwardAsymPattern (by omega)
      backwardAsymPattern_irreducible ∈ hensonForbiddenFamily ell hell := by
    simp [hensonForbiddenFamily]
  have hAsym := B3_avoids_both_asym_patterns A.L W cut hSocle
    (fun x => hSym cut x) hUpperNamed (hDelete _ hFM) (hDelete _ hBM)
  have hLM : NormalizedForbidden.singleton loopPattern loopPattern_nonNeutral ∈
      hensonForbiddenFamily ell hell := by simp [hensonForbiddenFamily]
  have hNoLoop : ¬ ∃ e : Fin 1 → Nat, W.Realizes loopPattern e := by
    rintro ⟨e,he⟩
    by_cases hAt : e 0 = cut
    · have hDiag := he.2.2.2.2 (0 : Fin 1) (0 : Fin 1)
      have hZero := (hSocle.2.2.2 cut le_rfl (0 : Fin 1)).trans
        (oneGap_diag_false_of_avoid ell hell A.L hAvoid cut (hCarrier cut le_rfl))
      simp [loopPattern,hAt,hZero] at hDiag
    · exact hDelete _ hLM ⟨e,
        AgeTestModel.realizes_restrictCarrier W (fun x => x ≠ cut)
          loopPattern e he (by intro a; fin_cases a; exact hAt)⟩
  simp [hensonForbiddenFamily] at hBad
  rcases hBad with h | h | h | h
  · subst bad
    exact hNoLoop
  · subst bad
    exact hAsym.1
  · subst bad
    exact hAsym.2
  · subst bad
    exact hNoClique

end Kk
