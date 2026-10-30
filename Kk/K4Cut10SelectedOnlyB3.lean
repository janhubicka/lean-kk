import Kk.K4ActualAlgorithmRunCut10
import Kk.HensonB3Asymmetry
import SuccessorTree.V10.I3AmbientSocleBridge
import Mathlib.Tactic

/-!
# The selected x-only K4 age test does not see the first gadget cut

At numerical-H cut 10 the FULL parameter-closed source contains the
auxiliary q2 original and the active x original; the actual AlgorithmRun
must retain this cut (verified in K4ActualAlgorithmRunCut10).

For comparison, suppose ONLY the complete upper L-type of x=38 is
allowed. The old socle 0,...,10 is edgeless. The old coordinate 8
has exactly the SAME positive crossing to all these x-type future
vertices as the tested coordinate 10, since both are even.

Any new four-clique through 10 would therefore have three future
vertices, and replacing 10 by 8 gives a forbidden four-clique after
deleting 10. Singleton loops and asymmetric ordered pairs cannot
appear at 10 because the whole initial L-socle is loopless and
symmetric and the complete x-type agrees with literal numerical H.

Thus the actual selected-only CommonSocleAgeTest at cut 10 PASSES
while the full two-type test FAILS. This supplies the precise
mathematical witness-projection obstruction: one cannot deduce
boringness of the full selected parameter closure from no change in
the selected one-sort age, even in the literal numerical-H example.

The theorem does not identify the example with a specific
globally resolved labelled diary or disprove a different repair.
-/

namespace Kk

open SuccessorTree.V10

/-- A complete old edgeless socle and one extra old clone of the
tested cut prohibit creating a *new* K4 using only one prescribed
upper type. The proof works in an arbitrary finite or infinite
L-only continuation, with no assumption on future-future edges. -/
theorem no_new_K4_of_earlier_clone
    (C W : AgeTestModel 1 0 1)
    (cut anchor original : Nat)
    (hAnchor : anchor < cut)
    (hSocle : SameInitialL W C cut)
    (hOldEmpty : ∀ x y, x ≤ cut → y ≤ cut →
      C.binary x y (0 : Fin 1) = false)
    (hAnchorCarrier : anchor ∈ C.carrier)
    (hAnchorForward : C.binary anchor original (0 : Fin 1) = true)
    (hAnchorBackward : C.binary original anchor (0 : Fin 1) = true)
    (hAnchorDiagonal : C.diagonal anchor (0 : Fin 1) = false)
    (hUpper : UpperTypesPrescribed W cut
      (fun R => R = RelationalPrefixType.ofAgeModel C (cut+1) original))
    (hDelete : ¬ ∃ e : Fin 4 → Nat,
      (W.withoutVertex cut).Realizes (cliquePattern 4) e) :
    ¬ ∃ e : Fin 4 → Nat, W.Realizes (cliquePattern 4) e := by
  classical
  rintro ⟨e,hCopy⟩
  have hWOld : ∀ x y, x ≤ cut → y ≤ cut →
      W.binary x y (0 : Fin 1) = false := by
    intro x y hx hy
    rw [hSocle.2.1 x y hx hy (0 : Fin 1)]
    exact hOldEmpty x y hx hy
  have hCut : ∃ a : Fin 4, e a = cut := by
    by_contra hn
    have hAway : ∀ a : Fin 4, e a ≠ cut := by
      intro a hEq
      exact hn ⟨a,hEq⟩
    have hCopyAway :=
      AgeTestModel.realizes_restrictCarrier W
        (fun x => x ≠ cut) (cliquePattern 4) e hCopy hAway
    exact hDelete ⟨e,hCopyAway⟩
  have hFirst : e 0 = cut := by
    obtain ⟨a,ha⟩ := hCut
    by_contra hn
    have ha0 : a ≠ 0 := by
      intro h
      subst a
      exact hn ha
    have h0a : (0 : Fin 4) < a := by
      have hPos : 0 < a.val := by
        have hNe : a.val ≠ 0 := by
          intro h
          exact ha0 (Fin.ext h)
        omega
      exact Fin.lt_def.mpr hPos
    have hLower : e 0 < cut := by
      have hlt := hCopy.1 h0a
      rw [ha] at hlt
      exact hlt
    have hEdge : W.binary (e 0) (e a) (0 : Fin 1) = true := by
      have h :=
        hCopy.2.2.1 (0 : Fin 4) a (ne_of_lt h0a) (0 : Fin 1)
      simpa [cliquePattern, ne_of_lt h0a] using h
    rw [ha, hWOld (e 0) cut (by omega) le_rfl] at hEdge
    cases hEdge
  have hFuture : ∀ a : Fin 4, a ≠ 0 → cut < e a := by
    intro a ha
    have hPos : (0 : Fin 4) < a := by
      have hNe : a.val ≠ 0 := by
        intro h
        exact ha (Fin.ext h)
      exact Fin.lt_def.mpr (by omega)
    have hlt := hCopy.1 hPos
    rw [hFirst] at hlt
    exact hlt
  have hWAnchor : anchor ∈ W.carrier :=
    (hSocle.1 anchor (by omega)).2 hAnchorCarrier
  have hWAnchorDiagonal : W.diagonal anchor (0 : Fin 1) = false := by
    rw [hSocle.2.2.2 anchor (by omega) (0 : Fin 1)]
    exact hAnchorDiagonal
  have hAnchorFuture :
      ∀ y, y ∈ W.carrier → cut < y →
        W.binary anchor y (0 : Fin 1) = true ∧
        W.binary y anchor (0 : Fin 1) = true := by
    intro y hy hyAbove
    have hType := hUpper y hy hyAbove
    have hForward := congrArg
      (fun T : RelationalPrefixType (cut+1) 1 0 1 =>
        T.binary (some (⟨anchor,by omega⟩ : Fin (cut+1)))
          none (0 : Fin 1)) hType
    have hBackward := congrArg
      (fun T : RelationalPrefixType (cut+1) 1 0 1 =>
        T.binary none
          (some (⟨anchor,by omega⟩ : Fin (cut+1)))
          (0 : Fin 1)) hType
    change W.binary anchor y (0 : Fin 1) =
      C.binary anchor original (0 : Fin 1) at hForward
    change W.binary y anchor (0 : Fin 1) =
      C.binary original anchor (0 : Fin 1) at hBackward
    exact ⟨hForward.trans hAnchorForward,
      hBackward.trans hAnchorBackward⟩
  let f : Fin 4 → Nat := fun a => if a = 0 then anchor else e a
  have hStrict : StrictMono f := by
    intro a b hab
    have hb0 : b ≠ 0 := by
      intro hb
      subst b
      exact (Fin.not_lt_zero _ hab).elim
    by_cases ha0 : a = 0
    · subst a
      have hgt := hFuture b hb0
      have hlt : anchor < e b := lt_trans hAnchor hgt
      simpa [f,hb0] using hlt
    · have hlt := hCopy.1 hab
      simpa [f,ha0,hb0] using hlt
  have hIn : ∀ a : Fin 4, f a ∈ (W.withoutVertex cut).carrier := by
    intro a
    change f a ∈ W.carrier ∧ f a ≠ cut
    by_cases ha0 : a = 0
    · subst a
      exact ⟨by simpa [f] using hWAnchor,
        by simp [f,ne_of_lt hAnchor]⟩
    · have haAbove := hFuture a ha0
      exact ⟨by simpa [f,ha0] using hCopy.2.1 a,
        by simpa [f,ha0] using (ne_of_gt haAbove)⟩
  have hBinary : ∀ a b : Fin 4, a ≠ b →
      W.binary (f a) (f b) (0 : Fin 1) = true := by
    intro a b hab
    by_cases ha0 : a = 0
    · subst a
      have hb0 : b ≠ 0 := by
        intro h
        exact hab h.symm
      have hAdj := (hAnchorFuture (e b)
        (hCopy.2.1 b) (hFuture b hb0)).1
      simpa [f,hb0] using hAdj
    · by_cases hb0 : b = 0
      · subst b
        have hAdj := (hAnchorFuture (e a)
          (hCopy.2.1 a) (hFuture a ha0)).2
        simpa [f,ha0] using hAdj
      · have h := hCopy.2.2.1 a b hab (0 : Fin 1)
        have hh : W.binary (e a) (e b) (0 : Fin 1) = true := by
          simpa [cliquePattern,hab] using h
        simpa [f,ha0,hb0] using hh
  have hCopyAway : (W.withoutVertex cut).Realizes
      (cliquePattern 4) f := by
    refine ⟨hStrict,hIn,?_,?_,?_⟩
    · intro a b hab t
      fin_cases t
      change W.binary (f a) (f b) (0 : Fin 1) =
        decide (a ≠ b)
      rw [hBinary a b hab]
      simp [hab]
    · intro a t
      exact Fin.elim0 t
    · intro a t
      fin_cases t
      change W.diagonal (f a) (0 : Fin 1) = false
      by_cases ha0 : a = 0
      · subst a
        simpa [f] using hWAnchorDiagonal
      · have h := hCopy.2.2.2.2 a (0 : Fin 1)
        simpa [cliquePattern,f,ha0] using h
  exact hDelete ⟨f,hCopyAway⟩

/-- The selected x-only corrected B3 test at the first reserved
microcut 10 is TRUE. This uses the complete old H socle and all
directed upper x L-atoms, not an abstract one-sort rank estimate. -/
theorem k4Gadget_cut10_x_only_B3_good :
    CommonSocleAgeTest k4GadgetFamily
      (prescribedOrdinarySocle (k4GadgetH.partialTypeAt 11 38))
      10
      (fun T => T = (k4GadgetH.partialTypeAt 11 38).lReduct) := by
  intro W hFinite hSame hUpper hDelete bad hBad
  have hFromType : SameInitialL
      (prescribedOrdinarySocle (k4GadgetH.partialTypeAt 11 38))
      k4GadgetH.L 10 :=
    ambient_partialType_prescribedSocle k4GadgetH 10 38 (by decide)
  have hSocle : SameInitialL W k4GadgetH.L 10 :=
    hSame.trans hFromType
  have hCrossSym : ∀ x,
      k4GadgetH.L.binary 10 x (0 : Fin 1) =
        k4GadgetH.L.binary x 10 (0 : Fin 1) := by
    intro x
    exact henson_finiteNumericH_binary_symmetric
      k4FourOriginalEdge k4FourOriginalEdge_symmetric 4 40 10 x
  have hUpperWitness : ∀ x, x ∈ W.carrier → 10 < x →
      ∃ original, RelationalPrefixType.ofAgeModel W 11 x =
        RelationalPrefixType.ofAgeModel k4GadgetH.L 11 original := by
    intro x hx hAbove
    exact ⟨38,hUpper x hx hAbove⟩
  have hNoAsym := B3_avoids_both_asym_patterns
    k4GadgetH.L W 10 hSocle hCrossSym hUpperWitness
    (hDelete (.nontrivial 2 forwardAsymPattern (by decide)
      forwardAsymPattern_irreducible)
      (by simp [k4GadgetFamily,hensonForbiddenFamily]))
    (hDelete (.nontrivial 2 backwardAsymPattern (by decide)
      backwardAsymPattern_irreducible)
      (by simp [k4GadgetFamily,hensonForbiddenFamily]))
  simp [k4GadgetFamily,hensonForbiddenFamily] at hBad
  rcases hBad with h | h | h | h
  · rw [h]
    change ¬ ∃ e : Fin 1 → Nat, W.Realizes loopPattern e
    rintro ⟨e,hCopy⟩
    by_cases hAt : e 0 = 10
    · have hDiag := hCopy.2.2.2.2 (0 : Fin 1) (0 : Fin 1)
      have hWDiag : W.diagonal 10 (0 : Fin 1) = false := by
        rw [hSocle.2.2.2 10 le_rfl (0 : Fin 1)]
        exact k4H_all_diagonals_false 10
      change W.diagonal (e 0) (0 : Fin 1) = true at hDiag
      rw [hAt,hWDiag] at hDiag
      cases hDiag
    · have hAway : ∀ a : Fin 1, e a ≠ 10 := by
        intro a
        fin_cases a
        exact hAt
      have hCopyDelete :=
        AgeTestModel.realizes_restrictCarrier W
          (fun x => x ≠ 10) loopPattern e hCopy hAway
      exact (hDelete (.singleton loopPattern loopPattern_nonNeutral)
        (by simp [k4GadgetFamily,hensonForbiddenFamily]))
        ⟨e,hCopyDelete⟩
  · rw [h]
    exact hNoAsym.1
  · rw [h]
    exact hNoAsym.2
  · rw [h]
    apply no_new_K4_of_earlier_clone k4GadgetH.L W 10 8 38
      (by decide) hSocle
    · intro x y hx hy
      exact k4H_cut10_old_binary_false x y hx hy
    · change 8 < 40
      decide
    · change (finiteNumericHL
        (normalizedGraphModel k4FourOriginalEdge) 4 40).binary
        8 38 (0 : Fin 1) = true
      rw [k4H_upper_edge_eq 8 (by decide)]
      decide
    · change (finiteNumericHL
        (normalizedGraphModel k4FourOriginalEdge) 4 40).binary
        38 8 (0 : Fin 1) = true
      rw [k4H_upper_edge_reverse_eq 8 (by decide)]
      decide
    · exact k4H_all_diagonals_false 8
    · exact hUpper
    · exact (hDelete
        (.nontrivial 4 (cliquePattern 4) (by decide)
          (cliquePattern_irreducible 4))
        (by simp [k4GadgetFamily,hensonForbiddenFamily]))

end Kk
