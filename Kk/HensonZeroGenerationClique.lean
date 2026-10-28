import Kk.HensonB3Asymmetry
import Kk.HensonI3CliqueWitness
import Mathlib.Tactic

/-!
# Clique-only selected B3 obstructions, including generation zero

At positive numerical-H generations the size/rank argument already forces
every corrected-B3 witness for the normalized Henson family to be a clique.
At generation zero it only forces a nontrivial pattern and may superficially
leave either directed asymmetric pair.

The actual H binary relation is symmetric whenever its base graph is symmetric:
the generation gate is orientation independent and both orientations copy the
corresponding base atom. Prescribing the COMPLETE upper L-types therefore
precludes creating an asymmetric pair across the tested cut, using
`B3_avoids_both_asym_patterns`. The singleton case is excluded by the
common-socle/nonempty-upper forbidden-witness theorem.

Thus the only possible obstruction at ANY generation is the K_ell clique.
This is a selected-original full-L corrected-B3 statement; no claim is made
about projection onto the diary's marked active shadow or common source.
-/

namespace Kk

open SuccessorTree.V10

/-- The literal numerical-H binary relation preserves base symmetry
on ALL pairs of numerical coordinates, including fake vertices. -/
theorem hNumericBinary_symmetric_of_base
    {d : Nat}
    (B : Nat → Nat → Fin d → Bool)
    (hSym : ∀ i j t, B i j t = B j i t)
    (k x y : Nat) (t : Fin d) :
    hNumericBinary B k x y t = hNumericBinary B k y x t := by
  have hSwap (u v : Nat) :
      HNumericCrossing B k u v t → HNumericCrossing B k v u t := by
    rintro ⟨i,j,q,m,hij,hq,hm,hgate,hdir⟩
    refine ⟨i,j,q,m,hij,hq,hm,hgate,?_⟩
    rcases hdir with ⟨hu,hv,hbit⟩ | ⟨hu,hv,hbit⟩
    · right
      refine ⟨hv,hu,?_⟩
      rw [← hSym i j t]
      exact hbit
    · left
      refine ⟨hv,hu,?_⟩
      rw [hSym i j t]
      exact hbit
  cases hxy : hNumericBinary B k x y t with
  | false =>
    cases hyx : hNumericBinary B k y x t with
    | false => rfl
    | true =>
      have hxtrue : hNumericBinary B k x y t = true :=
        (hNumericBinary_true_iff B k x y t).2
          (hSwap y x ((hNumericBinary_true_iff B k y x t).1 hyx))
      rw [hxy] at hxtrue
      contradiction
  | true =>
    cases hyx : hNumericBinary B k y x t with
    | false =>
      have hytrue : hNumericBinary B k y x t = true :=
        (hNumericBinary_true_iff B k y x t).2
          (hSwap x y ((hNumericBinary_true_iff B k x y t).1 hxy))
      rw [hyx] at hytrue
      contradiction
    | true => rfl

/-- For the actual finite numerical H constructed from a symmetric graph,
the directed binary bits agree on both orientations, also at a stage cut. -/
theorem henson_finiteNumericH_binary_symmetric
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k N x y : Nat) :
    (finiteNumericHL (normalizedGraphModel E) k N).binary x y (0 : Fin 1) =
      (finiteNumericHL (normalizedGraphModel E) k N).binary y x (0 : Fin 1) := by
  change hNumericBinary (normalizedGraphModel E).binary k x y (0 : Fin 1) =
    hNumericBinary (normalizedGraphModel E).binary k y x (0 : Fin 1)
  apply hNumericBinary_symmetric_of_base
  intro i j t
  fin_cases t
  change E i j = E j i
  exact hSym i j

/-- In the ACTUAL Henson selected-original corrected-B3 test, any
failure has a genuine finite L-only K_ell continuation witness.
No positive-generation hypothesis is needed: the two asymmetric
patterns are impossible by the symmetry of the prescribed complete
crossing, and the singleton is ruled out by the exact socle test.

The upper names include auxiliary originals selected by the full
parameter closure, not necessarily only the marked diary branches. -/
theorem henson_selectedB3_failure_has_clique_witness
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N cut M : Nat)
    (hCut : cut < N)
    (original : Fin M → Fin N)
    (Selected : Fin M → Prop)
    (hFailure :
      ¬ (selectedStagePoolPrescribedData
        (finiteNumericH (normalizedGraphModel E) k N)
        cut original Selected).CorrectedB3
          (hensonForbiddenFamily ell hell)) :
    ∃ W : AgeTestModel 1 0 1,
      W.BoundedCarrier ∧
      SameInitialL W (finiteNumericHL (normalizedGraphModel E) k N) cut ∧
      (∀ bad, bad ∈ hensonForbiddenFamily ell hell →
        bad.Avoids (W.withoutVertex cut)) ∧
      (∀ x, x ∈ W.carrier → cut < x →
        ∃ v : Fin M,
          Selected v ∧
          cut+1 ≤ (finiteNumericH (normalizedGraphModel E) k N).freeLevel
            (original v).val ∧
          RelationalPrefixType.ofAgeModel W (cut+1) x =
            RelationalPrefixType.ofAgeModel
              (finiteNumericHL (normalizedGraphModel E) k N)
              (cut+1) (original v).val) ∧
      ¬ (NormalizedForbidden.nontrivial ell
        (cliquePattern ell) (by omega)
        (cliquePattern_irreducible ell)).Avoids W := by
  classical
  let family : List (NormalizedForbidden 1 0 1) :=
    hensonForbiddenFamily ell hell
  let K : AgeTestModel 1 0 1 := normalizedGraphModel E
  let A : EnumeratedPartialStructure 1 0 1 := finiteNumericH K k N
  have hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K :=
    (hensonForbiddenFamily_avoids_iff ell hell E).2
      ⟨hLoops,hSym,hClique⟩
  have hAvoidA : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericHL K k N) :=
    finiteNumericH_avoids_family family K
      (by intro i; trivial) k N hAvoidK
  obtain ⟨S0,hS0,W,hFinite,hSocle,hDelete,hUpper,bad,hMember,hBad⟩ :=
    selectedStagePool_failedCorrectedB3_has_selected_original_witness
      family A cut hCut original Selected hFailure
  have hBound : bad.patternCard ≤ k+1 :=
    (hensonForbiddenFamily_patternCard_le ell hell bad hMember).trans hK
  obtain ⟨_e,_r,hr,hrt,_hrk,_hIrred,_hCopy,_hDeleteP,
      _hLast,_hLow,_hHigh⟩ :=
    normalizedForbidden_bounded_signature_cut
      (finiteNumericHL K k N) W cut k bad hBound
      hSocle (hAvoidA bad hMember) (hDelete bad hMember) hBad
  have hNotSingleton : 1 < bad.patternCard := by omega
  have hCrossSym : ∀ x : Nat,
      (finiteNumericHL K k N).binary cut x (0 : Fin 1) =
        (finiteNumericHL K k N).binary x cut (0 : Fin 1) := by
    intro x
    exact henson_finiteNumericH_binary_symmetric E hSym k N cut x
  have hUpperNamed : ∀ x, x ∈ W.carrier → cut < x →
      ∃ address : Nat,
        RelationalPrefixType.ofAgeModel W (cut+1) x =
          RelationalPrefixType.ofAgeModel
            (finiteNumericHL K k N) (cut+1) address := by
    intro x hx hAbove
    obtain ⟨v,_hSel,_hFree,hType⟩ := hUpper x hx hAbove
    exact ⟨(original v).val,hType⟩
  have hForwardMem :
      (NormalizedForbidden.nontrivial 2 forwardAsymPattern (by omega)
        forwardAsymPattern_irreducible) ∈ family := by
    simp [family,hensonForbiddenFamily]
  have hBackwardMem :
      (NormalizedForbidden.nontrivial 2 backwardAsymPattern (by omega)
        backwardAsymPattern_irreducible) ∈ family := by
    simp [family,hensonForbiddenFamily]
  have hAvoidAsym :=
    B3_avoids_both_asym_patterns (finiteNumericHL K k N) W cut
      hSocle hCrossSym hUpperNamed
      (hDelete _ hForwardMem) (hDelete _ hBackwardMem)
  have hOnlyClique :
      bad = NormalizedForbidden.nontrivial ell
        (cliquePattern ell) (by omega)
        (cliquePattern_irreducible ell) := by
    simp [family,hensonForbiddenFamily] at hMember
    rcases hMember with h | h | h | h
    · rw [h] at hNotSingleton
      simp [NormalizedForbidden.patternCard] at hNotSingleton
    · rw [h] at hBad
      exact False.elim (hBad hAvoidAsym.1)
    · rw [h] at hBad
      exact False.elim (hBad hAvoidAsym.2)
    · exact h
  have hViolation :
      ¬ (NormalizedForbidden.nontrivial ell
        (cliquePattern ell) (by omega)
        (cliquePattern_irreducible ell)).Avoids W := by
    rw [hOnlyClique] at hBad
    exact hBad
  exact ⟨W,hFinite,hSocle,hDelete,hUpper,hViolation⟩

end Kk
