import Kk.HensonAlgorithmRunHigherCapacity
import SuccessorTree.V10.I3ActualHigherSignature
import Mathlib.Tactic

/-!
# The forbidden-clique size restricts corrected B3 event generations

In the normalized K_ell-free signature the forbidden patterns have
sizes 1, 2, 2 and ell. The full finite L-only I3 age witness is a
genuine copy of one of THESE indexed family members, not an
arbitrary forbidden pattern of size up to the generation height k+1.

For a failed corrected B3 at a numerical H cut, the exact
relocation theorem gives that the tested generation g equals
r-1, where r is the number of lower vertices in the forbidden
copy. Since r is a proper nonempty initial segment and the
forbidden family member has at most ell vertices, g+2<=ell.

This prohibits selected-stage B3 failures at generation
g>=ell-1 EVEN WHEN the numerical H construction uses k=ell,
as in the circulation manuscript. The theorem concerns the
genuine selected-original stage B3; the macro-diary projection
and equality of canonical labelled sources are still open.
-/

namespace Kk

open SuccessorTree.V10

/-- At every actual selected-original corrected-B3 failure at
numerical H generation g<k, the tested generation is at most
ell-2. The conclusion uses the exact Henson forbidden-family
pattern size ell, not merely the looser k+1 bound. -/
theorem henson_failedSelectedB3_generation_below_clique_margin
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N cut g idx M : Nat)
    (hg : g < k)
    (hCut : cut < N)
    (hGeneration : cut = hPosition k idx g)
    (original : Fin M → Fin N)
    (Selected : Fin M → Prop)
    (hFailure :
      ¬ (selectedStagePoolPrescribedData
        (finiteNumericH (normalizedGraphModel E) k N)
        cut original Selected).CorrectedB3
          (hensonForbiddenFamily ell hell)) :
    g+2 ≤ ell := by
  let family : List (NormalizedForbidden 1 0 1) :=
    hensonForbiddenFamily ell hell
  let K : AgeTestModel 1 0 1 := normalizedGraphModel E
  let A : EnumeratedPartialStructure 1 0 1 := finiteNumericH K k N
  have hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K :=
    (hensonForbiddenFamily_avoids_iff ell hell E).2
      ⟨hLoops,hSym,hClique⟩
  have hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L :=
    finiteNumericH_avoids_family family K
      (by intro n; trivial) k N hAvoidK
  have hFamilyBound : ∀ bad, bad ∈ family →
      bad.patternCard ≤ k+1 := by
    intro bad hb
    exact (hensonForbiddenFamily_patternCard_le ell hell bad hb).trans hK
  obtain ⟨S0,hS0,W,hFinite,hSocle,hDelete,hUpper,bad,hMember,hBad⟩ :=
    selectedStagePool_failedCorrectedB3_has_selected_original_witness
      family A cut hCut original Selected hFailure
  obtain ⟨j,hj,hGet⟩ := List.getElem_of_mem hMember
  let i : Fin family.length := ⟨j,hj⟩
  have hIndex : family.get i = bad := hGet
  subst bad
  have hSocleH : SameInitialL W (finiteNumericHL K k N) cut := hSocle
  obtain ⟨e,r,hr,hrt,hrk,hIrred,hCopy,hDeleteP,hLast,hLow,hHigh⟩ :=
    normalizedForbidden_bounded_signature_cut
      (finiteNumericHL K k N) W cut k (family.get i)
      (hFamilyBound (family.get i) hMember)
      hSocleH (hAvoidA (family.get i) hMember)
      (hDelete (family.get i) hMember) hBad
  have hUpperNamed : ∀ b : Fin (family.get i).patternCard, r ≤ b.val →
      ∃ originalAddress : Nat, cut < originalAddress ∧
        RelationalPrefixType.ofAgeModel W (cut+1) (e b) =
          RelationalPrefixType.ofAgeModel
            (finiteNumericHL K k N) (cut+1) originalAddress := by
    intro b hb
    have hAbove : cut < e b := (hHigh b).1 hb
    obtain ⟨v,hSel,hFree,hType⟩ :=
      hUpper (e b) (hCopy.2.1 b) hAbove
    have hAddress : A.freeLevel (original v).val ≤
        (original v).val := A.freeLevel_le (original v).val
    refine ⟨(original v).val,?_,hType⟩
    omega
  obtain ⟨iH,hGenerationLast,_hStrictUpper⟩ :=
    numericI3_actual_witness_generation_conclusions
      K k N cut r hr hrt hrk W hSocleH
      (family.get i).signaturePattern hIrred e hCopy
      hDeleteP hLast hUpperNamed
  have hGenEq : g = r-1 := by
    obtain ⟨_hBase,hRank⟩ :=
      hPosition_injective_bounded k idx g iH (r-1)
        (Nat.le_of_lt hg) (by omega)
        (hGeneration.symm.trans hGenerationLast)
    exact hRank
  have hSize : (family.get i).patternCard ≤ ell :=
    hensonForbiddenFamily_patternCard_le ell hell
      (family.get i) hMember
  omega

/-- At a selected-original B3 stage in numerical H, any cut at
generation g>=ell-1 is automatically corrected-B3 admissible
(regardless of whether k=ell or k=ell-1). -/
theorem henson_selectedB3_of_generation_ge_clique_margin
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N cut g idx M : Nat)
    (hg : g < k) (hLarge : ell-1 ≤ g)
    (hCut : cut < N)
    (hGeneration : cut = hPosition k idx g)
    (original : Fin M → Fin N)
    (Selected : Fin M → Prop) :
    (selectedStagePoolPrescribedData
      (finiteNumericH (normalizedGraphModel E) k N)
      cut original Selected).CorrectedB3
        (hensonForbiddenFamily ell hell) := by
  by_contra hFailure
  have hBound :=
    henson_failedSelectedB3_generation_below_clique_margin
      ell hell k hK E hLoops hSym hClique
      N cut g idx M hg hCut hGeneration original Selected hFailure
  omega

end Kk
