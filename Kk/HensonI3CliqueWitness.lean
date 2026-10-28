import Kk.HensonI3PatternSize
import SuccessorTree.V10.I3ActualHigherSignature
import Mathlib.Tactic

/-!
# Positive-generation Henson B3 failures use a forbidden clique

The true normalized K_ell-free language has FOUR forbidden patterns:
a loop singleton, two asymmetric ordered pairs, and K_ell.
The latter is the only one with at least three vertices.

The checked I3 forbidden-copy relocation says an actual selected-pool
B3 failure at H generation g comes from a forbidden pattern with
r=g+1 lower vertices and at least one upper vertex, hence with at
least g+2 vertices. Therefore for g>0 the forbidden pattern must
be K_ell, even though the FULL age test is in the directed normalized
signature.

This proves more than the previous g<=ell-2 cutoff: all positive-
generation failures are genuine clique failures, not asymmetry
or loop failures. It does NOT project their auxiliary upper types
onto selected diary branches; the full parameter-closure invariant
is still required for that application.
-/

namespace Kk

open SuccessorTree.V10

/-- The clique pattern is the only member of the normalized
K_ell-free forbidden list with at least three vertices. -/
theorem henson_forbidden_pattern_large_is_clique
    (ell : Nat) (hell : 2 ≤ ell)
    (bad : NormalizedForbidden 1 0 1)
    (hMem : bad ∈ hensonForbiddenFamily ell hell)
    (hLarge : 3 ≤ bad.patternCard) :
    bad = .nontrivial ell (cliquePattern ell) (by omega)
      (cliquePattern_irreducible ell) := by
  simp [hensonForbiddenFamily] at hMem
  rcases hMem with h | h | h | h
  · rw [h] at hLarge
    simp [NormalizedForbidden.patternCard] at hLarge
  · rw [h] at hLarge
    simp [NormalizedForbidden.patternCard] at hLarge
  · rw [h] at hLarge
    simp [NormalizedForbidden.patternCard] at hLarge
  · exact h

/-- An actual selected-original corrected B3 failure at a
POSITIVE H generation has a finite forbidden L-continuation
which fails avoidance of the symmetric K_ell pattern.

No extra E on the arbitrary finite age-test witness is assumed;
the exact pattern comes from the indexed normalized forbidden
family and the checked numerical H relocation theorem.

The witness W need not be the ambient numerical H itself:
its lower socle is the prescribed H initial segment and its
upper vertices realize the complete selected original types. -/
theorem henson_positive_generation_B3_has_clique_witness
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N cut g idx M : Nat)
    (hPositive : 0 < g) (hg : g < k)
    (hCut : cut < N)
    (hGeneration : cut = hPosition k idx g)
    (original : Fin M → Fin N)
    (Selected : Fin M → Prop)
    (hFailure :
      ¬ (selectedStagePoolPrescribedData
        (finiteNumericH (normalizedGraphModel E) k N)
        cut original Selected).CorrectedB3
          (hensonForbiddenFamily ell hell)) :
    ∃ W : AgeTestModel 1 0 1,
      W.BoundedCarrier ∧
      SameInitialL W
        (finiteNumericHL (normalizedGraphModel E) k N) cut ∧
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
  have hLarge : 3 ≤ (family.get i).patternCard := by omega
  have hBadClique :=
    henson_forbidden_pattern_large_is_clique
      ell hell (family.get i) hMember hLarge
  have hViolation :
      ¬ (NormalizedForbidden.nontrivial ell
        (cliquePattern ell) (by omega)
        (cliquePattern_irreducible ell)).Avoids W := by
    change ¬ (family.get i).Avoids W at hBad
    rw [hBadClique] at hBad
    exact hBad
  exact ⟨W,hFinite,hSocleH,hDelete,hUpper,hViolation⟩


/-- The forbidden-clique continuation can also be recorded as an
ACTUAL original-labelled I3 signature for the one-element
forbidden family consisting only of the clique pattern.

This proves the missing connection between the verified
positive-generation clique witness and the general fixed-pattern
signature-count theorem, without asserting that original names are
already restricted to the strictly higher-generation subpool. -/
theorem henson_positive_generation_B3_has_clique_signature
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N cut g idx M : Nat)
    (hPositive : 0 < g) (hg : g < k)
    (hCut : cut < N)
    (hGeneration : cut = hPosition k idx g)
    (original : Fin M → Fin N)
    (Selected : Fin M → Prop)
    (hFailure :
      ¬ (selectedStagePoolPrescribedData
        (finiteNumericH (normalizedGraphModel E) k N)
        cut original Selected).CorrectedB3
          (hensonForbiddenFamily ell hell)) :
    Nonempty (I3OriginalSignatureWitness
      (fun _ : Fin 1 => ell)
      (fun _ : Fin 1 => cliquePattern ell)
      (finiteNumericHL (normalizedGraphModel E) k N)
      (fun v : Fin M => (original v).val) cut) := by
  classical
  obtain ⟨W,hFinite,hSocle,hDelete,hUpper,hBad⟩ :=
    henson_positive_generation_B3_has_clique_witness
      ell hell k hK E hLoops hSym hClique
      N cut g idx M hPositive hg hCut hGeneration
      original Selected hFailure
  let bad : NormalizedForbidden 1 0 1 :=
    .nontrivial ell (cliquePattern ell) (by omega)
      (cliquePattern_irreducible ell)
  have hMember : bad ∈ hensonForbiddenFamily ell hell := by
    simp [bad,hensonForbiddenFamily]
  obtain ⟨e,hCopy⟩ :=
    bad.signaturePattern_copy_of_violation W hBad
  have hDeletePattern :
      ¬ ∃ f : Fin ell → Nat,
        (W.withoutVertex cut).Realizes (cliquePattern ell) f := by
    exact (bad.signaturePattern_avoids_iff
      (W.withoutVertex cut)).1 (hDelete bad hMember)
  refine ⟨{
    familyIndex := 0
    W := W
    e := e
    finite := hFinite
    copy := hCopy
    socle := hSocle
    deleteAvoids := hDeletePattern
    upperNames := ?_
  }⟩
  intro a hAbove
  obtain ⟨v,_hSelected,_hFree,hType⟩ :=
    hUpper (e a) (hCopy.2.1 a) hAbove
  exact ⟨v,hType⟩


end Kk
