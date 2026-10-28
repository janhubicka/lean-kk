import Kk.HensonZeroGenerationClique
import SuccessorTree.V10.I3ChosenOriginalGeneration
import SuccessorTree.V10.I3ActualWitnessGeneration
import Mathlib.Tactic

/-!
# Fixed clique signature at every generation, including zero

At any numerical-H generation g, a failed selected-source
corrected B3 has a genuine K_ell forbidden clique witness. The
existing clique-only signature theorem retains the FULL original
name pool; the generic higher-generation signature theorem retains
the WHOLE forbidden-pattern family.

This file proves their desired intersection on the SAME finite
witness: it is a clique and every upper vertex of that witness
can be named by an actually selected original from generation m>g.
Thus it can be reindexed into the higher-generation subpool,
without losing the fixed forbidden pattern index.

All continued-age witnesses are finite L-only structures.
No E age witness, unproved Ramsey theorem, or macro-diary
factorisation is assumed.
-/

namespace Kk

open SuccessorTree.V10

/-- At a failed genuine selected-original B3 stage at any
generation g, one can choose an indexed I3 signature of the
single clique pattern whose upper names all lie in strictly
higher numerical-H generations. -/
theorem henson_any_generation_B3_has_clique_higher_signature
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
    ∃ w : I3OriginalSignatureWitness
        (fun _ : Fin 1 => ell)
        (fun _ : Fin 1 => cliquePattern ell)
        (finiteNumericHL (normalizedGraphModel E) k N)
        (fun v : Fin M => (original v).val) cut,
      ∀ a : Fin ell, cut < w.e a →
        ∃ v : Fin M,
          (∃ j m : Nat, g < m ∧ m ≤ k ∧
            (original v).val = hPosition k j m) ∧
          RelationalPrefixType.ofAgeModel w.W (cut+1) (w.e a) =
            RelationalPrefixType.ofAgeModel
              (finiteNumericHL (normalizedGraphModel E) k N)
              (cut+1) (original v).val := by
  classical
  let K : AgeTestModel 1 0 1 := normalizedGraphModel E
  let A : EnumeratedPartialStructure 1 0 1 := finiteNumericH K k N
  let family : List (NormalizedForbidden 1 0 1) :=
    hensonForbiddenFamily ell hell
  let bad : NormalizedForbidden 1 0 1 :=
    .nontrivial ell (cliquePattern ell) (by omega)
      (cliquePattern_irreducible ell)
  have hBadMem : bad ∈ family := by
    simp [bad, family, hensonForbiddenFamily]
  have hAvoidK : ∀ b, b ∈ family → b.Avoids K :=
    (hensonForbiddenFamily_avoids_iff ell hell E).2
      ⟨hLoops, hSym, hClique⟩
  have hAvoidA : ∀ b, b ∈ family →
      b.Avoids (finiteNumericHL K k N) :=
    finiteNumericH_avoids_family family K
      (by intro i; trivial) k N hAvoidK
  obtain ⟨W,hFinite,hSocle,hDelete,hUpper,hBad⟩ :=
    henson_selectedB3_failure_has_clique_witness
      ell hell k hK E hLoops hSym hClique
      N cut M hCut original Selected hFailure
  have hBound : bad.patternCard ≤ k+1 := by
    change ell ≤ k+1
    exact hK
  obtain ⟨e,r,hr,hrt,hrk,hIrred,hCopy,hDeleteP,
      hLast,hLow,hHigh⟩ :=
    normalizedForbidden_bounded_signature_cut
      (finiteNumericHL K k N) W cut k bad hBound
      hSocle (hAvoidA bad hBadMem)
      (hDelete bad hBadMem) hBad
  have hNamed : ∀ b : Fin ell, r ≤ b.val →
      ∃ v : Fin M,
        (Selected v ∧ cut+1 ≤ A.freeLevel (original v).val) ∧
        cut < (original v).val ∧
        RelationalPrefixType.ofAgeModel W (cut+1) (e b) =
          RelationalPrefixType.ofAgeModel
            (finiteNumericHL K k N) (cut+1) (original v).val := by
    intro b hb
    have hAbove : cut < e b := (hHigh b).1 hb
    obtain ⟨v,hSelected,hFree,hType⟩ :=
      hUpper (e b) (hCopy.2.1 b) hAbove
    have hAddress : A.freeLevel (original v).val ≤
        (original v).val := A.freeLevel_le (original v).val
    have hAfter : cut < (original v).val :=
      lt_of_lt_of_le (Nat.lt_succ_self cut) (hFree.trans hAddress)
    exact ⟨v,⟨hSelected,hFree⟩,hAfter,hType⟩
  have hUpperNamed : ∀ b : Fin ell, r ≤ b.val →
      ∃ address : Nat, cut < address ∧
        RelationalPrefixType.ofAgeModel W (cut+1) (e b) =
          RelationalPrefixType.ofAgeModel
            (finiteNumericHL K k N) (cut+1) address := by
    intro b hb
    obtain ⟨v,_hSelected,hAfter,hType⟩ := hNamed b hb
    exact ⟨(original v).val,hAfter,hType⟩
  obtain ⟨iH,hGenLast,_hUpperGeneration⟩ :=
    numericI3_actual_witness_generation_conclusions
      K k N cut r hr hrt hrk W hSocle
      (cliquePattern ell) hIrred e hCopy
      hDeleteP hLast hUpperNamed
  have hGenEq : g = r-1 := by
    obtain ⟨_hFirst,hRank⟩ :=
      hPosition_injective_bounded k idx g iH (r-1)
        (Nat.le_of_lt hg) (by omega)
        (hGeneration.symm.trans hGenLast)
    exact hRank
  have hChosenHigh :=
    numericI3_selected_named_originals_have_higher_generation
      K k N cut r hr hrt hrk W (cliquePattern ell)
      hIrred e hCopy hLast
      (fun v : Fin M => (original v).val)
      (fun v => Selected v ∧ cut+1 ≤ A.freeLevel (original v).val)
      hNamed ⟨iH,hGenLast⟩
  let w : I3OriginalSignatureWitness
      (fun _ : Fin 1 => ell)
      (fun _ : Fin 1 => cliquePattern ell)
      (finiteNumericHL K k N)
      (fun v : Fin M => (original v).val) cut := {
    familyIndex := 0
    W := W
    e := e
    finite := hFinite
    copy := hCopy
    socle := hSocle
    deleteAvoids := hDeleteP
    upperNames := by
      intro a ha
      obtain ⟨v,_j,_m,_hBoth,_hReal,_hStrict,_hm,hType⟩ :=
        hChosenHigh a ((hHigh a).2 ha)
      exact ⟨v,hType⟩
  }
  refine ⟨w,?_⟩
  intro a ha
  obtain ⟨v,j,m,_hBoth,hReal,hStrict,hm,hType⟩ :=
    hChosenHigh a ((hHigh a).2 ha)
  refine ⟨v,⟨j,m,?_,hm,hReal⟩,hType⟩
  omega

end Kk
