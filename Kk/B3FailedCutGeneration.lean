import Kk.HensonZeroGenerationClique
import SuccessorTree.V10.I3ActualWitnessGeneration
import Mathlib.Tactic

/-!
# Track D: every failed selected-stage Henson corrected B3 has a non-top real cut

English-first proof and 18 hostile checks:
docs/audits/2026-11-15-track-d-failed-b3-lower-generation-english.md

An actual failed selected-source corrected-B3 test in a finite numerical H
forces the tested cut to equal hPosition k i g with g<k. This is a conclusion,
not a pre-existing cut-generation premise. The proof uses the whole finite
irreducible K_ell witness, its genuine selected eligible original next-cut
L type labels, and the checked numerical-H forbidden-copy relocation.

This is strictly corrected B3: top/odd cuts may still be required by I1/I2,
and no global diary or common labelled inverse-source orbit is claimed.
-/

namespace Kk

open SuccessorTree.V10

/-- A genuinely failed selected-stage corrected B3 in a finite Henson
numerical-H source forces the tested physical coordinate to be REAL
and strictly BELOW the top numerical generation.

No preset generation, positive-generation, no-(I2), selected-shadow age
or common-source hypothesis is required. Even generation zero is handled. -/
theorem henson_failed_selectedB3_forces_lower_real_generation
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N cut M : Nat) (hCut : cut < N)
    (original : Fin M → Fin N)
    (Selected : Fin M → Prop)
    (hFailure :
      ¬ (selectedStagePoolPrescribedData
        (finiteNumericH (normalizedGraphModel E) k N)
        cut original Selected).CorrectedB3
          (hensonForbiddenFamily ell hell)) :
    ∃ g idx : Nat, g < k ∧ cut = hPosition k idx g := by
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
      ⟨hLoops,hSym,hClique⟩
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
  have hUpperNamed : ∀ b : Fin ell, r ≤ b.val →
      ∃ address : Nat, cut < address ∧
        RelationalPrefixType.ofAgeModel W (cut+1) (e b) =
          RelationalPrefixType.ofAgeModel
            (finiteNumericHL K k N) (cut+1) address := by
    intro b hb
    have hAbove : cut < e b := (hHigh b).1 hb
    obtain ⟨v,hSelected,hFree,hType⟩ :=
      hUpper (e b) (hCopy.2.1 b) hAbove
    have hAddress : A.freeLevel (original v).val ≤
        (original v).val := A.freeLevel_le (original v).val
    have hAfter : cut < (original v).val :=
      lt_of_lt_of_le (Nat.lt_succ_self cut) (hFree.trans hAddress)
    exact ⟨(original v).val,hAfter,hType⟩
  obtain ⟨idx,hCutGeneration,_hHigher⟩ :=
    numericI3_actual_witness_generation_conclusions
      K k N cut r hr hrt hrk W hSocle
      (cliquePattern ell) hIrred e hCopy
      hDeleteP hLast hUpperNamed
  refine ⟨r-1,idx,by omega,?_⟩
  exact hCutGeneration

/-- Any genuine TOP-generation numerical-H coordinate passes the
selected-stage corrected B3 test for ANY selected original-name pool.

This is not a graph-theoretic statement about arbitrary abstract top
vertices: it relies on the complete earlier numerical-H old socle and
the forbidden-clique relocation theorem, not merely on the local
generation edge gate, which allows top-to-top binary edges. -/
theorem henson_numericH_top_generation_cut_correctedB3
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N idx M : Nat) (hCut : hPosition k idx k < N)
    (original : Fin M → Fin N)
    (Selected : Fin M → Prop) :
    (selectedStagePoolPrescribedData
      (finiteNumericH (normalizedGraphModel E) k N)
      (hPosition k idx k) original Selected).CorrectedB3
        (hensonForbiddenFamily ell hell) := by
  classical
  by_contra hFailure
  obtain ⟨g,j,hg,hGen⟩ :=
    henson_failed_selectedB3_forces_lower_real_generation
      ell hell k hK E hLoops hSym hClique
      N (hPosition k idx k) M hCut original Selected hFailure
  have hEqual : k = g :=
    (hPosition_injective_bounded k idx k j g le_rfl
      (Nat.le_of_lt hg) hGen).2
  omega

#print axioms henson_failed_selectedB3_forces_lower_real_generation
#print axioms henson_numericH_top_generation_cut_correctedB3

end Kk
