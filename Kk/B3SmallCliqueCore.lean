import Kk.B3ReductProfile
import Kk.HensonZeroGenerationClique
import SuccessorTree.V10.LocalAgeForbiddenTest
import Mathlib.Tactic

/-!
# Shrink a corrected-B3 Henson clique obstruction to its forbidden core

Even after restricting to the normalized symmetric K_ell forbidden
pattern, the finite age-test continuation W supplied by a failed B3
test may have many unrelated future vertices. The test is hereditary
under restrictions of the carrier, and an upper vertex's complete
L-type over the initial socle is unchanged under deleting other
future vertices.

Thus W can be replaced by its whole lower socle plus precisely the
upper vertices of ONE forbidden K_ell. This yields at most ell-1
future vertices (the tested cut itself lies in the clique). All
upper types remain named by actually selected originals, including
their exact numerical H free-cut guards. No auxiliary E values are
invented for the L-only continuation.

This helps narrow the remaining diary witness-projection task to
clique cores involving at most ell-1 full parameter-closed upper
names. It does NOT prove that these names belong to active diary
branches, nor that the canonical gadgets project those witnesses.
-/

namespace Kk

open SuccessorTree.V10

/-- Removing future vertices cannot introduce an age obstruction
after deleting the tested cut: every forbidden copy in the smaller
L-structure is also a forbidden copy in the original deletion. -/
theorem normalized_avoid_without_of_future_restriction
    {db du dd : Nat}
    (W : AgeTestModel db du dd)
    (cut : Nat) (P : Nat → Prop)
    (bad : NormalizedForbidden db du dd)
    (hAvoid : bad.Avoids (W.withoutVertex cut)) :
    bad.Avoids ((W.restrictCarrier P).withoutVertex cut) := by
  cases bad with
  | singleton F hNonNeutral =>
      change ¬ ∃ e : Fin 1 → Nat,
        (W.withoutVertex cut).Realizes F e at hAvoid
      change ¬ ∃ e : Fin 1 → Nat,
        ((W.restrictCarrier P).withoutVertex cut).Realizes F e
      rintro ⟨e,hCopy⟩
      have hNotCut : ∀ a : Fin 1, e a ≠ cut := by
        intro a
        exact (hCopy.2.1 a).2
      have hRestricted : (W.restrictCarrier P).Realizes F e :=
        AgeTestModel.realizes_of_restrictCarrier
          (W.restrictCarrier P) (fun x => x ≠ cut) F e hCopy
      have hOriginal : W.Realizes F e :=
        AgeTestModel.realizes_of_restrictCarrier
          W P F e hRestricted
      exact hAvoid ⟨e,
        AgeTestModel.realizes_restrictCarrier
          W (fun x => x ≠ cut) F e hOriginal hNotCut⟩
  | nontrivial r F hr hIrred =>
      change ¬ ∃ e : Fin r → Nat,
        (W.withoutVertex cut).Realizes F e at hAvoid
      change ¬ ∃ e : Fin r → Nat,
        ((W.restrictCarrier P).withoutVertex cut).Realizes F e
      rintro ⟨e,hCopy⟩
      have hNotCut : ∀ a : Fin r, e a ≠ cut := by
        intro a
        exact (hCopy.2.1 a).2
      have hRestricted : (W.restrictCarrier P).Realizes F e :=
        AgeTestModel.realizes_of_restrictCarrier
          (W.restrictCarrier P) (fun x => x ≠ cut) F e hCopy
      have hOriginal : W.Realizes F e :=
        AgeTestModel.realizes_of_restrictCarrier
          W P F e hRestricted
      exact hAvoid ⟨e,
        AgeTestModel.realizes_restrictCarrier
          W (fun x => x ≠ cut) F e hOriginal hNotCut⟩

/-- One failing genuine selected-stage corrected-B3 test has a
finite forbidden core W whose only vertices ABOVE the tested cut
are drawn from ONE marked K_ell copy. The copy contains the cut,
so there are at most ell-1 upper vertices.

Each remaining upper type still has the full L-type of a selected
original with the exact cut+1 free-level eligibility. This is
stronger than merely extracting a forbidden e inside an unbounded
continuation, and it is valid at generation zero as well. -/
theorem henson_selectedB3_failure_has_small_clique_core
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
    ∃ (V : AgeTestModel 1 0 1) (e : Fin ell → Nat),
      V.BoundedCarrier ∧
      SameInitialL V
        (finiteNumericHL (normalizedGraphModel E) k N) cut ∧
      (∀ bad, bad ∈ hensonForbiddenFamily ell hell →
        bad.Avoids (V.withoutVertex cut)) ∧
      (∀ x, x ∈ V.carrier → cut < x →
        ∃ v : Fin M,
          Selected v ∧
          cut+1 ≤ (finiteNumericH (normalizedGraphModel E) k N).freeLevel
            (original v).val ∧
          RelationalPrefixType.ofAgeModel V (cut+1) x =
            RelationalPrefixType.ofAgeModel
              (finiteNumericHL (normalizedGraphModel E) k N)
              (cut+1) (original v).val) ∧
      V.Realizes (cliquePattern ell) e ∧
      (∃ a : Fin ell, e a = cut) ∧
      (∀ x, x ∈ V.carrier → cut < x →
        ∃ a : Fin ell, e a = x) := by
  classical
  obtain ⟨W,hFinite,hSocle,hDelete,hUpper,hBad⟩ :=
    henson_selectedB3_failure_has_clique_witness
      ell hell k hK E hLoops hSym hClique
      N cut M hCut original Selected hFailure
  have hCliqueCopy : ∃ e : Fin ell → Nat,
      W.Realizes (cliquePattern ell) e := by
    change ¬ ¬ ∃ e : Fin ell → Nat,
      W.Realizes (cliquePattern ell) e at hBad
    exact not_not.mp hBad
  obtain ⟨e,hCopy⟩ := hCliqueCopy
  have hCliqueMember :
      (NormalizedForbidden.nontrivial ell
        (cliquePattern ell) (by omega)
        (cliquePattern_irreducible ell)) ∈
        hensonForbiddenFamily ell hell := by
    simp [hensonForbiddenFamily]
  have hNoCliqueDelete : ¬ ∃ f : Fin ell → Nat,
      (W.withoutVertex cut).Realizes (cliquePattern ell) f := by
    exact (NormalizedForbidden.nontrivial ell
      (cliquePattern ell) (by omega)
      (cliquePattern_irreducible ell)).signaturePattern_avoids_iff
        (W.withoutVertex cut) |>.mp
          (hDelete _ hCliqueMember)
  have hAt : ∃ a : Fin ell, e a = cut := by
    by_contra hn
    have hAway : ∀ a : Fin ell, e a ≠ cut := by
      intro a ha
      exact hn ⟨a,ha⟩
    exact hNoCliqueDelete ⟨e,
      AgeTestModel.realizes_restrictCarrier W (fun x => x ≠ cut)
        (cliquePattern ell) e hCopy hAway⟩
  let P : Nat → Prop := forbiddenWitnessCarrier cut e
  let V : AgeTestModel 1 0 1 := W.restrictCarrier P
  have hBelow : ∀ x, x ≤ cut → P x := by
    intro x hx
    exact Or.inl hx
  have hSocleV : SameInitialL V
      (finiteNumericHL (normalizedGraphModel E) k N) cut :=
    hSocle.restrictCarrier P hBelow
  have hFiniteV : V.BoundedCarrier := by
    obtain ⟨b,hb⟩ := hFinite
    refine ⟨b,?_⟩
    intro x hx
    exact hb x hx.1
  have hDeleteV : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (V.withoutVertex cut) := by
    intro bad hMember
    exact normalized_avoid_without_of_future_restriction
      W cut P bad (hDelete bad hMember)
  have hUpperV : ∀ x, x ∈ V.carrier → cut < x →
      ∃ v : Fin M,
        Selected v ∧
        cut+1 ≤ (finiteNumericH (normalizedGraphModel E) k N).freeLevel
          (original v).val ∧
        RelationalPrefixType.ofAgeModel V (cut+1) x =
          RelationalPrefixType.ofAgeModel
            (finiteNumericHL (normalizedGraphModel E) k N)
            (cut+1) (original v).val := by
    intro x hx hAbove
    exact hUpper x hx.1 hAbove
  have hCopyV : V.Realizes (cliquePattern ell) e := by
    apply AgeTestModel.realizes_restrictCarrier W P
      (cliquePattern ell) e hCopy
    intro a
    by_cases hle : e a ≤ cut
    · exact Or.inl hle
    · exact Or.inr ⟨a,rfl,by omega⟩
  have hFuture : ∀ x, x ∈ V.carrier → cut < x →
      ∃ a : Fin ell, e a = x := by
    intro x hx hAbove
    rcases hx.2 with hBelow' | ⟨a,ha,_hx⟩
    · omega
    · exact ⟨a,ha⟩
  exact ⟨V,e,hFiniteV,hSocleV,hDeleteV,
    hUpperV,hCopyV,hAt,hFuture⟩

end Kk
