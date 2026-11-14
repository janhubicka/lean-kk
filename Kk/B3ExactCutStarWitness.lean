import Kk.B3CutStarLocality
import Kk.B3CutStarNormalForm
import Mathlib.Tactic

/-!
# Track D: exact full L-type labels on EVERY upper vertex of a failed B3 clique

The already verified small-clique-core theorem identifies one finite
ordinary-L forbidden witness V and one K_ell clique e through the cut.
We sharpen its upper labels: EACH future vertex of that SAME core has
one genuinely selected, cut-eligible, CUT-ADJACENT physical original
whose COMPLETE next-cut L-prefix type agrees with the vertex's type.

The selected name may be an auxiliary Kpt parameter. No (I2) exclusion,
global resolved diary or common labelled inverse-source orbit is assumed.

English proof and hostile audit:
docs/audits/2026-11-14-track-d-exact-cut-star-witness-english.md
-/

namespace Kk

open SuccessorTree.V10

/-- For an arbitrary L-only forbidden clique containing the tested cut,
the SAME complete selected upper-type label witnesses both the original
physical cut adjacency and the full next-cut ordinary L-prefix type.

This conclusion is stronger than merely finding some selected
cut-neighbour; no upper--upper age-witness edge is identified with
an ambient physical edge. -/
theorem clique_core_every_upper_has_exact_cut_neighbour_label
    (C W : AgeTestModel 1 0 1)
    (cut ell M : Nat)
    (original : Fin M → Nat)
    (Selected : Fin M → Prop)
    (hUpper : ∀ x, x ∈ W.carrier → cut < x →
      ∃ v : Fin M, Selected v ∧
        RelationalPrefixType.ofAgeModel W (cut+1) x =
          RelationalPrefixType.ofAgeModel C (cut+1) (original v))
    (e : Fin ell → Nat)
    (hCopy : W.Realizes (cliquePattern ell) e)
    (hAt : ∃ b : Fin ell, e b = cut) :
    ∀ a : Fin ell, cut < e a →
      ∃ v : Fin M, Selected v ∧
        C.binary cut (original v) (0 : Fin 1) = true ∧
        RelationalPrefixType.ofAgeModel W (cut+1) (e a) =
          RelationalPrefixType.ofAgeModel C (cut+1) (original v) := by
  intro a ha
  obtain ⟨v,hSelected,hType⟩ :=
    hUpper (e a) (hCopy.2.1 a) ha
  obtain ⟨b,hb⟩ := hAt
  have hba : b ≠ a := by
    intro heq
    rw [heq] at hb
    omega
  have hWEdge : W.binary cut (e a) (0 : Fin 1) = true := by
    have hCopyEdge :=
      hCopy.2.2.1 b a hba (0 : Fin 1)
    simpa [hb, cliquePattern, hba] using hCopyEdge
  have hCross := congrArg
      (fun T : RelationalPrefixType (cut+1) 1 0 1 =>
        T.binary (some (⟨cut, Nat.lt_succ_self cut⟩ : Fin (cut+1)))
          none (0 : Fin 1)) hType
  change W.binary cut (e a) (0 : Fin 1) =
    C.binary cut (original v) (0 : Fin 1) at hCross
  exact ⟨v,hSelected,hCross.symm.trans hWEdge,hType⟩

/-- A failed genuine Henson selected-stage corrected B3 test has ONE
finite L-only clique core V such that EVERY upper V-vertex has a
SINGLE selected physical original satisfying ALL of:
(1) genuine free-level cut eligibility;
(2) physical positive cut adjacency;
(3) equality of the entire directed (cut+1) L-reduct type.

No structural no-(I2) assumption is needed for this witness extraction.
This is not yet the unproved relative graph-age/B3-loss equivalence. -/
theorem henson_failed_selectedB3_has_exact_full_cut_star_core
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
    ∃ (V : AgeTestModel 1 0 1) (e : Fin ell → Nat),
      V.BoundedCarrier ∧
      SameInitialL V
        (finiteNumericHL (normalizedGraphModel E) k N) cut ∧
      (∀ bad, bad ∈ hensonForbiddenFamily ell hell →
        bad.Avoids (V.withoutVertex cut)) ∧
      V.Realizes (cliquePattern ell) e ∧
      (∃ a : Fin ell, e a = cut) ∧
      (∀ x, x ∈ V.carrier → cut < x →
        ∃ a : Fin ell, e a = x) ∧
      (∀ x, x ∈ V.carrier → cut < x →
        ∃ v : Fin M, Selected v ∧
          cut+1 ≤ (finiteNumericH (normalizedGraphModel E) k N).freeLevel
            (original v).val ∧
          (finiteNumericHL (normalizedGraphModel E) k N).binary
            cut (original v).val (0 : Fin 1) = true ∧
          RelationalPrefixType.ofAgeModel V (cut+1) x =
            RelationalPrefixType.ofAgeModel
              (finiteNumericHL (normalizedGraphModel E) k N)
              (cut+1) (original v).val) := by
  obtain ⟨V,e,hFinite,hSocle,hDelete,hUpper,hCopy,hAt,hFuture⟩ :=
    henson_selectedB3_failure_has_small_clique_core
      ell hell k hK E hLoops hSym hClique
      N cut M hCut original Selected hFailure
  let A := finiteNumericH (normalizedGraphModel E) k N
  let C := finiteNumericHL (normalizedGraphModel E) k N
  have hNamed : ∀ a : Fin ell, cut < e a →
      ∃ v : Fin M,
        (Selected v ∧ cut+1 ≤ A.freeLevel (original v).val) ∧
        C.binary cut (original v).val (0 : Fin 1) = true ∧
        RelationalPrefixType.ofAgeModel V (cut+1) (e a) =
          RelationalPrefixType.ofAgeModel C (cut+1) (original v).val := by
    have hUpperNamed : ∀ x, x ∈ V.carrier → cut < x →
        ∃ v : Fin M,
          (Selected v ∧ cut+1 ≤ A.freeLevel (original v).val) ∧
          RelationalPrefixType.ofAgeModel V (cut+1) x =
            RelationalPrefixType.ofAgeModel C (cut+1) (original v).val := by
      intro x hx hAbove
      obtain ⟨v,hSelected,hFree,hType⟩ := hUpper x hx hAbove
      exact ⟨v,⟨hSelected,hFree⟩,hType⟩
    exact clique_core_every_upper_has_exact_cut_neighbour_label
      C V cut ell M (fun v => (original v).val)
      (fun v => Selected v ∧ cut+1 ≤ A.freeLevel (original v).val)
      hUpperNamed e hCopy hAt
  refine ⟨V,e,hFinite,hSocle,hDelete,hCopy,hAt,hFuture,?_⟩
  intro x hx hAbove
  obtain ⟨a,ha⟩ := hFuture x hx hAbove
  obtain ⟨v,⟨hSelected,hFree⟩,hEdge,hType⟩ :=
    hNamed a (by rw [ha]; exact hAbove)
  refine ⟨v,hSelected,hFree,hEdge,?_⟩
  rw [ha] at hType
  exact hType

#print axioms clique_core_every_upper_has_exact_cut_neighbour_label
#print axioms henson_failed_selectedB3_has_exact_full_cut_star_core

end Kk
