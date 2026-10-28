import Kk.B3SmallCliqueCore
import Mathlib.Tactic

/-!
# Cut-star locality for arbitrary corrected-B3 clique continuations

The full corrected B3 witness W is an arbitrary finite L-only
continuation. Its upper-upper edges need NOT agree with the actual
ambient numerical H: one must NOT apply real-H clique-block locality
directly to all vertices of W.

Nevertheless, the complete named-original L-type of EACH upper W
vertex agrees through the tested cut with the actual ambient H type.
A forbidden clique witnessing failed B3 contains the tested cut.
Therefore every upper vertex of that clique has a named actual-H
original ADJACENT TO THE CUT. This controls membership in the
cut's neighbourhood without ever asserting anything about
upper-upper W edges.

The second theorem makes this a general support-locality interface:
any prescribed source name outside a chosen Relevant set which has
no ambient edge to the cut cannot occur in the forbidden clique.
For a cut lying in one reserved gadget block, this can exclude
all OTHER reserved blocks using the already verified actual-H
cross-block nonedges, and exclude active vertices outside that
block's support. The classification/coverage of the remaining
parameter-closed source names is still a separate geometric task.
-/

namespace Kk

open SuccessorTree.V10

/-- A complete prescribed upper L-type transfers the cut--upper edge
from the arbitrary age-test continuation W to the literal ambient
L-structure C. No condition on edges between two upper vertices of
W is required. -/
theorem clique_core_upper_name_adjacent_to_cut
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
      ∃ v : Fin M,
        Selected v ∧ C.binary cut (original v) (0 : Fin 1) = true := by
  intro a ha
  obtain ⟨v,hSel,hType⟩ :=
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
  exact ⟨v,hSel,hCross.symm.trans hWEdge⟩

/-- If all unwanted selected original names are actually nonadjacent
to the tested cut, no such original can be used by a future vertex
of an arbitrary forbidden clique continuation. The exclusion only
uses ONE cut--upper crossing, so freely chosen upper--upper
continuation edges do not invalidate it. -/
theorem clique_core_upper_names_local_of_cut_nonedges
    (C W : AgeTestModel 1 0 1)
    (cut ell M : Nat)
    (original : Fin M → Nat)
    (Selected Relevant : Fin M → Prop)
    (hUpper : ∀ x, x ∈ W.carrier → cut < x →
      ∃ v : Fin M, Selected v ∧
        RelationalPrefixType.ofAgeModel W (cut+1) x =
          RelationalPrefixType.ofAgeModel C (cut+1) (original v))
    (hOutside : ∀ v : Fin M, Selected v → ¬ Relevant v →
      C.binary cut (original v) (0 : Fin 1) = false)
    (e : Fin ell → Nat)
    (hCopy : W.Realizes (cliquePattern ell) e)
    (hAt : ∃ b : Fin ell, e b = cut) :
    ∀ a : Fin ell, cut < e a →
      ∃ v : Fin M, Selected v ∧ Relevant v := by
  intro a ha
  obtain ⟨v,hSel,hEdge⟩ :=
    clique_core_upper_name_adjacent_to_cut
      C W cut ell M original Selected hUpper
      e hCopy hAt a ha
  refine ⟨v,hSel,?_⟩
  by_contra hn
  have hZero := hOutside v hSel hn
  rw [hZero] at hEdge
  cases hEdge

/-- Direct application to a GENUINE failed selected-original B3 test
in numerical H. The finite witness core has ONLY upper vertices
from the forbidden clique, and every one must come from an
ambient-original name with a genuine positive edge to the tested cut.

The caller supplies the explicit outside-cut nonedge condition
for the chosen Relevant names. This is the precise remaining
gadget-geometric interface; no classification of all source names
is silently assumed. -/
theorem henson_failed_selectedB3_has_cut_local_small_core
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
    (Selected Relevant : Fin M → Prop)
    (hOutside : ∀ v : Fin M, Selected v → ¬ Relevant v →
      (finiteNumericHL (normalizedGraphModel E) k N).binary
        cut (original v).val (0 : Fin 1) = false)
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
        ∃ v : Fin M, Selected v ∧ Relevant v) := by
  obtain ⟨V,e,hFinite,hSocle,hDelete,hUpper,hCopy,hAt,hFuture⟩ :=
    henson_selectedB3_failure_has_small_clique_core
      ell hell k hK E hLoops hSym hClique
      N cut M hCut original Selected hFailure
  let C := finiteNumericHL (normalizedGraphModel E) k N
  have hTypes : ∀ x, x ∈ V.carrier → cut < x →
      ∃ v : Fin M, Selected v ∧
        RelationalPrefixType.ofAgeModel V (cut+1) x =
          RelationalPrefixType.ofAgeModel C (cut+1) (original v).val := by
    intro x hx hAbove
    obtain ⟨v,hSel,_hFree,hType⟩ := hUpper x hx hAbove
    exact ⟨v,hSel,hType⟩
  have hRelevant : ∀ a : Fin ell, cut < e a →
      ∃ v : Fin M, Selected v ∧ Relevant v :=
    clique_core_upper_names_local_of_cut_nonedges
      C V cut ell M (fun v => (original v).val)
      Selected Relevant hTypes hOutside e hCopy hAt
  refine ⟨V,e,hFinite,hSocle,hDelete,hCopy,hAt,?_⟩
  intro x hx hAbove
  obtain ⟨a,ha⟩ := hFuture x hx hAbove
  obtain ⟨v,hSel,hRel⟩ := hRelevant a (by rw [ha]; exact hAbove)
  exact ⟨v,hSel,hRel⟩

end Kk
