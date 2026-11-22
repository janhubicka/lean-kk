import Kk.IntegerWitnessCompleteComponent
import Kk.ExtensionProfileAge
import Kk.IsolatedBlockContinuationAge
import Mathlib.Tactic

/-!
# Track F: finite class equivalence determines exact numeric canonical ages

English proof and adversarial audit committed FIRST:
docs/track_f_complete_nat_witness_numeric_age_english_audit_20261122.md

Every normalized K4 clique witness w has total size n < 4.
Its genuinely distinct typed vertices X_w = Σ j, Fin(w_j) can be
enumerated by Fin n and hence by actual Nat indices [0,n).
The total Nat sort map on those vertices realizes all support
multiplicities EXACTLY, including repeated labels and triples.
The complete loop-free symmetric graph on [0,n) is K4-free.

Thus finite sorted graph acceptance on this one REAL finite
Nat-labelled clique is exactly full normalized witness feasibility.
Consequently if two genuine integer graph ages accept precisely
the same finite symmetric K4-free sorted graphs, then all of
their normalized witness systems coincide, and the verified
extension-profile theorem yields NUMERIC equality of the FULL
canonical age FUNCTIONS, not equality of redundant RAW bounds.

This bridges the verified Track F finite graph-class equivalence
to numerical old/later survivor endpoint age equality, once the
actual finite source/target theorem's sorts are matched. It
does not assume a published diary theorem, geometric global orbit,
or the desired BRD lower bound.
-/

namespace Kk

/-- An arbitrary normalized integer clique multiplicity vector
has a genuine finite NAT-labelled realization with total N < ell,
realizing the exact whole support count on EVERY admissible
nonempty support, not just one selected support.

The default sort j0 is used only OUTSIDE the chosen finite Nat pool;
the intended K4 application can pick j0 when d>0. For d=0 there
are no supports and no j0; that degenerate case is handled
separately in the numerical age equality theorem. -/
theorem integerCliqueWeights_exists_exact_nat_sorted_pool
    (d ell : Nat) (hell : 0 < ell)
    (w : IntegerCliqueWeights d ell)
    (j0 : Fin d) :
    ∃ (N : Nat) (σ : Nat → Fin d),
      N < ell ∧
      ∀ T : IntegerGraphSupport d ell,
        ((Finset.range N).filter
          (fun x => σ x ∈ T.1)).card =
        integerCliqueOnSupport w T := by
  classical
  let X := IntegerWitnessVertex w
  let N : Nat := Fintype.card X
  let ι : Fin N ≃ X := (Fintype.equivFin X).symm
  let σ : Nat → Fin d := fun x =>
    if hx : x < N then (ι ⟨x, hx⟩).1 else j0
  have hSort (i : Fin N) : σ i.val = (ι i).1 := by
    dsimp [σ]
    simp [i.isLt]
  have hN : N < ell := integerWitnessVertex_card_lt w hell
  refine ⟨N, σ, hN, ?_⟩
  intro T
  let A : Finset (Fin N) :=
    Finset.univ.filter (fun i : Fin N => (ι i).1 ∈ T.1)
  let B : Finset X :=
    Finset.univ.filter (fun v : X => v.1 ∈ T.1)
  have hAImage :
      A.image Fin.val =
        (Finset.range N).filter (fun x => σ x ∈ T.1) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
      subst x
      have hiT : (ι i).1 ∈ T.1 :=
        (Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr i.isLt,
          by simpa only [hSort i] using hiT⟩
    · intro hx
      obtain ⟨hxN, hxT⟩ := Finset.mem_filter.mp hx
      let i : Fin N := ⟨x, Finset.mem_range.mp hxN⟩
      refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ i, ?_⟩
      have hxVal : σ i.val ∈ T.1 := hxT
      rw [hSort i] at hxVal
      exact hxVal
  have hBImage : A.image ι = B := by
    ext v
    constructor
    · intro hv
      obtain ⟨i, hi, hiv⟩ := Finset.mem_image.mp hv
      subst v
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
    · intro hv
      let i : Fin N := ι.symm v
      refine Finset.mem_image.mpr ⟨i, ?_, by simp [i]⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ i, ?_⟩
      have hvT : v.1 ∈ T.1 := (Finset.mem_filter.mp hv).2
      simpa only [i, Equiv.apply_symm_apply] using hvT
  have hCardA : (A.image Fin.val).card = A.card :=
    Finset.card_image_of_injective A Fin.val_injective
  have hCardB : (A.image ι).card = A.card :=
    Finset.card_image_of_injective A ι.injective
  calc
    ((Finset.range N).filter
      (fun x => σ x ∈ T.1)).card =
        (A.image Fin.val).card := congrArg Finset.card hAImage.symm
    _ = A.card := hCardA
    _ = (A.image ι).card := hCardB.symm
    _ = B.card := congrArg Finset.card hBImage
    _ = integerCliqueOnSupport w T :=
      integerWitnessVertex_support_eq_integerCliqueOnSupport w T

/-- Literal complete loop-free symmetric edge table on NAT indices.
Only its finite initial pool [0,N) is tested for K_ell-freeness. -/
def trackFNatCompleteEdge (x y : Nat) : Bool := decide (x ≠ y)

theorem trackFNatCompleteEdge_symmetric :
    ∀ x y : Nat, trackFNatCompleteEdge x y =
      trackFNatCompleteEdge y x := by
  intro x y
  simp only [trackFNatCompleteEdge, ne_comm]

theorem trackFNatCompleteEdge_clique
    (C : Finset Nat) :
    IsDirectedCliqueOn trackFNatCompleteEdge C := by
  classical
  intro x _ y _ hxy
  simp [trackFNatCompleteEdge, hxy]

theorem trackFNatCompleteEdge_no_forbidden_clique
    (ell N : Nat) (hN : N < ell) :
    finitePoolCliqueCheck trackFNatCompleteEdge ell
      (Finset.range N) = false := by
  classical
  apply (finitePoolCliqueCheck_false_iff_capacity_lt
    trackFNatCompleteEdge ell (Finset.range N)).2
  obtain ⟨C, hCN, _hClique, hCard⟩ :=
    finiteDirectedCliqueCapacity_attained
      trackFNatCompleteEdge (Finset.range N)
  have hCsize : C.card ≤ N := by
    simpa only [Finset.card_range] using Finset.card_le_card hCN
  omega

/-- The COMPLETE all-clique finite-test predicate of the exact
normalised age machinery; its finite sorted graph may have
repeated labels and arbitrary symmetric edges. -/
def trackFNatFiniteSortedAgeTest
    (d ell N : Nat)
    (F : IntegerGraphSupport d ell → Nat)
    (E : Nat → Nat → Bool)
    (σ : Nat → Fin d) : Prop :=
  ∀ C : Finset Nat,
    C ⊆ Finset.range N →
    IsDirectedCliqueOn E C →
    ∀ T : IntegerGraphSupport d ell,
      (C.filter (fun x => σ x ∈ T.1)).card ≤ F T

/-- In a true COMPLETE Nat-labelled clique, finite sorted-graph
acceptance is EXACTLY feasibility of the normalized vector whose
full support counts the labels. The converse checks EVERY clique
subset using filtered-cardinality monotonicity, not just C=range N.

No age-consistency assumption on F is needed for this equivalence. -/
theorem trackFNatCompleteTest_iff_integerWitness_feasible
    (d ell N : Nat)
    (F : IntegerGraphSupport d ell → Nat)
    (σ : Nat → Fin d)
    (w : IntegerCliqueWeights d ell)
    (hCounts : ∀ T : IntegerGraphSupport d ell,
      ((Finset.range N).filter (fun x => σ x ∈ T.1)).card =
      integerCliqueOnSupport w T) :
    trackFNatFiniteSortedAgeTest d ell N F
      trackFNatCompleteEdge σ ↔
    WitnessRespects
      (integerCliqueOnSupport (d := d) (ell := ell)) F w := by
  classical
  constructor
  · intro hTest T
    have h := hTest (Finset.range N)
      (Finset.Subset.refl _) (trackFNatCompleteEdge_clique _) T
    rw [hCounts T] at h
    exact h
  · intro hw C hCN _hClique T
    have hSubFilter :
        C.filter (fun x => σ x ∈ T.1) ⊆
          (Finset.range N).filter (fun x => σ x ∈ T.1) := by
      intro x hx
      obtain ⟨hxC, hxT⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hCN hxC, hxT⟩
    calc
      (C.filter (fun x => σ x ∈ T.1)).card ≤
          ((Finset.range N).filter
            (fun x => σ x ∈ T.1)).card :=
        Finset.card_le_card hSubFilter
      _ = integerCliqueOnSupport w T := hCounts T
      _ ≤ F T := hw T

/-- Equality of ALL finite sorted K4-free graph-class tests for
two GENUINE integer ages implies equality of their exact NUMERIC
canonical support values, including mixed triple supports.

The proof uses the actual Nat complete-clique representation of
EVERY normalized witness, and the separately verified finite
extension-profile characterization. The d=0 case is vacuous;
no fictitious default sort is selected. -/
theorem trackF_numeric_integer_age_eq_of_all_finite_K4_tests
    (d : Nat)
    (F G : IntegerGraphSupport d 4 → Nat)
    (hF : IsIntegerGraphAge d 4 F)
    (hG : IsIntegerGraphAge d 4 G)
    (hTests : ∀ N : Nat, ∀ E : Nat → Nat → Bool,
      ∀ σ : Nat → Fin d,
      (∀ x y, E x y = E y x) →
      finitePoolCliqueCheck E 4 (Finset.range N) = false →
      (trackFNatFiniteSortedAgeTest d 4 N F E σ ↔
       trackFNatFiniteSortedAgeTest d 4 N G E σ)) :
    F = G := by
  classical
  by_cases hd : d = 0
  · subst d
    funext T
    obtain ⟨j, _hj⟩ := T.2.1
    exact Fin.elim0 j
  · have hdPos : 0 < d := Nat.pos_of_ne_zero hd
    let j0 : Fin d := ⟨0, hdPos⟩
    have hSame :
        ∀ w : IntegerCliqueWeights d 4,
          WitnessRespects
            (integerCliqueOnSupport (d := d) (ell := 4)) F w ↔
          WitnessRespects
            (integerCliqueOnSupport (d := d) (ell := 4)) G w := by
      intro w
      obtain ⟨N, σ, hN, hCounts⟩ :=
        integerCliqueWeights_exists_exact_nat_sorted_pool
          d 4 (by decide) w j0
      have hSym : ∀ x y,
          trackFNatCompleteEdge x y =
            trackFNatCompleteEdge y x :=
        trackFNatCompleteEdge_symmetric
      have hFree :
          finitePoolCliqueCheck trackFNatCompleteEdge 4
            (Finset.range N) = false :=
        trackFNatCompleteEdge_no_forbidden_clique 4 N hN
      have hClasses := hTests N trackFNatCompleteEdge σ hSym hFree
      have hFIff :=
        trackFNatCompleteTest_iff_integerWitness_feasible
          d 4 N F σ w hCounts
      have hGIff :=
        trackFNatCompleteTest_iff_integerWitness_feasible
          d 4 N G σ w hCounts
      exact hFIff.symm.trans (hClasses.trans hGIff)
    exact integerGraphAge_eq_of_same_feasible_vectors
      d 4 F G hF hG hSame

end Kk
