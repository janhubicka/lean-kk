import Kk.UniformStageOriginalCoverLoss
import Kk.UniversalFutureExactProfile
import Kk.RelativeUniversalFiniteTarget
import Kk.FiniteTaggedFutureEncoding
import Mathlib.Tactic

/-!
# Track B: a genuine physical post-cover age gives a NONEMPTY selected T future

English-first proof and twelve hostile checks:
docs/track_b_selected_sort_nonvacuity_english_audit.md

A conditional finite-stage statement "for every w with tau(w) in T"
could be VACUOUS if the tagged future has no T vertex. Positivity of
the canonical integer age at T is the exact legitimate condition.
A verified universal finite clique attains this positive value, so
an actual universal witness vertex in sort T exists. Pass to its
genuine future subtype, encode its physical Nat original address
using finiteTaggedIndex, and decode the actual sort without defaults.

For a real Henson canonical cover lower < upper, lower(T)>0 and the
already checked genuine isolated-block age-cover theorem IDENTIFIES
the canonical age of the actual old+Q raw B with lower. Hence the
positive tagged sort witness exists, and the one finite-stage f,M
realizes an ACTUAL selected original v=f(w) with true two-directed
E links to all Q. Only the NEXT future positive typed column
remains an explicit premise for strict canonical loss.
-/

namespace Kk

/-- If the joint normalized integer witness canonical age G_B(T)
is POSITIVE, the genuinely constructed finite tagged future has
an ACTUAL numbered vertex w whose exact decoded sort tau(w) is in T.

No fake default sort or existential embedding from a different
finite universal witness is used. -/
theorem finiteTaggedFuture_exists_T_sort_of_positive_canonical
    (d ell F : Nat)
    (hd : 0 < d) (hell : 0 < ell)
    (B : IntegerGraphSupport d ell → Nat)
    (T : IntegerGraphSupport d ell)
    (hPositive : 0 < integerGraphAgeCanonical d ell B T) :
    let V := RelativeUniversalTaggedVertex d ell B
    let W : Finset Nat := finiteTaggedFuturePool (V := V) F
    let tau := finiteTaggedFutureSort hd
      (relativeUniversalTaggedSort d ell B) F
    ∃ w ∈ W, tau w ∈ T.1 := by
  classical
  obtain ⟨s, hSubset, _hClique, hCounts⟩ :=
    universalWitnessFuture_clique_attains_canonical
      d ell hell B T
  have hNonempty :
      (s.filter (fun u => u.2.1 ∈ T.1)).Nonempty := by
    apply Finset.card_pos.mp
    rw [hCounts]
    exact hPositive
  obtain ⟨u, huFilter⟩ := hNonempty
  obtain ⟨huS, huSort⟩ := Finset.mem_filter.mp huFilter
  let z : RelativeUniversalTaggedVertex d ell B :=
    ⟨u, hSubset huS⟩
  refine ⟨finiteTaggedIndex F z, ?_, ?_⟩
  · unfold finiteTaggedFuturePool
    exact Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩
  · change finiteTaggedFutureSort hd
        (relativeUniversalTaggedSort d ell B) F
        (finiteTaggedIndex F z) ∈ T.1
    rw [finiteTaggedFutureSort_index]
    exact huSort

/-- A GENUINE finite first Henson canonical cover, with one uniform
selected top stage, has an ACTUAL nonempty physical top witness v=f(w)
of sort tau(w)∈T. That SAME f has both-directed original E links
from ALL reserved q∈Q to v. This is not a vacuous "all such w" claim.

For ANY subsequently prescribed complete future-sort column which
agrees below F and is T-positive at that selected original, the
true-prefix canonical T-age STRICTLY drops between F and f(w)+1.
The choice/existence of such a coherent FUTURE column is not proved.
No bound on how many canonical cover events occur, auxiliary Kpt
source synchronization, or common labelled orbit is asserted. -/
theorem real_cover_uniform_stage_has_selected_T_witness_forcing_loss
    (E : Nat → Nat → Bool)
    (hSym : ∀ x y, E x y = E y x)
    (ell d b F k r : Nat) (hd : 0 < d)
    (c : Nat → Fin d → Bool)
    (Q : Finset Nat) (T : IntegerGraphSupport d ell)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hBF : b ≤ F)
    (hWithin : ∀ q ∈ Q, b ≤ q ∧ q < F)
    (hClique : IsDirectedCliqueOn E Q)
    (hCard : Q.card = r)
    (hIso : ∀ p, p < b → ∀ q ∈ Q,
      E p q = false ∧ E q p = false)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (hEll : ell = lower T + r + 1)
    (hAt : upper T = lower T + 1)
    (hPrior : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) = upper)
    (hStage : HasUniformPositiveSupportStage
      E d ell b F k hd c Q T) :
    let B := finiteOldColumnRawBound E ell d
      (Finset.range b ∪ Q) (supportBlockOldColumn Q T.1 c)
    let V := RelativeUniversalTaggedVertex d ell B
    let W : Finset Nat := finiteTaggedFuturePool (V := V) F
    let tau := finiteTaggedFutureSort hd
      (relativeUniversalTaggedSort d ell B) F
    ∃ (f : Nat → Nat) (M : Nat) (w : Nat),
      w ∈ W ∧ tau w ∈ T.1 ∧ F ≤ f w ∧
      (∀ q ∈ Q, E q (f w) = true ∧ E (f w) q = true) ∧
      (∀ (cNext : Nat → Fin d → Bool),
        (∀ p, p < F → ∀ t,
          cNext p t = supportBlockGappedColumn b Q T.1 c p t) →
        (∀ t ∈ T.1, cNext (f w) t = true) →
        integerGraphAgeCanonical d ell
          (finiteOldColumnRawBound E ell d
            (Finset.range (f w + 1)) cNext) T <
        integerGraphAgeCanonical d ell
          (finiteOldColumnRawBound E ell d
            (Finset.range F) cNext) T) := by
  classical
  let B : IntegerGraphSupport d ell → Nat :=
    finiteOldColumnRawBound E ell d
      (Finset.range b ∪ Q) (supportBlockOldColumn Q T.1 c)
  let tau : Nat → Fin d :=
    finiteTaggedFutureSort hd
      (relativeUniversalTaggedSort d ell B) F
  have hDisjoint : Disjoint (Finset.range b) Q := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hpB := Finset.mem_range.mp hp
    have hqb := (hWithin p hq).1
    omega
  have hZero : ∀ p ∈ Finset.range b, ∀ q ∈ Q,
      E p q = false := by
    intro p hp q hq
    exact (hIso p (Finset.mem_range.mp hp) q hq).1
  have hQCapacity : finiteDirectedCliqueCapacity E Q = r := by
    rw [isolatedReservedClique_capacity_eq_card E Q hClique]
    exact hCard
  have hCoverAge : integerGraphAgeCanonical d ell B = lower := by
    have hAge := isolatedSupportCanonicalAge_cover_step
      E ell d r (Finset.range b) Q hDisjoint hZero c T
      lower upper hCover hEll hAt hPrior (le_of_eq hQCapacity)
    simpa only [B, hQCapacity, if_neg (lt_irrefl r)] using hAge
  have hPositive : 0 < integerGraphAgeCanonical d ell B T := by
    rw [hCoverAge]
    have hp : 1 ≤ lower T := (hCover.lower_age.1 T).1
    omega
  have hEllPos : 0 < ell := by omega
  obtain ⟨w, hw, hwSort⟩ :=
    finiteTaggedFuture_exists_T_sort_of_positive_canonical
      d ell F hd hEllPos B T hPositive
  obtain ⟨f, M, hAfter, hColumn⟩ :=
    uniform_positive_stage_reserved_original_E_column
      E hSym d ell b F k hd c Q T hWithin hStage
  have hLinks : ∀ q ∈ Q,
      E q (f w) = true ∧ E (f w) q = true := by
    intro q hq
    have hBits := hColumn q hq w hw
    have hDec : decide (tau w ∈ T.1) = true := by
      simp [hwSort]
    exact ⟨hBits.1.trans hDec, hBits.2.trans hDec⟩
  refine ⟨f, M, w, hw, hwSort, hAfter w hw, hLinks, ?_⟩
  intro cNext hPrefix hVPositive
  exact (real_cover_later_full_link_forces_strict_canonical_T_drop
    E ell d b F r c cNext T Q lower upper
    hBF hWithin hClique hCard hIso hCover hEll hAt hPrior
    (f w) (hAfter w hw) hPrefix hVPositive hLinks).1

#print axioms Kk.finiteTaggedFuture_exists_T_sort_of_positive_canonical
#print axioms Kk.real_cover_uniform_stage_has_selected_T_witness_forcing_loss

end Kk
