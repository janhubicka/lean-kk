import Kk.PhysicalIsolatedSupportStage
import Kk.IsolatedSupportCanonicalAge
import Kk.IntegerAgeUniversalProperties
import Mathlib.Tactic

/-!
# KK Track A: one GENUINE finite Henson isolated-block CANONICAL AGE COVER stage

English proof and 20 hostile adversarial checks committed FIRST:
  docs/physical_canonical_cover_stage_english_audit.md

This theorem combines separately verified:
* real Henson reserved-clique existence and all-gap,
  all-generation complete L columns for ONE common finite top
  future, with the actual literal gap-inclusive raw bound
  (Track A physical stage PR #195);
* exact normalized-witness/canonical-age equality between
  ACTUAL isolated block raw update and IDEAL one-coordinate
  cover bound, despite pointwise RAW differences on proper
  sub-supports (Track A PR #191).

For a genuine integer graph-age cover lower ⋖ upper and the
substantive complete old-reference invariant G_(B_P)=upper,
the theorem constructs a real isolated clique Q of the exact
required size r, a physical F including ALL real gaps, and
one common numerical-H future with complete old/reserved/gap
L columns. The TRUE canonical old age after inserting Q
is exactly lower on EVERY support, and the physical common
future's full normalized clique-vector profile is precisely
lower-feasible, not just one distinguished support capacity.

This is a FINITE positive-link ordinary-L cover step.
The coherent infinite canonical resolved diary, full H+
parameter-closed Kpt E/I1–I3/B3 source and common labelled
inverse source orbit, and the big Ramsey degree theorem
remain open and are NOT claimed here.
-/

namespace Kk

/-- An actual directed clique Q has clique capacity |Q|.
This cardinal equality is valid ONLY with a genuine clique
hypothesis, not for an arbitrary reserved collection. -/
theorem isolatedReservedClique_capacity_eq_card
    (E : Nat → Nat → Bool) (Q : Finset Nat)
    (hClique : IsDirectedCliqueOn E Q) :
    finiteDirectedCliqueCapacity E Q = Q.card := by
  classical
  have hLower : Q.card ≤ finiteDirectedCliqueCapacity E Q :=
    directedClique_card_le_capacity E Q Q
      (Finset.Subset.refl Q) hClique
  obtain ⟨s,hsQ,hsClique,hCapCard⟩ :=
    finiteDirectedCliqueCapacity_attained E Q
  have hUpper : s.card ≤ Q.card :=
    Finset.card_le_card hsQ
  omega

/-- Equality of the entire normalized integer witness families
follows from pointwise equality of a raw bound's canonicalization
with a second target bound. In particular, canonical equality
gives exact feasibility, not merely equality of maxima. -/
theorem integerCliqueFeasible_eq_of_canonical_eq
    (d ell : Nat)
    (B H : IntegerGraphSupport d ell → Nat)
    (hCanonical : integerGraphAgeCanonical d ell B = H) :
    feasibleIntegerCliqueVectors d ell B =
      feasibleIntegerCliqueVectors d ell H := by
  classical
  ext w
  change
    WitnessRespects
      (integerCliqueOnSupport (d := d) (ell := ell)) B w ↔
    WitnessRespects
      (integerCliqueOnSupport (d := d) (ell := ell)) H w
  rw [← hCanonical]
  exact (integerGraphAgeCanonical_preserves_clique_vectors
    d ell B w).symm

/-- The complete GENUINE finite physical canonical cover step.

From a fixed original normalized left-dense Henson enumeration E,
one entire original old prefix [0,b), a full prescribed old-to-future
typed column c, a genuine integer graph-age cover lower ⋖ upper
with ell=lower(T)+r+1, upper(T)=lower(T)+1, and the necessary
PRE-STAGE COMPLETE age invariant G_(B_P)=upper, we ACTUALLY CHOOSE:

* one genuinely isolated reserved original K_r clique Q after b;
* a genuine cutoff F containing every intervening original gap;
* one finite physical Henson/numerical-H universal stage AFTER F,
  with one f,M and every complete old/reserve/gap ordinary-L column.

The actual old common-neighbour canonical age over THE WHOLE
numeric original prefix [0,F) is EXACTLY lower. The physical
finite stage's raw bound from P∪Q has EXACTLY the same normalized
labelled clique-vector set as lower: its ONE actual numeric-H top
future therefore realizes all and only lower-feasible normalized
vectors. The equivalence is global across ALL nonempty supports.

We do NOT claim the infinite diary's repeated stages maintain the
pre-stage age=upper invariant, or settle H+ Kpt E/B3/orbits/BRDs. -/
theorem henson_leftDense_exists_physical_finite_canonical_cover_stage
    (d ell b k r : Nat)
    (hell : 2 ≤ ell) (hd : 0 < d)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool)
    (T : IntegerGraphSupport d ell)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (hEll : ell = lower T + r + 1)
    (hAt : upper T = lower T + 1)
    (hPrior : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) = upper) :
    ∃ (Q : Finset Nat) (F : Nat),
      Q.card = r ∧
      (∀ q ∈ Q, b ≤ q ∧ q < F) ∧
      IsDirectedCliqueOn E Q ∧
      (∀ p, p < b → ∀ q ∈ Q,
        E p q = false ∧ E q p = false) ∧
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range F)
          (supportBlockGappedColumn b Q T.1 c)) = lower ∧
      feasibleIntegerCliqueVectors d ell
        (finiteOldColumnRawBound E ell d
          (Finset.range b ∪ Q)
          (supportBlockOldColumn Q T.1 c)) =
        feasibleIntegerCliqueVectors d ell lower ∧
      HasUniformPositiveSupportStage E d ell b F k hd c Q T := by
  classical
  have hLowerPositive : 1 ≤ lower T := (hCover.lower_age.1 T).1
  have hUpperBound : upper T ≤ ell - 1 := (hCover.upper_age.1 T).2
  have hr : r < ell := by omega
  have hrPos : 0 < r := by omega
  obtain ⟨Q,F,hCard,hQWithin,hClique,hOldIso,hStage⟩ :=
    henson_leftDense_exists_uniform_finite_support_stage
      d ell b k r hell hd hr E hAvoid hDense c T
  have hNonempty : Q.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨q,hq⟩ := hNonempty
  have hBF : b ≤ F :=
    le_trans (hQWithin q hq).1
      (Nat.le_of_lt (hQWithin q hq).2)
  have hDisjoint : Disjoint (Finset.range b) Q := by
    apply Finset.disjoint_left.mpr
    intro p hp hqP
    have hPb : p < b := Finset.mem_range.mp hp
    have hQb : b ≤ p := (hQWithin p hqP).1
    omega
  have hZero : ∀ p ∈ Finset.range b, ∀ q ∈ Q,
      E p q = false := by
    intro p hp q hqQ
    exact (hOldIso p (Finset.mem_range.mp hp) q hqQ).1
  have hCapEq : finiteDirectedCliqueCapacity E Q = r := by
    rw [isolatedReservedClique_capacity_eq_card E Q hClique]
    exact hCard
  have hAgePQ := isolatedSupportCanonicalAge_cover_step
    E ell d r (Finset.range b) Q hDisjoint hZero c T
    lower upper hCover hEll hAt hPrior
    (by rw [hCapEq])
  rw [hCapEq, if_neg (lt_irrefl r)] at hAgePQ
  have hGapAge := supportBlockGappedCanonicalAge_eq
    E ell d b F hBF Q hQWithin T c
  have hPhysicalAge :
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range F)
          (supportBlockGappedColumn b Q T.1 c)) = lower :=
    hGapAge.trans hAgePQ
  have hFeasibleF :=
    integerCliqueFeasible_eq_of_canonical_eq d ell
      (finiteOldColumnRawBound E ell d (Finset.range F)
        (supportBlockGappedColumn b Q T.1 c))
      lower hPhysicalAge
  have hRawEq := supportBlockGappedRawBound_eq
    E ell d b F hBF Q hQWithin T c
  have hFeasiblePQ :
      feasibleIntegerCliqueVectors d ell
        (finiteOldColumnRawBound E ell d
          (Finset.range b ∪ Q)
          (supportBlockOldColumn Q T.1 c)) =
        feasibleIntegerCliqueVectors d ell lower := by
    rw [← hRawEq]
    exact hFeasibleF
  exact ⟨Q,F,hCard,hQWithin,hClique,hOldIso,
    hPhysicalAge,hFeasiblePQ,hStage⟩

#print axioms Kk.isolatedReservedClique_capacity_eq_card
#print axioms Kk.integerCliqueFeasible_eq_of_canonical_eq
#print axioms Kk.henson_leftDense_exists_physical_finite_canonical_cover_stage

end Kk
