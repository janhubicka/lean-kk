import Kk.TwoPhysicalCanonicalCovers
import Mathlib.Tactic

/-!
# Track B: finite physical Henson cover spacing with zero future columns

English proof and hostile audit committed FIRST in:
docs/track_b_zero_tail_physical_spacing_english_audit.md

For a complete typed future-sort column c, keep every old value p<b
unchanged and set ALL later original indices p>=b to false. On any
admissible NONEMPTY support, the true common-old-original neighbour
pool is now literally constant at every later original cut N>=b.
The full raw/canonical old age is therefore constant through the gap.

This is a valid ordinary-L finite-column recipe. It is NOT a coherent
extension of previously chosen positive selected witnesses lying beyond b:
zeroing their passing bits can invalidate their required type. No
unbounded resolved copy, Kpt dependent L+ event dictionary, or labelled
inverse-source orbit is asserted.
-/

namespace Kk

/-- Keep actual old full typed columns below b, zero EVERY future
original's column from b onward. Does not alter the original E graph. -/
def oldColumnZeroTail {d : Nat} (b : Nat)
    (c : Nat → Fin d → Bool) (p : Nat) (t : Fin d) : Bool :=
  if p < b then c p t else false

/-- On a genuine nonempty support, the complete common-old-neighbour
pool after zeroing every later column is literally fixed at the
chosen original cut b. This includes every original (not just a
selected macrodiary subsequence). -/
theorem oldSupportCommonNeighbourPool_zeroTail
    (d ell b N : Nat)
    (c : Nat → Fin d → Bool)
    (U : IntegerGraphSupport d ell)
    (hBN : b ≤ N) :
    oldSupportCommonNeighbourPool (Finset.range N)
      (oldColumnZeroTail b c) U.1 =
    oldSupportCommonNeighbourPool (Finset.range b) c U.1 := by
  classical
  ext p
  change
    p ∈ (Finset.range N).filter
      (fun q => ∀ t ∈ U.1, oldColumnZeroTail b c q t = true) ↔
    p ∈ (Finset.range b).filter
      (fun q => ∀ t ∈ U.1, c q t = true)
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hPN, hAll⟩
    have hPB : p < b := by
      by_contra hNot
      obtain ⟨t, ht⟩ := U.2.1
      have hColumn := hAll t ht
      simp [oldColumnZeroTail, hNot] at hColumn
    refine ⟨hPB, ?_⟩
    intro t ht
    simpa [oldColumnZeroTail, hPB] using hAll t ht
  · rintro ⟨hPB, hAll⟩
    refine ⟨lt_of_lt_of_le hPB hBN, ?_⟩
    intro t ht
    simpa [oldColumnZeroTail, hPB] using hAll t ht

/-- Exact literal RAW support equality after any finite zero-column
gap. No graph symmetry, Henson avoidance or other safety is needed. -/
theorem finiteOldColumnRawBound_zeroTail
    (E : Nat → Nat → Bool) (ell d b N : Nat)
    (c : Nat → Fin d → Bool)
    (U : IntegerGraphSupport d ell)
    (hBN : b ≤ N) :
    finiteOldColumnRawBound E ell d (Finset.range N)
      (oldColumnZeroTail b c) U =
    finiteOldColumnRawBound E ell d (Finset.range b) c U := by
  change ell - 1 -
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range N)
          (oldColumnZeroTail b c) U.1) =
    ell - 1 -
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b) c U.1)
  rw [oldSupportCommonNeighbourPool_zeroTail d ell b N c U hBN]

/-- Pointwise equality of the entire RAW old age, as a function on
ALL admissible nonempty future-sort supports. -/
theorem finiteOldColumnRawBound_zeroTail_fun
    (E : Nat → Nat → Bool) (ell d b N : Nat)
    (c : Nat → Fin d → Bool)
    (hBN : b ≤ N) :
    finiteOldColumnRawBound E ell d (Finset.range N)
        (oldColumnZeroTail b c) =
      finiteOldColumnRawBound E ell d (Finset.range b) c := by
  funext U
  exact finiteOldColumnRawBound_zeroTail E ell d b N c U hBN

/-- The WHOLE integer-witness CANONICAL reference age is fixed
through arbitrarily long later original intervals with true ZERO
future columns. This is an age-level statement, not a preservation
theorem for earlier positive selected witnesses beyond the cut. -/
theorem integerGraphAgeCanonical_zeroTail
    (E : Nat → Nat → Bool) (ell d b N : Nat)
    (c : Nat → Fin d → Bool)
    (hBN : b ≤ N) :
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range N)
        (oldColumnZeroTail b c)) =
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) := by
  rw [finiteOldColumnRawBound_zeroTail_fun E ell d b N c hBN]

/-- A GENUINE physical Henson canonical cover can be placed beyond
ANY prescribed later original cutoff N≥b by zeroing the chosen
future-sort column after b. The actual old canonical age at N is
DERIVED from the age at b, not independently postulated.

The construction does not preserve any positive selected-witness
passing bits beyond b that the zero-tail recipe overwrites. -/
theorem henson_leftDense_exists_physical_cover_after_zeroTail
    (d ell b N k r : Nat)
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
      (finiteOldColumnRawBound E ell d (Finset.range b) c) = upper)
    (hBN : b ≤ N) :
    ∃ (Q : Finset Nat) (F : Nat),
      Q.card = r ∧
      (∀ q ∈ Q, N ≤ q ∧ q < F) ∧
      IsDirectedCliqueOn E Q ∧
      (∀ p, p < N → ∀ q ∈ Q,
        E p q = false ∧ E q p = false) ∧
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range F)
          (supportBlockGappedColumn N Q T.1
            (oldColumnZeroTail b c))) = lower ∧
      feasibleIntegerCliqueVectors d ell
        (finiteOldColumnRawBound E ell d
          (Finset.range N ∪ Q)
          (supportBlockOldColumn Q T.1
            (oldColumnZeroTail b c))) =
        feasibleIntegerCliqueVectors d ell lower ∧
      HasUniformPositiveSupportStage E d ell N F k hd
        (oldColumnZeroTail b c) Q T := by
  have hLater :
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range N)
          (oldColumnZeroTail b c)) = upper :=
    (integerGraphAgeCanonical_zeroTail E ell d b N c hBN).trans hPrior
  exact henson_leftDense_exists_physical_finite_canonical_cover_stage
    d ell N k r hell hd E hAvoid hDense (oldColumnZeroTail b c)
    T lower upper hCover hEll hAt hLater

/-- TWO consecutive GENUINE physical finite cover stages in one
fixed Henson original graph, now separated by an ARBITRARY number
m of intervening original indices.

The second stage uses a deliberately ZEROED future typed column
above the first original cutoff F0; this preserves its canonical
old age at F0+m but need NOT preserve earlier positive future
selected witnesses beyond F0. All physical original E edges remain
unchanged, and both-direction Q0-Q1 nonedges are genuine. -/
theorem henson_leftDense_exists_two_physical_covers_with_zero_gap
    (d ell b m k0 k1 r0 r1 : Nat)
    (hell : 2 ≤ ell) (hd : 0 < d)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool)
    (T0 T1 : IntegerGraphSupport d ell)
    (lower middle upper : IntegerGraphSupport d ell → Nat)
    (hCover0 : AgeCover (IsIntegerGraphAge d ell) middle upper)
    (hCover1 : AgeCover (IsIntegerGraphAge d ell) lower middle)
    (hEll0 : ell = middle T0 + r0 + 1)
    (hAt0 : upper T0 = middle T0 + 1)
    (hEll1 : ell = lower T1 + r1 + 1)
    (hAt1 : middle T1 = lower T1 + 1)
    (hPrior : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) = upper) :
    ∃ (Q0 : Finset Nat) (F0 : Nat) (Q1 : Finset Nat) (F1 : Nat),
      Q0.card = r0 ∧
      (∀ q ∈ Q0, b ≤ q ∧ q < F0) ∧
      Q1.card = r1 ∧
      (∀ q ∈ Q1, F0+m ≤ q ∧ q < F1) ∧
      IsDirectedCliqueOn E Q0 ∧
      IsDirectedCliqueOn E Q1 ∧
      (∀ q0 ∈ Q0, ∀ q1 ∈ Q1,
        E q0 q1 = false ∧ E q1 q0 = false) ∧
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range F0)
          (supportBlockGappedColumn b Q0 T0.1 c)) = middle ∧
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range F1)
          (supportBlockGappedColumn (F0+m) Q1 T1.1
            (oldColumnZeroTail F0
              (supportBlockGappedColumn b Q0 T0.1 c)))) = lower ∧
      HasUniformPositiveSupportStage E d ell b F0 k0 hd c Q0 T0 ∧
      HasUniformPositiveSupportStage E d ell (F0+m) F1 k1 hd
        (oldColumnZeroTail F0 (supportBlockGappedColumn b Q0 T0.1 c))
        Q1 T1 := by
  classical
  obtain ⟨Q0,F0,h0card,h0within,h0clique,_h0iso,h0age,
      _h0feas,h0stage⟩ :=
    henson_leftDense_exists_physical_finite_canonical_cover_stage
      d ell b k0 r0 hell hd E hAvoid hDense c T0
      middle upper hCover0 hEll0 hAt0 hPrior
  have hGap : F0 ≤ F0 + m := Nat.le_add_right F0 m
  let c1 := supportBlockGappedColumn b Q0 T0.1 c
  have hMid :
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range (F0+m))
          (oldColumnZeroTail F0 c1)) = middle :=
    (integerGraphAgeCanonical_zeroTail E ell d F0 (F0+m) c1 hGap).trans h0age
  obtain ⟨Q1,F1,h1card,h1within,h1clique,h1iso,h1age,
      _h1feas,h1stage⟩ :=
    henson_leftDense_exists_physical_finite_canonical_cover_stage
      d ell (F0+m) k1 r1 hell hd E hAvoid hDense
      (oldColumnZeroTail F0 c1) T1
      lower middle hCover1 hEll1 hAt1 hMid
  refine ⟨Q0,F0,Q1,F1,h0card,h0within,h1card,h1within,
    h0clique,h1clique,?_,h0age,?_,h0stage,?_⟩
  · intro q0 hq0 q1 hq1
    exact h1iso q0 (lt_of_lt_of_le (h0within q0 hq0).2 hGap) q1 hq1
  · exact h1age
  · exact h1stage

#print axioms Kk.oldColumnZeroTail
#print axioms Kk.oldSupportCommonNeighbourPool_zeroTail
#print axioms Kk.finiteOldColumnRawBound_zeroTail
#print axioms Kk.finiteOldColumnRawBound_zeroTail_fun
#print axioms Kk.integerGraphAgeCanonical_zeroTail
#print axioms Kk.henson_leftDense_exists_physical_cover_after_zeroTail
#print axioms Kk.henson_leftDense_exists_two_physical_covers_with_zero_gap

end Kk
