import Kk.OneGapPartialStructure
import Kk.FiniteCliqueEmbeddingTransport

/-!
# Exact ordinary ages through finite images and one-gap padding

Common-neighbour pools transport through induced finite images. In
one-gap padding, every support is nonempty, so dummy rows cannot survive
its positive-column filter. The remaining rows are the exact address
image of the unpadded pool, preserving raw and canonical age functions.

English proof and independent review precede this implementation:
`docs/one_gap_age_transport_english_20261127.md`.
-/

namespace Kk

/-- Typed common-neighbour pools commute with a finite image whenever
the full columns agree on that image. No injectivity is needed here. -/
theorem oldSupportCommonNeighbourPool_image_eq
    {d : Nat} (P : Finset Nat) (c c' : Nat → Fin d → Bool)
    (f : Nat → Nat) (T : Finset (Fin d))
    (hColumns : ∀ x ∈ P, ∀ i, c' (f x) i = c x i) :
    oldSupportCommonNeighbourPool (P.image f) c' T =
      (oldSupportCommonNeighbourPool P c T).image f := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨hyP, hAll⟩ := Finset.mem_filter.mp hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hyP
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩, rfl⟩
    intro i hi
    exact (hColumns x hx i).symm.trans (hAll i hi)
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxP, hAll⟩ := Finset.mem_filter.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨x, hxP, rfl⟩, ?_⟩
    intro i hi
    exact (hColumns x hxP i).trans (hAll i hi)

/-- A finite induced image preserves the entire raw old-column bound.
Only off-diagonal graph agreement on the old pool is required. -/
theorem finiteOldColumnRawBound_induced_image_eq
    (E F : Nat → Nat → Bool) (ell d : Nat) (P : Finset Nat)
    (c c' : Nat → Fin d → Bool) (f : Nat → Nat)
    (hInj : Function.Injective f)
    (hEdges : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → F (f x) (f y) = E x y)
    (hColumns : ∀ x ∈ P, ∀ i, c' (f x) i = c x i) :
    finiteOldColumnRawBound F ell d (P.image f) c' =
      finiteOldColumnRawBound E ell d P c := by
  funext T
  unfold finiteOldColumnRawBound
  rw [oldSupportCommonNeighbourPool_image_eq P c c' f T.1 hColumns]
  have hCapacity := finiteDirectedCliqueCapacity_induced_image_eq E F
    (oldSupportCommonNeighbourPool P c T.1) f
    (fun _ _ _ _ hEq => hInj hEq)
    (fun x hx y hy hxy =>
      (hEdges x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy).symm)
  exact congrArg (fun capacity => ell - 1 - capacity) hCapacity

/-- The same induced image preserves the full jointly canonical age. -/
theorem integerGraphAgeCanonical_induced_image_eq
    (E F : Nat → Nat → Bool) (ell d : Nat) (P : Finset Nat)
    (c c' : Nat → Fin d → Bool) (f : Nat → Nat)
    (hInj : Function.Injective f)
    (hEdges : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → F (f x) (f y) = E x y)
    (hColumns : ∀ x ∈ P, ∀ i, c' (f x) i = c x i) :
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound F ell d (P.image f) c') =
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d P c) := by
  rw [finiteOldColumnRawBound_induced_image_eq E F ell d P c c' f
    hInj hEdges hColumns]

/-- Dummy rows cannot be common neighbours of a nonempty support. Thus
only the meaningful address image remains, for any finite padded pool. -/
theorem oneGap_commonNeighbourPool_eq_image
    (g : Nat → Nat → Bool) (ell d : Nat) (P Q : Finset Nat)
    (selected : Fin d → Nat)
    (hPositions : ∀ q, oneGapAddress q ∈ Q ↔ q ∈ P)
    (T : IntegerGraphSupport d ell) :
    oldSupportCommonNeighbourPool Q
        (fun v i => oneGapEdge g v (oneGapAddress (selected i))) T.1 =
      (oldSupportCommonNeighbourPool P (fun q i => g q (selected i)) T.1).image
        oneGapAddress := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨hvQ, hAll⟩ := Finset.mem_filter.mp hv
    obtain ⟨i, hi⟩ := T.2.1
    have hReal : oneGapReal v := (oneGapEdge_real g (hAll i hi)).1
    have hAddress := oneGapAddress_index hReal
    apply Finset.mem_image.mpr
    refine ⟨oneGapIndex v, Finset.mem_filter.mpr ⟨?_, ?_⟩, hAddress⟩
    · exact (hPositions (oneGapIndex v)).mp (hAddress.symm ▸ hvQ)
    · intro j hj
      calc
        g (oneGapIndex v) (selected j) =
            oneGapEdge g (oneGapAddress (oneGapIndex v)) (oneGapAddress (selected j)) :=
          (oneGapEdge_address g (oneGapIndex v) (selected j)).symm
        _ = true := by simpa only [hAddress] using hAll j hj
  · intro hv
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hqP, hAll⟩ := Finset.mem_filter.mp hq
    apply Finset.mem_filter.mpr
    refine ⟨(hPositions q).mpr hqP, ?_⟩
    intro i hi
    exact (oneGapEdge_address g q (selected i)).trans (hAll i hi)

/-- Exact raw-age transport for any padded finite pool having precisely
the prescribed meaningful positions. Extra dummy rows do not contribute. -/
theorem oneGap_rawBound_eq_of_positions
    (g : Nat → Nat → Bool) (ell d : Nat) (P Q : Finset Nat)
    (selected : Fin d → Nat)
    (hPositions : ∀ q, oneGapAddress q ∈ Q ↔ q ∈ P) :
    finiteOldColumnRawBound (oneGapEdge g) ell d Q
      (fun v i => oneGapEdge g v (oneGapAddress (selected i))) =
    finiteOldColumnRawBound g ell d P (fun q i => g q (selected i)) := by
  funext T
  unfold finiteOldColumnRawBound
  rw [oneGap_commonNeighbourPool_eq_image g ell d P Q selected hPositions T]
  have hCapacity := finiteDirectedCliqueCapacity_induced_image_eq
    g (oneGapEdge g)
    (oldSupportCommonNeighbourPool P (fun q i => g q (selected i)) T.1)
    oneGapAddress
    (fun _ _ _ _ hEq => oneGapAddress_strictMono.injective hEq)
    (fun x _hx y _hy _hxy => (oneGapEdge_address g x y).symm)
  exact congrArg (fun capacity => ell - 1 - capacity) hCapacity

/-- Before a meaningful coordinate, padding has exactly the original
strict prefix as its meaningful old positions. -/
theorem oneGap_rawBound_before_eq
    (g : Nat → Nat → Bool) (ell d p : Nat) (selected : Fin d → Nat) :
    finiteOldColumnRawBound (oneGapEdge g) ell d (Finset.range (oneGapAddress p))
      (fun v i => oneGapEdge g v (oneGapAddress (selected i))) =
    finiteOldColumnRawBound g ell d (Finset.range p) (fun q i => g q (selected i)) := by
  apply oneGap_rawBound_eq_of_positions
  intro q
  simp only [Finset.mem_range]
  unfold oneGapAddress
  omega

/-- After that same meaningful coordinate, its unpadded vertex is included.
The padded cutoff is address p plus one, not address (p+1). -/
theorem oneGap_rawBound_after_eq
    (g : Nat → Nat → Bool) (ell d p : Nat) (selected : Fin d → Nat) :
    finiteOldColumnRawBound (oneGapEdge g) ell d (Finset.range (oneGapAddress p + 1))
      (fun v i => oneGapEdge g v (oneGapAddress (selected i))) =
    finiteOldColumnRawBound g ell d (Finset.range (p+1)) (fun q i => g q (selected i)) := by
  apply oneGap_rawBound_eq_of_positions
  intro q
  simp only [Finset.mem_range]
  unfold oneGapAddress
  omega

theorem oneGap_canonicalAge_before_eq
    (g : Nat → Nat → Bool) (ell d p : Nat) (selected : Fin d → Nat) :
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound (oneGapEdge g) ell d (Finset.range (oneGapAddress p))
        (fun v i => oneGapEdge g v (oneGapAddress (selected i)))) =
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound g ell d (Finset.range p) (fun q i => g q (selected i))) := by
  rw [oneGap_rawBound_before_eq]

theorem oneGap_canonicalAge_after_eq
    (g : Nat → Nat → Bool) (ell d p : Nat) (selected : Fin d → Nat) :
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound (oneGapEdge g) ell d (Finset.range (oneGapAddress p + 1))
        (fun v i => oneGapEdge g v (oneGapAddress (selected i)))) =
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound g ell d (Finset.range (p+1)) (fun q i => g q (selected i))) := by
  rw [oneGap_rawBound_after_eq]

/-- Complete unpadded canonical-age neutrality transports to the padded cut. -/
theorem oneGap_canonicalAge_neutral_of_unpadded
    (g : Nat → Nat → Bool) (ell d p : Nat) (selected : Fin d → Nat)
    (hAge : integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound g ell d (Finset.range p) (fun q i => g q (selected i))) =
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound g ell d (Finset.range (p+1)) (fun q i => g q (selected i)))) :
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound (oneGapEdge g) ell d (Finset.range (oneGapAddress p))
        (fun v i => oneGapEdge g v (oneGapAddress (selected i)))) =
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound (oneGapEdge g) ell d (Finset.range (oneGapAddress p + 1))
        (fun v i => oneGapEdge g v (oneGapAddress (selected i)))) := by
  rw [oneGap_canonicalAge_before_eq, oneGap_canonicalAge_after_eq]
  exact hAge

/-- Complete ordinary old-column equality is unchanged by inserting dummy rows. -/
theorem oneGap_oldColumns_before_iff
    (g : Nat → Nat → Bool) (p u v : Nat) :
    (∀ q, q < oneGapAddress p →
      oneGapEdge g q (oneGapAddress u) = oneGapEdge g q (oneGapAddress v)) ↔
      ∀ q, q < p → g q u = g q v := by
  constructor
  · intro h q hq
    have hBits := h (oneGapAddress q) (oneGapAddress_strictMono hq)
    simpa only [oneGapEdge_address] using hBits
  · intro h q hq
    by_cases hReal : oneGapReal q
    · have hAddress := oneGapAddress_index hReal
      have hOld : oneGapIndex q < p := by
        unfold oneGapAddress at hAddress hq
        omega
      have hBits : oneGapEdge g (oneGapAddress (oneGapIndex q)) (oneGapAddress u) =
          oneGapEdge g (oneGapAddress (oneGapIndex q)) (oneGapAddress v) := by
        simpa only [oneGapEdge_address] using h (oneGapIndex q) hOld
      simpa only [hAddress] using hBits
    · simp [oneGapEdge, hReal]

/-- An ordinary no-split implication on a selected list survives one-gap padding. -/
theorem oneGap_noSplit_of_unpadded
    (g : Nat → Nat → Bool) (d p : Nat) (selected : Fin d → Nat)
    (hNoSplit : ∀ i j : Fin d,
      (∀ q, q < p → g q (selected i) = g q (selected j)) →
        g p (selected i) = g p (selected j)) :
    ∀ i j : Fin d,
      (∀ q, q < oneGapAddress p →
        oneGapEdge g q (oneGapAddress (selected i)) =
          oneGapEdge g q (oneGapAddress (selected j))) →
      oneGapEdge g (oneGapAddress p) (oneGapAddress (selected i)) =
        oneGapEdge g (oneGapAddress p) (oneGapAddress (selected j)) := by
  intro i j hOld
  have hBits := hNoSplit i j
    ((oneGap_oldColumns_before_iff g p (selected i) (selected j)).mp hOld)
  simpa only [oneGapEdge_address] using hBits

end Kk
