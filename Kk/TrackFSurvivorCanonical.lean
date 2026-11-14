import Kk.TrackFSurvivorReindex
import Kk.TrackFMonotoneRawLocality
import Mathlib.Tactic

/-!
# Track F: exact canonical-age survivor reindexing

For any injection f : Fin e ↪ Fin d and a SUPPORT-MONOTONE raw
capacity B on the old d sorts, the genuine finite normalized-clique
canonicalizer satisfies G_(f^*B)(U) = G_B(f(U)).

Unlike the literal raw word identity, this uses both restrictions of
normalized feasible integer weights and an explicit zero extension
along the selected coordinates, verifying every old full support.
Raw monotonicity is essential: arbitrary nonmonotone B fail.

This is a finite dictionary lemma, not the full concrete/abstract
diary inverse or infinite BRD unavoidability.
-/

namespace Kk

/-- Restrict an actual normalized d-sort clique vector to the
surviving e sorts selected injectively by f. -/
noncomputable def trackFRestrictWeights {e d ell : Nat}
    (f : Fin e ↪ Fin d)
    (w : IntegerCliqueWeights d ell) :
    IntegerCliqueWeights e ell := by
  classical
  let v : Fin e → Fin ell := fun i => w.1 (f i)
  have hSum :
      Finset.univ.sum (fun i : Fin e => (v i).val) =
      (Finset.univ.image f).sum (fun j : Fin d => (w.1 j).val) := by
    simp only [v, Finset.sum_image f.injective.injOn]
  have hBound :
      Finset.univ.sum (fun i : Fin e => (v i).val) ≤ ell - 1 := by
    calc
      _ = (Finset.univ.image f).sum
          (fun j : Fin d => (w.1 j).val) := hSum
      _ ≤ Finset.univ.sum (fun j : Fin d => (w.1 j).val) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _)
        intro j _ _
        exact Nat.zero_le _
      _ ≤ ell - 1 := w.2
  exact ⟨v, hBound⟩

/-- Restricting normalized weights preserves their precise masses
on each selected nonempty admissible support. -/
theorem trackFRestrictWeights_mass {e d ell : Nat}
    (f : Fin e ↪ Fin d)
    (w : IntegerCliqueWeights d ell)
    (U : IntegerGraphSupport e ell) :
    integerCliqueOnSupport (trackFRestrictWeights f w) U =
      integerCliqueOnSupport w (trackFMapSupport f U) := by
  classical
  unfold integerCliqueOnSupport
  change U.1.sum (fun i => (w.1 (f i)).val) =
      (U.1.image f).sum (fun j => (w.1 j).val)
  simp only [Finset.sum_image f.injective.injOn]

/-- A selected coordinate gets its original weight; a deleted
coordinate gets zero. This uses the *injectivity* of f in its
definition and is deliberately not a mere arbitrary-function pullback. -/
noncomputable def trackFExtendCoordinate {e d ell : Nat}
    (f : Fin e ↪ Fin d) (hell : 0 < ell)
    (w : Fin e → Fin ell) (j : Fin d) : Fin ell :=
  if h : ∃ i : Fin e, f i = j then
    w (Classical.choose h)
  else ⟨0,hell⟩

/-- The zero extension is exactly the identity on surviving sorts. -/
theorem trackFExtendCoordinate_selected {e d ell : Nat}
    (f : Fin e ↪ Fin d) (hell : 0 < ell)
    (w : Fin e → Fin ell) (i : Fin e) :
    trackFExtendCoordinate f hell w (f i) = w i := by
  classical
  unfold trackFExtendCoordinate
  split_ifs with h
  · have hi : Classical.choose h = i :=
      f.injective (Classical.choose_spec h)
    exact congrArg w hi
  · exact False.elim (h ⟨i,rfl⟩)

/-- A genuinely omitted old coordinate has zero extended weight. -/
theorem trackFExtendCoordinate_outside {e d ell : Nat}
    (f : Fin e ↪ Fin d) (hell : 0 < ell)
    (w : Fin e → Fin ell) (j : Fin d)
    (hj : j ∉ Finset.univ.image f) :
    (trackFExtendCoordinate f hell w j).val = 0 := by
  classical
  have hNone : ¬ ∃ i : Fin e, f i = j := by
    rintro ⟨i,hi⟩
    apply hj
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,hi⟩
  simp [trackFExtendCoordinate,hNone]

/-- Zero-extend normalized survivor weights to all old d sorts,
without changing their total normalized size ≤ ell-1. -/
noncomputable def trackFExtendWeights {e d ell : Nat}
    (f : Fin e ↪ Fin d) (hell : 0 < ell)
    (w : IntegerCliqueWeights e ell) :
    IntegerCliqueWeights d ell := by
  classical
  let v : Fin d → Fin ell := trackFExtendCoordinate f hell w.1
  have hOutSum :
      Finset.univ.sum (fun j : Fin d => (v j).val) =
      (Finset.univ.image f).sum (fun j : Fin d => (v j).val) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j hj hjNot
    exact trackFExtendCoordinate_outside f hell w.1 j hjNot
  have hImageSum :
      (Finset.univ.image f).sum (fun j : Fin d => (v j).val) =
      Finset.univ.sum (fun i : Fin e => (w.1 i).val) := by
    rw [Finset.sum_image f.injective.injOn]
    apply Finset.sum_congr rfl
    intro i _
    simp only [v,trackFExtendCoordinate_selected]
  have hTotal :
      Finset.univ.sum (fun j : Fin d => (v j).val) ≤ ell - 1 := by
    calc
      _ = (Finset.univ.image f).sum (fun j : Fin d => (v j).val) :=
        hOutSum
      _ = Finset.univ.sum (fun i : Fin e => (w.1 i).val) :=
        hImageSum
      _ ≤ ell - 1 := w.2
  exact ⟨v,hTotal⟩

/-- Zero extension preserves the exact mass on every survivor
nonempty support, including the last surviving singleton. -/
theorem trackFExtendWeights_mass {e d ell : Nat}
    (f : Fin e ↪ Fin d) (hell : 0 < ell)
    (w : IntegerCliqueWeights e ell)
    (U : IntegerGraphSupport e ell) :
    integerCliqueOnSupport (trackFExtendWeights f hell w)
      (trackFMapSupport f U) =
    integerCliqueOnSupport w U := by
  classical
  unfold integerCliqueOnSupport
  change (U.1.image f).sum (fun j =>
      (trackFExtendCoordinate f hell w.1 j).val) =
    U.1.sum (fun i => (w.1 i).val)
  rw [Finset.sum_image f.injective.injOn]
  apply Finset.sum_congr rfl
  intro i _
  simp only [trackFExtendCoordinate_selected]

/-- Restricting an actual B-feasible normalized clique vector
preserves feasibility for the EXACT pulled-back raw bound. -/
theorem trackFRestrictWeights_feasible {e d ell : Nat}
    (f : Fin e ↪ Fin d)
    (B : IntegerGraphSupport d ell → Nat)
    (w : IntegerCliqueWeights d ell)
    (hB : WitnessRespects
      (integerCliqueOnSupport (d := d) (ell := ell)) B w) :
    WitnessRespects
      (integerCliqueOnSupport (d := e) (ell := ell))
      (trackFPullbackRaw f B) (trackFRestrictWeights f w) := by
  intro U
  rw [trackFRestrictWeights_mass]
  exact hB (trackFMapSupport f U)

/-- The exact selected old indices inside a full support V. -/
def trackFSelectedPreimage {e d ell : Nat}
    (f : Fin e ↪ Fin d)
    (V : IntegerGraphSupport d ell) : Finset (Fin e) :=
  Finset.univ.filter (fun i : Fin e => f i ∈ V.1)

/-- Its image is exactly the intersection of V with the old
set of survivor coordinates. -/
theorem trackFSelectedPreimage_image {e d ell : Nat}
    (f : Fin e ↪ Fin d)
    (V : IntegerGraphSupport d ell) :
    (trackFSelectedPreimage f V).image f =
      V.1 ∩ Finset.univ.image f := by
  classical
  ext j
  simp only [trackFSelectedPreimage, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
  constructor
  · rintro ⟨i,hi,rfl⟩
    exact ⟨hi,⟨i,Finset.mem_univ i,rfl⟩⟩
  · rintro ⟨hj,⟨i,_,rfl⟩⟩
    exact ⟨i,hj,rfl⟩

/-- The old full-support V-mass of a zero-extended survivor vector
is exactly the survivor mass on the selected preimage of V. -/
theorem trackFExtendWeights_preimage_mass {e d ell : Nat}
    (f : Fin e ↪ Fin d) (hell : 0 < ell)
    (w : IntegerCliqueWeights e ell)
    (V : IntegerGraphSupport d ell) :
    integerCliqueOnSupport (trackFExtendWeights f hell w) V =
      (trackFSelectedPreimage f V).sum
        (fun i => (w.1 i).val) := by
  classical
  let S := trackFSelectedPreimage f V
  let R : Finset (Fin d) := Finset.univ.image f
  unfold integerCliqueOnSupport
  change V.1.sum (fun j => (trackFExtendCoordinate f hell w.1 j).val) =
    S.sum (fun i => (w.1 i).val)
  calc
    V.1.sum (fun j => (trackFExtendCoordinate f hell w.1 j).val) =
      (V.1 ∩ R).sum
        (fun j => (trackFExtendCoordinate f hell w.1 j).val) := by
      symm
      apply Finset.sum_subset (Finset.inter_subset_left)
      intro j hjV hjNot
      have hJnotR : j ∉ R := by
        intro hjR
        exact hjNot (Finset.mem_inter.mpr ⟨hjV,hjR⟩)
      exact trackFExtendCoordinate_outside f hell w.1 j hJnotR
    _ = (S.image f).sum
        (fun j => (trackFExtendCoordinate f hell w.1 j).val) := by
      rw [trackFSelectedPreimage_image]
    _ = S.sum (fun i => (w.1 i).val) := by
      rw [Finset.sum_image f.injective.injOn]
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg Fin.val
        (trackFExtendCoordinate_selected f hell w.1 i)

/-- Zero extension of a survivor raw-feasible vector is B-feasible
on **every old support**, assuming genuine raw support monotonicity.
Empty intersection with selected coordinates is a separate zero case. -/
theorem trackFExtendWeights_feasible {e d ell : Nat}
    (f : Fin e ↪ Fin d) (hell : 0 < ell)
    (B : IntegerGraphSupport d ell → Nat)
    (hMono : TrackFRawSupportMonotone d ell B)
    (w : IntegerCliqueWeights e ell)
    (hPull : WitnessRespects
      (integerCliqueOnSupport (d := e) (ell := ell))
      (trackFPullbackRaw f B) w) :
    WitnessRespects
      (integerCliqueOnSupport (d := d) (ell := ell))
      B (trackFExtendWeights f hell w) := by
  classical
  intro V
  rw [trackFExtendWeights_preimage_mass]
  let S := trackFSelectedPreimage f V
  by_cases hS : S.Nonempty
  · have hCard : S.card ≤ ell - 1 := by
      calc
        S.card = (S.image f).card :=
          (Finset.card_image_of_injective S f.injective).symm
        _ = (V.1 ∩ Finset.univ.image f).card := by
          rw [trackFSelectedPreimage_image]
        _ ≤ V.1.card :=
          Finset.card_le_card (Finset.inter_subset_left)
        _ ≤ ell - 1 := V.2.2
    let U : IntegerGraphSupport e ell := ⟨S,⟨hS,hCard⟩⟩
    have hImageSub : (trackFMapSupport f U).1 ⊆ V.1 := by
      change S.image f ⊆ V.1
      rw [trackFSelectedPreimage_image]
      exact Finset.inter_subset_left
    calc
      S.sum (fun i => (w.1 i).val) =
        integerCliqueOnSupport w U := rfl
      _ ≤ B (trackFMapSupport f U) := hPull U
      _ ≤ B V := hMono (trackFMapSupport f U) V hImageSub
  · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [hEmpty]

/-- The true normalized finite integer-clique canonicalizer commutes
with any injective survivor sorting f, for arbitrary support-MONOTONE
raw bounds B (which need NOT themselves be genuine graph ages). -/
theorem trackFCanonical_reindex_mono {e d ell : Nat}
    (f : Fin e ↪ Fin d) (hell : 0 < ell)
    (B : IntegerGraphSupport d ell → Nat)
    (hMono : TrackFRawSupportMonotone d ell B)
    (U : IntegerGraphSupport e ell) :
    integerGraphAgeCanonical e ell (trackFPullbackRaw f B) U =
      integerGraphAgeCanonical d ell B (trackFMapSupport f U) := by
  classical
  let smallValue := integerCliqueOnSupport (d := e) (ell := ell)
  let largeValue := integerCliqueOnSupport (d := d) (ell := ell)
  apply Nat.le_antisymm
  · change (Finset.univ.filter
      (WitnessRespects smallValue (trackFPullbackRaw f B))).sup
        (fun w => smallValue w U) ≤
      integerGraphAgeCanonical d ell B (trackFMapSupport f U)
    apply Finset.sup_le
    intro w hw
    have hW : WitnessRespects smallValue
        (trackFPullbackRaw f B) w := (Finset.mem_filter.mp hw).2
    have hExt : WitnessRespects largeValue B
        (trackFExtendWeights f hell w) :=
      trackFExtendWeights_feasible f hell B hMono w hW
    calc
      smallValue w U = largeValue (trackFExtendWeights f hell w)
          (trackFMapSupport f U) :=
        (trackFExtendWeights_mass f hell w U).symm
      _ ≤ integerGraphAgeCanonical d ell B
          (trackFMapSupport f U) :=
        witnessValue_le_canonical largeValue B
          (trackFExtendWeights f hell w) hExt _
  · change (Finset.univ.filter
      (WitnessRespects largeValue B)).sup
        (fun w => largeValue w (trackFMapSupport f U)) ≤
      integerGraphAgeCanonical e ell (trackFPullbackRaw f B) U
    apply Finset.sup_le
    intro w hw
    have hW : WitnessRespects largeValue B w :=
      (Finset.mem_filter.mp hw).2
    have hRes : WitnessRespects smallValue (trackFPullbackRaw f B)
        (trackFRestrictWeights f w) :=
      trackFRestrictWeights_feasible f B w hW
    calc
      largeValue w (trackFMapSupport f U) =
          smallValue (trackFRestrictWeights f w) U :=
        (trackFRestrictWeights_mass f w U).symm
      _ ≤ integerGraphAgeCanonical e ell
          (trackFPullbackRaw f B) U :=
        witnessValue_le_canonical smallValue
          (trackFPullbackRaw f B)
          (trackFRestrictWeights f w) hRes U

/-- Exact finite abstract age after deleting/reindexing literal words:
no requirement that old raw word phi was a canonical age itself.
This is the desired dimension-change bridge for the coding step. -/
theorem trackFWordCanonical_reindex {e d ell : Nat}
    (f : Fin e ↪ Fin d) (hell : 0 < ell)
    (cols : List (Fin d → Nat))
    (U : IntegerGraphSupport e ell) :
    integerGraphAgeCanonical e ell
      (trackFWordRaw e ell (trackFRestrictColumns f cols)) U =
    integerGraphAgeCanonical d ell
      (trackFWordRaw d ell cols) (trackFMapSupport f U) := by
  rw [trackFWordRaw_restrict_columns]
  exact trackFCanonical_reindex_mono f hell
    (trackFWordRaw d ell cols)
    (fun S T hST => trackFWordRaw_monotone cols S T hST) U

end Kk
