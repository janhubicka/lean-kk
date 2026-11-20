import Kk.SupportImageAge
import Kk.TrackFMonotoneRawLocality
import Mathlib.Tactic

/-!
# Canonical graph ages under arbitrary maps of sorts

The English proof and independent audit were committed first in
`docs/track_b_canonical_sort_pullback_english_audit.md`.

Unlike injective survivor restriction, a split may give several children
the same parent. Pushforward must SUM their weights. The preimage of an
old support may be too large; its positive-weight part is admissible.
Lifting uses one representative inside the requested new support per
parent. No parent multiplicity is copied to two children.

These are finite ordinary graph-age identities. They do not insert a
pivot or transport a parameter-closed auxiliary Kpt source.
-/

namespace Kk

private theorem sortFibreSum_on_finset {e d : Nat}
    (pi : Fin e → Fin d) (w : Fin e → Nat) (S : Finset (Fin d)) :
    S.sum (fun j => (Finset.univ.filter (fun i => pi i = j)).sum w) =
      (Finset.univ.filter (fun i => pi i ∈ S)).sum w := by
  classical
  exact Finset.sum_fiberwise_eq_sum_filter Finset.univ S pi w

/-- Sum all multiplicities in a parent fibre. Total normalized mass
is preserved, including when several positive children share a parent. -/
noncomputable def integerCliquePushforward {e d ell : Nat}
    (pi : Fin e → Fin d) (hell : 0 < ell)
    (w : IntegerCliqueWeights e ell) : IntegerCliqueWeights d ell := by
  classical
  let a : Fin d → Nat := fun j =>
    (Finset.univ.filter (fun i => pi i = j)).sum (fun i => (w.1 i).val)
  have hCoord (j : Fin d) : a j < ell := by
    have hLe : a j ≤ Finset.univ.sum (fun i => (w.1 i).val) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro i _ _
      exact Nat.zero_le _
    have hTotal := w.2
    omega
  have hSum : Finset.univ.sum a =
      Finset.univ.sum (fun i => (w.1 i).val) := by
    simpa [a] using
      sortFibreSum_on_finset pi (fun i => (w.1 i).val) Finset.univ
  refine ⟨(fun j => ⟨a j, hCoord j⟩), ?_⟩
  change Finset.univ.sum a ≤ ell - 1
  rw [hSum]
  exact w.2

/-- Exact pushforward mass on any finite parent set; no cardinality
restriction is imposed on its preimage. -/
theorem integerCliquePushforward_mass_on_finset {e d ell : Nat}
    (pi : Fin e → Fin d) (hell : 0 < ell)
    (w : IntegerCliqueWeights e ell) (S : Finset (Fin d)) :
    S.sum (fun j => ((integerCliquePushforward pi hell w).1 j).val) =
      (Finset.univ.filter (fun i => pi i ∈ S)).sum
        (fun i => (w.1 i).val) := by
  change S.sum (fun j =>
      (Finset.univ.filter (fun i => pi i = j)).sum (fun i => (w.1 i).val)) = _
  exact sortFibreSum_on_finset pi (fun i => (w.1 i).val) S

theorem integerCliquePushforward_mass {e d ell : Nat}
    (pi : Fin e → Fin d) (hell : 0 < ell)
    (w : IntegerCliqueWeights e ell) (S : IntegerGraphSupport d ell) :
    integerCliqueOnSupport (integerCliquePushforward pi hell w) S =
      (Finset.univ.filter (fun i => pi i ∈ S.1)).sum
        (fun i => (w.1 i).val) :=
  integerCliquePushforward_mass_on_finset pi hell w S.1

/-- A support may omit siblings of its members. Consequently its mass
is at most, rather than necessarily equal to, the mass of its image. -/
theorem integerCliquePushforward_image_mass_ge {e d ell : Nat}
    (pi : Fin e → Fin d) (hell : 0 < ell)
    (w : IntegerCliqueWeights e ell) (U : IntegerGraphSupport e ell) :
    integerCliqueOnSupport w U ≤
      integerCliqueOnSupport (integerCliquePushforward pi hell w)
        (integerGraphSupportImage pi U) := by
  classical
  rw [integerCliquePushforward_mass]
  unfold integerCliqueOnSupport
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
  · intro i _ _
    exact Nat.zero_le _

/-- A feasible child vector aggregates to a feasible parent vector
for a support-monotone raw bound. The positive preimage, not the full
preimage, supplies the admissible support used in the proof. -/
theorem integerCliquePushforward_feasible {e d ell : Nat}
    (pi : Fin e → Fin d) (hell : 0 < ell)
    (B : IntegerGraphSupport d ell → Nat)
    (hMono : TrackFRawSupportMonotone d ell B)
    (w : IntegerCliqueWeights e ell)
    (hw : WitnessRespects (integerCliqueOnSupport (d := e) (ell := ell))
      (fun U => B (integerGraphSupportImage pi U)) w) :
    WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell)) B
      (integerCliquePushforward pi hell w) := by
  classical
  intro S
  rw [integerCliquePushforward_mass]
  let P : Finset (Fin e) := Finset.univ.filter (fun i => pi i ∈ S.1)
  let Q : Finset (Fin e) := P.filter (fun i => 0 < (w.1 i).val)
  have hQP : Q ⊆ P := Finset.filter_subset _ _
  have hMass : Q.sum (fun i => (w.1 i).val) =
      P.sum (fun i => (w.1 i).val) := by
    apply Finset.sum_subset hQP
    intro i hi hiNot
    have hNotPos : ¬ 0 < (w.1 i).val := by
      intro hPos
      exact hiNot (Finset.mem_filter.mpr ⟨hi, hPos⟩)
    omega
  change P.sum (fun i => (w.1 i).val) ≤ B S
  rw [← hMass]
  by_cases hQ : Q.Nonempty
  · have hCard : Q.card ≤ ell - 1 := by
      calc
        Q.card = Q.sum (fun _ => (1 : Nat)) := by simp
        _ ≤ Q.sum (fun i => (w.1 i).val) := by
          apply Finset.sum_le_sum
          intro i hi
          exact (Finset.mem_filter.mp hi).2
        _ ≤ Finset.univ.sum (fun i => (w.1 i).val) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Q)
          intro i _ _
          exact Nat.zero_le _
        _ ≤ ell - 1 := w.2
    let T : IntegerGraphSupport e ell := ⟨Q, hQ, hCard⟩
    have hImage : (integerGraphSupportImage pi T).1 ⊆ S.1 := by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact (Finset.mem_filter.mp (hQP hi)).2
    exact (hw T).trans (hMono (integerGraphSupportImage pi T) S hImage)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hQ]

private theorem zeroOutside_sum_on_finset {d ell : Nat}
    (hell : 0 < ell) (w : IntegerCliqueWeights d ell)
    (R S : Finset (Fin d)) :
    S.sum (fun j => ((trackFZeroOutside d ell hell w R).1 j).val) =
      (S ∩ R).sum (fun j => (w.1 j).val) := by
  classical
  calc
    S.sum (fun j => ((trackFZeroOutside d ell hell w R).1 j).val) =
        (S ∩ R).sum
          (fun j => ((trackFZeroOutside d ell hell w R).1 j).val) := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro j hjS hjNot
      have hjR : j ∉ R := by
        intro h
        exact hjNot (Finset.mem_inter.mpr ⟨hjS, h⟩)
      simp [trackFZeroOutside, hjR]
    _ = (S ∩ R).sum (fun j => (w.1 j).val) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [trackFZeroOutside, (Finset.mem_inter.mp hj).2]

/-- Every feasible old vector can be lifted into a requested new
support with exactly the old image mass. One chosen representative per
parent receives its entire weight; all remaining children receive zero.
This direction requires no monotonicity of the old raw bound. -/
theorem integerClique_exists_lift_along_sortMap {e d ell : Nat}
    (pi : Fin e → Fin d) (hell : 0 < ell)
    (B : IntegerGraphSupport d ell → Nat)
    (w : IntegerCliqueWeights d ell)
    (hw : WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell)) B w)
    (U : IntegerGraphSupport e ell) :
    ∃ z : IntegerCliqueWeights e ell,
      WitnessRespects (integerCliqueOnSupport (d := e) (ell := ell))
        (fun V => B (integerGraphSupportImage pi V)) z ∧
      integerCliqueOnSupport z U =
        integerCliqueOnSupport w (integerGraphSupportImage pi U) := by
  classical
  obtain ⟨u₀, hu₀⟩ := U.2.1
  let R := U.1.image pi
  have hRep (j : Fin d) (hj : j ∈ R) :
      ∃ i : Fin e, i ∈ U.1 ∧ pi i = j := Finset.mem_image.mp hj
  let rep : Fin d → Fin e := fun j =>
    if hj : j ∈ R then Classical.choose (hRep j hj) else u₀
  have hRepMem (j : Fin d) : rep j ∈ U.1 := by
    dsimp only [rep]
    split_ifs with hj
    · exact (Classical.choose_spec (hRep j hj)).1
    · exact hu₀
  have hRepPi (j : Fin d) (hj : j ∈ R) : pi (rep j) = j := by
    simp only [rep, dite_eq_left hj]
    exact (Classical.choose_spec (hRep j hj)).2
  let w₀ := trackFZeroOutside d ell hell w R
  let z := integerCliquePushforward rep hell w₀
  refine ⟨z, ?_, ?_⟩
  · intro V
    change integerCliqueOnSupport (integerCliquePushforward rep hell w₀) V ≤ _
    rw [integerCliquePushforward_mass]
    rw [zeroOutside_sum_on_finset]
    have hSub : (Finset.univ.filter (fun j => rep j ∈ V.1)) ∩ R ⊆
        (integerGraphSupportImage pi V).1 := by
      intro j hj
      obtain ⟨hjV, hjR⟩ := Finset.mem_inter.mp hj
      exact Finset.mem_image.mpr
        ⟨rep j, (Finset.mem_filter.mp hjV).2, hRepPi j hjR⟩
    calc
      _ ≤ (integerGraphSupportImage pi V).1.sum (fun j => (w.1 j).val) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hSub
        intro j _ _
        exact Nat.zero_le _
      _ ≤ B (integerGraphSupportImage pi V) := hw _
  · change integerCliqueOnSupport (integerCliquePushforward rep hell w₀) U = _
    rw [integerCliquePushforward_mass]
    rw [zeroOutside_sum_on_finset]
    have hAll : Finset.univ.filter (fun j => rep j ∈ U.1) = Finset.univ := by
      ext j
      simp [hRepMem j]
    rw [hAll, Finset.univ_inter]
    rfl

/-- Canonicalization commutes with the image pullback along ANY map
of finite sorts, including noninjective splitting maps, for a
support-monotone raw bound. No genuine-age premise on B is needed. -/
theorem integerGraphAgeCanonical_pullback_mono {e d ell : Nat}
    (pi : Fin e → Fin d) (hell : 0 < ell)
    (B : IntegerGraphSupport d ell → Nat)
    (hMono : TrackFRawSupportMonotone d ell B)
    (U : IntegerGraphSupport e ell) :
    integerGraphAgeCanonical e ell
        (fun V => B (integerGraphSupportImage pi V)) U =
      integerGraphAgeCanonical d ell B (integerGraphSupportImage pi U) := by
  classical
  let newValue := integerCliqueOnSupport (d := e) (ell := ell)
  let oldValue := integerCliqueOnSupport (d := d) (ell := ell)
  let B' := fun V => B (integerGraphSupportImage pi V)
  apply Nat.le_antisymm
  · change (Finset.univ.filter (WitnessRespects newValue B')).sup
        (fun w => newValue w U) ≤ _
    apply Finset.sup_le
    intro w hw
    have hFeasible : WitnessRespects newValue B' w := (Finset.mem_filter.mp hw).2
    have hPush := integerCliquePushforward_feasible pi hell B hMono w hFeasible
    calc
      newValue w U ≤ oldValue (integerCliquePushforward pi hell w)
          (integerGraphSupportImage pi U) :=
        integerCliquePushforward_image_mass_ge pi hell w U
      _ ≤ integerGraphAgeCanonical d ell B (integerGraphSupportImage pi U) :=
        witnessValue_le_canonical oldValue B (integerCliquePushforward pi hell w)
          hPush _
  · change (Finset.univ.filter (WitnessRespects oldValue B)).sup
        (fun w => oldValue w (integerGraphSupportImage pi U)) ≤ _
    apply Finset.sup_le
    intro w hw
    have hFeasible : WitnessRespects oldValue B w := (Finset.mem_filter.mp hw).2
    obtain ⟨z, hz, hMass⟩ :=
      integerClique_exists_lift_along_sortMap pi hell B w hFeasible U
    calc
      oldValue w (integerGraphSupportImage pi U) = newValue z U := hMass.symm
      _ ≤ integerGraphAgeCanonical e ell B' U :=
        witnessValue_le_canonical newValue B' z hz U

/-- A genuine normalized positive integer graph age pulls back to
a genuine age under arbitrary splitting/deletion of sorts. -/
theorem isIntegerGraphAge_pullback {e d ell : Nat}
    (pi : Fin e → Fin d) (hell : 0 < ell)
    (F : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell F) :
    IsIntegerGraphAge e ell (fun U => F (integerGraphSupportImage pi U)) := by
  constructor
  · intro U
    exact hAge.1 (integerGraphSupportImage pi U)
  · intro U
    obtain ⟨w, hw, hMass⟩ := hAge.2 (integerGraphSupportImage pi U)
    obtain ⟨z, hz, hzMass⟩ :=
      integerClique_exists_lift_along_sortMap pi hell F w hw U
    exact ⟨z, hz, hzMass.trans hMass⟩

end Kk
