import Kk.TrackEOriginalPrefixSocleCover
import Kk.TrackDEvenRealNoI1
import Kk.TrackEOldBoringBareRootNoSeed
import Mathlib.Tactic

/-!
# Track C: genuine one-bare-root source no-novelty at a positive even-real zero stage

English proof and hostile audit were committed first:
  docs/track_c_onebare_evenreal_zero_quiet_english_audit_20261120.md

For one genuine old Kpt AlgorithmRun with arbitrary old dependent seeds,
adjoin precisely ONE real H+ original. At an old-unselected positive
even-real cut, its initial seed cannot end there (E76). With ZERO
ordinary L on every actual eligible stage original, D389 also excludes
ALL generated Kpt meet/parameter I1 terminals. With complete OLD Kpt
prefix witnesses for every active representing original, E74 gives
full same-node old/upper L+/E crossing containment (I2 fork safe).

The result concerns closure under the OLD selected tail, NOT yet a
separately computed new run, global diary schedule or BRD theorem.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- One true BARE numerical-H+ new original, with all original
stage zero-bits and complete OLD Kpt prefix witnesses, yields
actual FULL source no-novelty at each OLD-UNSELECTED positive real
cut. There is no independent "no initial seed terminal" or
"no generated I1" assumption.

All finite original columns, including coding/gap vertices, matter.
The new source is EXACTLY X union one literal physical original,
not the invalid whole ancestor-prefix pool. -/
theorem finiteNumericH_oldBoring_oneBare_real_zero_noNovelty
    (family : List (NormalizedForbidden 1 0 1))
    (K : AgeTestModel 1 0 1) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hSym : ∀ i j : Nat,
      (finiteNumericH K k N).L.binary i j (0 : Fin 1) =
        (finiteNumericH K k N).L.binary j i (0 : Fin 1))
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (newV : Fin N)
    (hBare : Y = X ∪
      ({(finiteNumericH K k N).kptOriginal family hAvoid newV} :
        Set (AdmissibleKptNode family)))
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid (U : Set (Fin N)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (idx g : Nat)
    (hPositive : 0 < hPosition k idx g)
    (hCut : hPosition k idx g < top)
    (hOldUnselected :
      hPosition k idx g ∉ R.I (hPosition k idx g))
    (hZeroStage : ∀ v : Fin N,
      v ∈ hStageOriginals K k N U
        (R.I (hPosition k idx g+1)) →
      hPosition k idx g+1 ≤
        (finiteNumericH K k N).freeLevel v.val →
      (finiteNumericH K k N).L.binary
        (hPosition k idx g) v.val (0 : Fin 1) = false)
    (hOriginalPrefix : ∀ (v : Fin N),
      v ∈ hStageOriginals K k N U
        (R.I (hPosition k idx g+1)) →
      (∃ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family)
          (R.I (hPosition k idx g+1)) Y ∧
        hPosition k idx g < LevelTree.lev z ∧
        z ≤ (finiteNumericH K k N).kptOriginal family hAvoid v) →
      ∃ w : AdmissibleKptNode family,
        w ∈ SMTree.Envelope.closure
          (admissibleKptSTree family)
          (R.I (hPosition k idx g+1)) X ∧
        ∃ (hV : hPosition k idx g < LevelTree.lev
          ((finiteNumericH K k N).kptOriginal family hAvoid v))
          (hW : hPosition k idx g < LevelTree.lev w),
          LevelTree.ancestor
            ((finiteNumericH K k N).kptOriginal family hAvoid v)
            (hPosition k idx g) (Nat.le_of_lt hV) =
          LevelTree.ancestor w (hPosition k idx g)
            (Nat.le_of_lt hW)) :
    NewRootNoNoveltyAtCut family
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (hPosition k idx g+1)) X)
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (hPosition k idx g+1)) Y)
      (hPosition k idx g) := by
  classical
  let cut : Nat := hPosition k idx g
  let A : EnumeratedPartialStructure 1 0 1 := finiteNumericH K k N
  have hXY : X ⊆ Y := by
    intro x hx
    rw [hBare]
    exact Or.inl hx
  have hNoSeedBare :
      ¬ ∃ y : AdmissibleKptNode family,
        y ∈ (X ∪
          ({(finiteNumericH K k N).kptOriginal family hAvoid newV} :
            Set (AdmissibleKptNode family))) ∧
        LevelTree.lev y = cut :=
    finiteNumericH_oldUnselected_bare_root_no_positive_real_seed
      family K k N hAvoid X top R newV idx g
      hPositive hCut hOldUnselected
  have hNoYSeed :
      ¬ ∃ y : AdmissibleKptNode family,
        y ∈ Y ∧ LevelTree.lev y = cut := by
    rintro ⟨y, hy, hLev⟩
    apply hNoSeedBare
    exact ⟨y, by simpa only [hBare] using hy, hLev⟩
  have hZeroAmbient :
      ∀ v : Fin A.size,
        v ∈ ambientStagePool A
          (U : Set (Fin N)) (R.I (cut+1)) →
        cut+1 ≤ A.freeLevel v.val →
        A.L.binary cut v.val (0 : Fin 1) = false := by
    intro v hv hFree
    have hMember :
        v ∈ U ∨
          (v.val ∈ R.I (cut+1) ∧ 0 < A.freeLevel v.val) := by
      change v ∈ (U : Set (Fin N)) ∪
        {i : Fin N | i.val ∈ R.I (cut+1) ∧
          0 < A.freeLevel i.val} at hv
      rcases hv with hRoot | hParam
      · exact Or.inl (Finset.mem_coe.mp hRoot)
      · exact Or.inr hParam
    let V : Finset (Fin N) :=
      hStageOriginals K k N U (R.I (cut+1))
    have hvV : v ∈ V := by
      change v ∈ Finset.univ.filter
        (fun x : Fin N => x ∈ U ∨
          (x.val ∈ R.I (cut+1) ∧ 0 < A.freeLevel x.val))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hMember
    exact hZeroStage v hvV hFree
  have hNoI1 :
      ¬ KptI1AtCut family
        (SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) Y) cut := by
    change ¬ ∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y ∧
      LevelTree.lev z = cut
    exact finiteNumericH_even_real_no_full_I1_of_zero_stage
      family K k N hAvoid hSym (R.I (cut+1)) Y
      (U : Set (Fin N)) hY idx g hPositive
      hNoYSeed hZeroAmbient
  have hCross :
      FullPhysicalClosureCrossing family
        (SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) Y) cut ⊆
      FullPhysicalClosureCrossing family
        (SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) X) cut := by
    exact finiteNumericH_candidate_zero_stage_original_prefixes_cover_full_crossings
      family K k N hAvoid hSym U X Y hXY hY
      top R cut hZeroStage hOriginalPrefix
  constructor
  · intro hNewI1
    exact (hNoI1 hNewI1).elim
  · exact hCross

end Kk

#check @Kk.finiteNumericH_oldBoring_oneBare_real_zero_noNovelty
#print axioms Kk.finiteNumericH_oldBoring_oneBare_real_zero_noNovelty
