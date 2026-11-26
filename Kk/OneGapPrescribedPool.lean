import Kk.OneGapPlannedEnvelope
import SuccessorTree.V10.I3EligibleStagePool
import SuccessorTree.V10.M2B3CopyCases
import Mathlib.Tactic

/-!
# The actual prescription on the complete retained original pool

Every source and target comes from the same eligible retained ambient name.
Complete next-type fibre agreement makes the chosen representative agree
with every crossing of the represented closure. The resulting full B3 and
one-gap map use the selected-positive obstruction theorem, including all
retained auxiliary names and the cap.
-/

namespace Kk
open SuccessorTree
open SuccessorTree.V10

/-- The complete retained pool, filtered by the genuine free cut. -/
noncomputable def oneGapRetainedPoolData
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd) (cut : Nat)
    (V : Set (Fin A.size)) : PrescribedBoringData cut db du dd :=
  eligibleAmbientPoolPrescribedData A cut (fun v : Fin A.size => v.val)
    (fun v => v ∈ V ∧ cut+1 ≤ A.freeLevel v.val)

/-- The same actual original witnesses old type, next type and eligibility. -/
theorem oneGapRetainedPoolData_source_original
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd) (cut : Nat)
    (V : Set (Fin A.size)) (T : PartialTypeWithE cut db du dd)
    (hT : T ∈ (oneGapRetainedPoolData A cut V).source) :
    ∃ v : Fin A.size, v ∈ V ∧ cut+1 ≤ A.freeLevel v.val ∧
      T = A.partialTypeAt cut v.val ∧
      (oneGapRetainedPoolData A cut V).target T =
        A.partialTypeAt (cut+1) v.val := by
  obtain ⟨v,⟨hv,hCut⟩,hOld,hNew⟩ :=
    eligibleAmbientPoolPrescribedData_source_original
      A cut (fun v : Fin A.size => v.val)
      (fun v => v ∈ V ∧ cut+1 ≤ A.freeLevel v.val) T hT
  exact ⟨v,hv,hCut,hOld,hNew⟩

/-- Duplicate old records do not lose any required crossing: the chosen
target is the next type of each eligible representative. -/
theorem oneGapRetainedPoolData_target_eq
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd) (cut : Nat)
    (V : Set (Fin A.size))
    (hFibre : ∀ v ∈ V, ∀ w ∈ V,
      cut+1 ≤ A.freeLevel v.val → cut+1 ≤ A.freeLevel w.val →
      A.partialTypeAt cut v.val = A.partialTypeAt cut w.val →
      A.partialTypeAt (cut+1) v.val = A.partialTypeAt (cut+1) w.val)
    (v : Fin A.size) (hv : v ∈ V) (hCut : cut+1 ≤ A.freeLevel v.val) :
    (oneGapRetainedPoolData A cut V).target (A.partialTypeAt cut v.val) =
      A.partialTypeAt (cut+1) v.val := by
  have hSource : A.partialTypeAt cut v.val ∈
      (oneGapRetainedPoolData A cut V).source :=
    ⟨v,⟨hv,hCut⟩,rfl⟩
  obtain ⟨w,hw,hWCut,hOld,hNew⟩ :=
    oneGapRetainedPoolData_source_original A cut V _ hSource
  exact hNew.trans (hFibre w hw v hv hWCut hCut hOld.symm)

/-- Every chosen output is a genuine admissible ambient prefix. -/
theorem oneGapRetainedPoolData_targets_admissible
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (cut : Nat) (V : Set (Fin A.size)) :
    ∀ T, T ∈ (oneGapRetainedPoolData A cut V).source →
      IsAdmissibleRawType family
        (⟨cut+1,(oneGapRetainedPoolData A cut V).target T⟩ :
          RawPartialTypeNode db du dd) := by
  intro T hT
  obtain ⟨v,_hv,hCut,_hOld,hNew⟩ :=
    oneGapRetainedPoolData_source_original A cut V T hT
  rw [hNew]
  have hAd : IsAdmissibleRawType family (A.rawTypeAtFree v.val) :=
    ⟨A,v.val,v.isLt,hAvoid,rfl⟩
  have hPrefix := admissibleRawType_closed_under_prefix family hAd (cut+1) hCut
  change IsAdmissibleRawType family
    (⟨cut+1,(A.partialTypeAt (A.freeLevel v.val) v.val).restrict hCut⟩ :
      RawPartialTypeNode db du dd) at hPrefix
  rw [A.partialTypeAt_restrict (cut+1) (A.freeLevel v.val) v.val hCut] at hPrefix
  exact hPrefix

/-- Complete ordinary-pool coverage plus fibre agreement covers every
crossing, including ancestors introduced by parameter closure. -/
theorem oneGapRetainedPoolData_covers
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (cut : Nat) (V : Set (Fin A.size))
    (Z : Set (AdmissibleKptNode family))
    (hPool : Z ⊆ ambientPrefixPool family A hAvoid V)
    (hFibre : ∀ v ∈ V, ∀ w ∈ V,
      cut+1 ≤ A.freeLevel v.val → cut+1 ≤ A.freeLevel w.val →
      A.partialTypeAt cut v.val = A.partialTypeAt cut w.val →
      A.partialTypeAt (cut+1) v.val = A.partialTypeAt (cut+1) w.val) :
    CoversClosureCrossing family Z cut (oneGapRetainedPoolData A cut V) := by
  intro z hz hzCut
  obtain ⟨o,⟨v,hv,rfl⟩,hzv⟩ := hPool hz
  have hCut : cut+1 ≤ A.freeLevel v.val := by
    have hLev := kptBelowOriginal_level_le_free family A hAvoid v z hzv
    omega
  refine ⟨A.partialTypeAt cut v.val,⟨v,⟨hv,hCut⟩,rfl⟩,?_,?_⟩
  · exact (kptBelowOriginal_ancestor_raw family A hAvoid v z hzv cut
      (Nat.le_of_lt hzCut)).symm
  · rw [oneGapRetainedPoolData_target_eq A cut V hFibre v hv hCut]
    exact (kptBelowOriginal_ancestor_raw family A hAvoid v z hzv (cut+1)
      (Nat.succ_le_iff.mpr hzCut)).symm

/-- The planned closure's complete source is constructed from retained
originals; its pool containment follows from actual parameter closure. -/
theorem oneGapRetainedPoolData_covers_planned_closure
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (cut : Nat) (I : Set Nat) (X : Set (AdmissibleKptNode family))
    (U V : Set (Fin A.size))
    (hX : X ⊆ ambientPrefixPool family A hAvoid U)
    (hUV : U ⊆ V)
    (hRet : ∀ i : Fin A.size, i.val ∈ I → 0 < A.freeLevel i.val → i ∈ V)
    (hFibre : ∀ v ∈ V, ∀ w ∈ V,
      cut+1 ≤ A.freeLevel v.val → cut+1 ≤ A.freeLevel w.val →
      A.partialTypeAt cut v.val = A.partialTypeAt cut w.val →
      A.partialTypeAt (cut+1) v.val = A.partialTypeAt (cut+1) w.val) :
    CoversClosureCrossing family
      (SMTree.Envelope.closure (admissibleKptSTree family) I X) cut
      (oneGapRetainedPoolData A cut V) := by
  exact oneGapRetainedPoolData_covers family A hAvoid cut V _
    (oneGap_planned_pool_covers_closure family A hAvoid I X U V hX hUV hRet)
    hFibre

/-- The complete retained-pool prescription satisfies corrected B3.
Selected-age equality is used only with the positive-source classification. -/
theorem oneGapRetainedPoolData_correctedB3
    (ell : Nat) (hell : 2 ≤ ell) (d cut : Nat) (hd : 0 < d)
    (A : EnumeratedPartialStructure 1 0 1) (hCut : cut < A.size)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell → bad.Avoids A.L)
    (hSym : ∀ x y, A.L.binary x y (0 : Fin 1) = A.L.binary y x (0 : Fin 1))
    (V : Set (Fin A.size)) (selected : Fin d → Nat)
    (hPositive : ∀ v ∈ V, cut+1 ≤ A.freeLevel v.val →
      A.L.binary cut v.val 0 = true → ∃ j : Fin d, v.val = selected j)
    (hAge : ∀ T : IntegerGraphSupport d ell,
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound (fun x y => A.L.binary x y 0) ell d
          (Finset.range cut) (fun p j => A.L.binary p (selected j) 0)) T =
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound (fun x y => A.L.binary x y 0) ell d
          (Finset.range (cut+1)) (fun p j => A.L.binary p (selected j) 0)) T) :
    (oneGapRetainedPoolData A cut V).CorrectedB3
      (hensonForbiddenFamily ell hell) := by
  apply oneGap_correctedB3_of_equal_selected_age ell hell d cut hd A hCut
    hAvoid hSym (oneGapRetainedPoolData A cut V) selected _ hAge
  intro T hT
  obtain ⟨v,hv,hFree,_hOld,hNew⟩ :=
    oneGapRetainedPoolData_source_original A cut V T hT
  exact ⟨v.val,hNew,hPositive v hv hFree⟩

/-- A new clique must use both the restored cut and an upper vertex.
If the cut is nonadjacent to every upper vertex, this is impossible. -/
theorem oneGap_no_new_clique_of_no_positive
    (ell : Nat) (hell : 2 ≤ ell) (cut : Nat)
    (C W : AgeTestModel 1 0 1)
    (hAvoidC : ∀ bad, bad ∈ hensonForbiddenFamily ell hell → bad.Avoids C)
    (hSocle : SameInitialL W C cut)
    (hDelete : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (W.withoutVertex cut))
    (hUpperZero : ∀ x, x ∈ W.carrier → cut < x →
      W.binary cut x (0 : Fin 1) = false) :
    ¬ ∃ e : Fin ell → Nat, W.Realizes (cliquePattern ell) e := by
  classical
  rintro ⟨e,hCopy⟩
  have hMem : NormalizedForbidden.nontrivial ell (cliquePattern ell)
      (by omega) (cliquePattern_irreducible ell) ∈
        hensonForbiddenFamily ell hell := by
    simp [hensonForbiddenFamily]
  have hAt : ∃ a : Fin ell, e a = cut := by
    by_contra hn
    exact hDelete _ hMem ⟨e,
      AgeTestModel.realizes_restrictCarrier W (fun x => x ≠ cut)
        (cliquePattern ell) e hCopy (fun a ha => hn ⟨a,ha⟩)⟩
  obtain ⟨a,ha⟩ := hAt
  obtain ⟨b,hb⟩ := forbiddenCopy_has_upper_of_sameInitialL W C cut
    (cliquePattern ell) e hSocle (hAvoidC _ hMem) hCopy
  have hab : a ≠ b := by
    intro heq
    rw [heq] at ha
    omega
  have hEdge : W.binary cut (e b) (0 : Fin 1) = true := by
    simpa [ha,cliquePattern,hab] using hCopy.2.2.1 a b hab (0 : Fin 1)
  have hZero := hUpperZero (e b) (hCopy.2.1 b) hb
  rw [hZero] at hEdge
  contradiction

/-- Full corrected B3 for a possibly nonempty source whose represented
next types are all nonpositive at the cut. No selected labels are needed. -/
theorem oneGap_correctedB3_of_no_positive
    (ell : Nat) (hell : 2 ≤ ell) (cut : Nat)
    (A : EnumeratedPartialStructure 1 0 1) (hCut : cut < A.size)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell → bad.Avoids A.L)
    (hSym : ∀ x y, A.L.binary x y (0 : Fin 1) = A.L.binary y x (0 : Fin 1))
    (F : PrescribedBoringData cut 1 0 1)
    (hRepresented : ∀ T, T ∈ F.source →
      ∃ v : Nat, F.target T = A.partialTypeAt (cut+1) v ∧
        A.L.binary cut v 0 = false) :
    F.CorrectedB3 (hensonForbiddenFamily ell hell) := by
  classical
  intro S hS W _hFinite hSame hUpper hDelete bad hBad
  obtain ⟨v0,hv0,_⟩ := hRepresented S hS
  have hSocle' : SameInitialL (prescribedOrdinarySocle (F.target S)) A.L cut := by
    rw [hv0]
    exact ambient_partialType_prescribedSocle A cut v0 hCut
  have hSocle := hSame.trans hSocle'
  have hUpperNamed : ∀ x, x ∈ W.carrier → cut < x →
      ∃ v : Nat, RelationalPrefixType.ofAgeModel W (cut+1) x =
        RelationalPrefixType.ofAgeModel A.L (cut+1) v := by
    intro x hx ha
    obtain ⟨T,hT,hEq⟩ := hUpper x hx ha
    obtain ⟨v,hv,_⟩ := hRepresented T hT
    exact ⟨v,hEq.trans (congrArg PartialTypeWithE.lReduct hv)⟩
  have hUpperZero : ∀ x, x ∈ W.carrier → cut < x →
      W.binary cut x (0 : Fin 1) = false := by
    intro x hx ha
    obtain ⟨T,hT,hEq⟩ := hUpper x hx ha
    obtain ⟨v,hv,hZero⟩ := hRepresented T hT
    have hType := hEq.trans (congrArg PartialTypeWithE.lReduct hv)
    have hBit := congrArg (fun R : RelationalPrefixType (cut+1) 1 0 1 =>
      R.binary (some (⟨cut,Nat.lt_succ_self cut⟩ : Fin (cut+1))) none 0) hType
    change W.binary cut x 0 = A.L.binary cut v 0 at hBit
    exact hBit.trans hZero
  have hNoClique := oneGap_no_new_clique_of_no_positive ell hell cut
    A.L W hAvoid hSocle hDelete hUpperZero
  have hFM : NormalizedForbidden.nontrivial 2 forwardAsymPattern (by omega)
      forwardAsymPattern_irreducible ∈ hensonForbiddenFamily ell hell := by
    simp [hensonForbiddenFamily]
  have hBM : NormalizedForbidden.nontrivial 2 backwardAsymPattern (by omega)
      backwardAsymPattern_irreducible ∈ hensonForbiddenFamily ell hell := by
    simp [hensonForbiddenFamily]
  have hAsym := B3_avoids_both_asym_patterns A.L W cut hSocle
    (fun x => hSym cut x) hUpperNamed (hDelete _ hFM) (hDelete _ hBM)
  have hLM : NormalizedForbidden.singleton loopPattern loopPattern_nonNeutral ∈
      hensonForbiddenFamily ell hell := by simp [hensonForbiddenFamily]
  have hNoLoop : ¬ ∃ e : Fin 1 → Nat, W.Realizes loopPattern e := by
    rintro ⟨e,he⟩
    by_cases hAt : e 0 = cut
    · have hDiag := he.2.2.2.2 (0 : Fin 1) (0 : Fin 1)
      have hCarrier : cut ∈ A.L.carrier := (A.carrier_iff cut).mpr hCut
      have hZero := (hSocle.2.2.2 cut le_rfl (0 : Fin 1)).trans
        (oneGap_diag_false_of_avoid ell hell A.L hAvoid cut hCarrier)
      simp [loopPattern,hAt,hZero] at hDiag
    · exact hDelete _ hLM ⟨e,
        AgeTestModel.realizes_restrictCarrier W (fun x => x ≠ cut)
          loopPattern e he (by intro a; fin_cases a; exact hAt)⟩
  simp [hensonForbiddenFamily] at hBad
  rcases hBad with h | h | h | h
  · subst bad
    exact hNoLoop
  · subst bad
    exact hAsym.1
  · subst bad
    exact hAsym.2
  · subst bad
    exact hNoClique

/-- Corrected B3 for every selected-front size, including zero. Empty
labels force all represented cut bits to be false; the full source may
still contain cap or auxiliary types. -/
theorem oneGapRetainedPoolData_correctedB3_all
    (ell : Nat) (hell : 2 ≤ ell) (d cut : Nat)
    (A : EnumeratedPartialStructure 1 0 1) (hCut : cut < A.size)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell → bad.Avoids A.L)
    (hSym : ∀ x y, A.L.binary x y (0 : Fin 1) = A.L.binary y x (0 : Fin 1))
    (V : Set (Fin A.size)) (selected : Fin d → Nat)
    (hPositive : ∀ v ∈ V, cut+1 ≤ A.freeLevel v.val →
      A.L.binary cut v.val 0 = true → ∃ j : Fin d, v.val = selected j)
    (hAge : ∀ T : IntegerGraphSupport d ell,
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound (fun x y => A.L.binary x y 0) ell d
          (Finset.range cut) (fun p j => A.L.binary p (selected j) 0)) T =
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound (fun x y => A.L.binary x y 0) ell d
          (Finset.range (cut+1)) (fun p j => A.L.binary p (selected j) 0)) T) :
    (oneGapRetainedPoolData A cut V).CorrectedB3
      (hensonForbiddenFamily ell hell) := by
  by_cases hd : 0 < d
  · exact oneGapRetainedPoolData_correctedB3 ell hell d cut hd A hCut
      hAvoid hSym V selected hPositive hAge
  · apply oneGap_correctedB3_of_no_positive ell hell cut A hCut hAvoid hSym
      (oneGapRetainedPoolData A cut V)
    intro T hT
    obtain ⟨v,hv,hFree,_hOld,hNew⟩ :=
      oneGapRetainedPoolData_source_original A cut V T hT
    refine ⟨v.val,hNew,?_⟩
    cases hBit : A.L.binary cut v.val 0 with
    | false => rfl
    | true =>
      obtain ⟨j,_hj⟩ := hPositive v hv hFree hBit
      have hlt := j.isLt
      omega

/-- A genuine one-gap monoid map on every represented crossing, with
the prescribed source and its complete B3 test constructed explicitly. -/
theorem oneGap_retained_pool_skip
    (ell : Nat) (hell : 2 ≤ ell) (d cut : Nat) (hd : 0 < d)
    (A : EnumeratedPartialStructure 1 0 1)
    (hCut : cut < A.size) (hPos : 0 < cut)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell → bad.Avoids A.L)
    (hSym : ∀ x y, A.L.binary x y (0 : Fin 1) = A.L.binary y x (0 : Fin 1))
    (V : Set (Fin A.size))
    (Z : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (hPool : Z ⊆ ambientPrefixPool (hensonForbiddenFamily ell hell) A hAvoid V)
    (hFibre : ∀ v ∈ V, ∀ w ∈ V,
      cut+1 ≤ A.freeLevel v.val → cut+1 ≤ A.freeLevel w.val →
      A.partialTypeAt cut v.val = A.partialTypeAt cut w.val →
      A.partialTypeAt (cut+1) v.val = A.partialTypeAt (cut+1) w.val)
    (selected : Fin d → Nat)
    (hPositive : ∀ v ∈ V, cut+1 ≤ A.freeLevel v.val →
      A.L.binary cut v.val 0 = true → ∃ j : Fin d, v.val = selected j)
    (hAge : ∀ T : IntegerGraphSupport d ell,
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound (fun x y => A.L.binary x y 0) ell d
          (Finset.range cut) (fun p j => A.L.binary p (selected j) 0)) T =
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound (fun x y => A.L.binary x y 0) ell d
          (Finset.range (cut+1)) (fun p j => A.L.binary p (selected j) 0)) T) :
    ∃ D : SMTree.MMap (normalizedKptSMTree (hensonForbiddenFamily ell hell)),
      D.map.SkipsOnly cut ∧
      ∀ ⦃z : AdmissibleKptNode (hensonForbiddenFamily ell hell)⦄, z ∈ Z →
        ∀ (hc : cut < LevelTree.lev z),
          D (LevelTree.ancestor z cut (Nat.le_of_lt hc)) =
            LevelTree.ancestor z (cut+1) (Nat.succ_le_iff.mpr hc) := by
  exact oneGap_skip_of_complete_prescribed_B3 (hensonForbiddenFamily ell hell)
    Z cut hPos (oneGapRetainedPoolData A cut V)
    (oneGapRetainedPoolData_covers _ A hAvoid cut V Z hPool hFibre)
    (oneGapRetainedPoolData_targets_admissible _ A hAvoid cut V)
    (oneGapRetainedPoolData_correctedB3 ell hell d cut hd A hCut hAvoid
      hSym V selected hPositive hAge)

/-- The actual one-gap map with no nonemptiness premise on selected labels. -/
theorem oneGap_retained_pool_skip_all
    (ell : Nat) (hell : 2 ≤ ell) (d cut : Nat)
    (A : EnumeratedPartialStructure 1 0 1)
    (hCut : cut < A.size) (hPos : 0 < cut)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell → bad.Avoids A.L)
    (hSym : ∀ x y, A.L.binary x y (0 : Fin 1) = A.L.binary y x (0 : Fin 1))
    (V : Set (Fin A.size))
    (Z : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (hPool : Z ⊆ ambientPrefixPool (hensonForbiddenFamily ell hell) A hAvoid V)
    (hFibre : ∀ v ∈ V, ∀ w ∈ V,
      cut+1 ≤ A.freeLevel v.val → cut+1 ≤ A.freeLevel w.val →
      A.partialTypeAt cut v.val = A.partialTypeAt cut w.val →
      A.partialTypeAt (cut+1) v.val = A.partialTypeAt (cut+1) w.val)
    (selected : Fin d → Nat)
    (hPositive : ∀ v ∈ V, cut+1 ≤ A.freeLevel v.val →
      A.L.binary cut v.val 0 = true → ∃ j : Fin d, v.val = selected j)
    (hAge : ∀ T : IntegerGraphSupport d ell,
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound (fun x y => A.L.binary x y 0) ell d
          (Finset.range cut) (fun p j => A.L.binary p (selected j) 0)) T =
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound (fun x y => A.L.binary x y 0) ell d
          (Finset.range (cut+1)) (fun p j => A.L.binary p (selected j) 0)) T) :
    ∃ D : SMTree.MMap (normalizedKptSMTree (hensonForbiddenFamily ell hell)),
      D.map.SkipsOnly cut ∧
      ∀ ⦃z : AdmissibleKptNode (hensonForbiddenFamily ell hell)⦄, z ∈ Z →
        ∀ (hc : cut < LevelTree.lev z),
          D (LevelTree.ancestor z cut (Nat.le_of_lt hc)) =
            LevelTree.ancestor z (cut+1) (Nat.succ_le_iff.mpr hc) := by
  exact oneGap_skip_of_complete_prescribed_B3 (hensonForbiddenFamily ell hell)
    Z cut hPos (oneGapRetainedPoolData A cut V)
    (oneGapRetainedPoolData_covers _ A hAvoid cut V Z hPool hFibre)
    (oneGapRetainedPoolData_targets_admissible _ A hAvoid cut V)
    (oneGapRetainedPoolData_correctedB3_all ell hell d cut A hCut hAvoid
      hSym V selected hPositive hAge)

end Kk
