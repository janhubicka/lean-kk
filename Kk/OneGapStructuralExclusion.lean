import Kk.OneGapFullClosure
import Kk.K4SingletonOldNeighbour

/-!
# Complete structural exclusion at an omitted one-gap cut

English proof and independent review precede this implementation:
`docs/one_gap_structural_exclusion_english_audit_20261126.md`.

Complete next-type fibre equality and endpoint exclusion imply that no pair
of pool originals has its same-component meet at the cut. The exact closure
normal form then excludes every closure endpoint, including iterated meets
and retained successor parameters. Meet-closure also excludes the full I2
test. All hypotheses concern the actual complete ambient pool.
-/

namespace Kk
open SuccessorTree
open SuccessorTree.V10

/-- Full fibre coherence excludes a cut-level meet of actual originals.
The endpoint condition is essential, including for self-meets. -/
theorem oneGap_originals_no_meet_of_full_fibre
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (V : Set (Fin A.size)) (cut : Nat)
    (hEnd : ∀ v ∈ V, A.freeLevel v.val ≠ cut)
    (hFibre : ∀ v ∈ V, ∀ w ∈ V,
      cut+1 ≤ A.freeLevel v.val → cut+1 ≤ A.freeLevel w.val →
      A.partialTypeAt cut v.val = A.partialTypeAt cut w.val →
      A.partialTypeAt (cut+1) v.val = A.partialTypeAt (cut+1) w.val) :
    ∀ v ∈ V, ∀ w ∈ V,
      SMTree.Envelope.SameComponent
        (A.kptOriginal family hAvoid v) (A.kptOriginal family hAvoid w) →
      LevelTree.lev (LevelTree.meet
        (A.kptOriginal family hAvoid v) (A.kptOriginal family hAvoid w)) ≠ cut := by
  intro v hv w hw hComp hMeet
  let a := A.kptOriginal family hAvoid v
  let b := A.kptOriginal family hAvoid w
  have hLeA : cut ≤ A.freeLevel v.val := by
    have h := LevelTree.level_le_of_le (LevelTree.meet_le_left hComp)
    rw [hMeet] at h
    exact h
  have hLeB : cut ≤ A.freeLevel w.val := by
    have h := LevelTree.level_le_of_le (LevelTree.meet_le_right hComp)
    rw [hMeet] at h
    exact h
  have hFreeA : cut+1 ≤ A.freeLevel v.val := by
    have h := hEnd v hv
    omega
  have hFreeB : cut+1 ≤ A.freeLevel w.val := by
    have h := hEnd w hw
    omega
  have hCa : cut < LevelTree.lev a := by
    change cut < A.freeLevel v.val
    omega
  have hCb : cut < LevelTree.lev b := by
    change cut < A.freeLevel w.val
    omega
  have hOldAnc :
      LevelTree.ancestor a cut (Nat.le_of_lt hCa) =
        LevelTree.ancestor b cut (Nat.le_of_lt hCb) := by
    have hLeft := LevelTree.eq_ancestor_of_le
      (LevelTree.meet_le_left hComp) hMeet (Nat.le_of_lt hCa)
    have hRight := LevelTree.eq_ancestor_of_le
      (LevelTree.meet_le_right hComp) hMeet (Nat.le_of_lt hCb)
    exact hLeft.symm.trans hRight
  have hOld : A.partialTypeAt cut v.val = A.partialTypeAt cut w.val := by
    have hRaw := congrArg Subtype.val hOldAnc
    rw [kptBelowOriginal_ancestor_raw family A hAvoid v a le_rfl cut
        (Nat.le_of_lt hCa),
      kptBelowOriginal_ancestor_raw family A hAvoid w b le_rfl cut
        (Nat.le_of_lt hCb)] at hRaw
    exact eq_of_heq (Sigma.mk.inj_iff.mp hRaw).2
  have hNext := hFibre v hv w hw hFreeA hFreeB hOld
  have hNextAnc :
      LevelTree.ancestor a (cut+1) (Nat.succ_le_iff.mpr hCa) =
        LevelTree.ancestor b (cut+1) (Nat.succ_le_iff.mpr hCb) := by
    apply Subtype.ext
    rw [kptBelowOriginal_ancestor_raw family A hAvoid v a le_rfl (cut+1)
        (Nat.succ_le_iff.mpr hCa),
      kptBelowOriginal_ancestor_raw family A hAvoid w b le_rfl (cut+1)
        (Nat.succ_le_iff.mpr hCb), hNext]
  have hCommon :
      LevelTree.ancestor a (cut+1) (Nat.succ_le_iff.mpr hCa) ≤
        LevelTree.meet a b := by
    apply LevelTree.le_meet
    · exact LevelTree.ancestor_le a (cut+1) (Nat.succ_le_iff.mpr hCa)
    · rw [hNextAnc]
      exact LevelTree.ancestor_le b (cut+1) (Nat.succ_le_iff.mpr hCb)
  have hBound := LevelTree.level_le_of_le hCommon
  rw [LevelTree.level_ancestor] at hBound
  change cut+1 ≤ LevelTree.lev (LevelTree.meet
    (A.kptOriginal family hAvoid v) (A.kptOriginal family hAvoid w)) at hBound
  rw [hMeet] at hBound
  omega

/-- The actual closure has neither an endpoint nor a competing meet at
the omitted cut. No no-I1/no-I2 verdict is an input. -/
theorem oneGap_planned_closure_structural_of_full_fibre
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (I : Set Nat) (X : Set (AdmissibleKptNode family))
    (U V : Set (Fin A.size))
    (hX : X ⊆ ambientPrefixPool family A hAvoid U)
    (hUV : U ⊆ V)
    (hRet : ∀ i : Fin A.size, i.val ∈ I → 0 < A.freeLevel i.val → i ∈ V)
    (cut : Nat)
    (hSeed : ∀ z ∈ X, LevelTree.lev z ≠ cut)
    (hEnd : ∀ v ∈ V, A.freeLevel v.val ≠ cut)
    (hFibre : ∀ v ∈ V, ∀ w ∈ V,
      cut+1 ≤ A.freeLevel v.val → cut+1 ≤ A.freeLevel w.val →
      A.partialTypeAt cut v.val = A.partialTypeAt cut w.val →
      A.partialTypeAt (cut+1) v.val = A.partialTypeAt (cut+1) w.val) :
    (¬ ∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure (admissibleKptSTree family) I X ∧
        LevelTree.lev z = cut) ∧
    (¬ ∃ a : AdmissibleKptNode family,
      a ∈ SMTree.Envelope.closure (admissibleKptSTree family) I X ∧
      ∃ b : AdmissibleKptNode family,
        b ∈ SMTree.Envelope.closure (admissibleKptSTree family) I X ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) := by
  have hMeet := oneGap_originals_no_meet_of_full_fibre
    family A hAvoid V cut hEnd hFibre
  have hI1 := oneGap_planned_closure_no_endpoint
    family A hAvoid I X U V hX hUV hRet cut hSeed hEnd hMeet
  refine ⟨hI1, ?_⟩
  rintro ⟨a, ha, b, hb, hComp, hLevel⟩
  exact hI1 ⟨LevelTree.meet a b,
    SMTree.Envelope.closure_meetClosed (admissibleKptSTree family) I X
      ha hb hComp, hLevel⟩

/-- In the ordinary graph signature, full column coherence supplies all
dependent next-type atoms. Eligibility controls both auxiliary E directions. -/
theorem oneGap_full_fibre_of_pool_columns
    (A : EnumeratedPartialStructure 1 0 1)
    (V : Set (Fin A.size)) (cut : Nat)
    (hSym : ∀ x y, A.L.binary x y (0 : Fin 1) = A.L.binary y x (0 : Fin 1))
    (hLoop : ∀ x, A.L.binary x x (0 : Fin 1) = false)
    (hDiag : ∀ x, A.L.diagonal x (0 : Fin 1) = false)
    (hColumns : ∀ v ∈ V, ∀ w ∈ V,
      cut+1 ≤ A.freeLevel v.val → cut+1 ≤ A.freeLevel w.val →
      (∀ p < cut, A.L.binary p v.val 0 = A.L.binary p w.val 0) →
      A.L.binary cut v.val 0 = A.L.binary cut w.val 0) :
    ∀ v ∈ V, ∀ w ∈ V,
      cut+1 ≤ A.freeLevel v.val → cut+1 ≤ A.freeLevel w.val →
      A.partialTypeAt cut v.val = A.partialTypeAt cut w.val →
      A.partialTypeAt (cut+1) v.val = A.partialTypeAt (cut+1) w.val := by
  intro v hv w hw hFreeV hFreeW hOld
  exact oneGap_full_nextType_eq_of_no_column_fork A cut v.val w.val
    hFreeV hFreeW hSym hLoop hDiag
    (hColumns v hv w hw hFreeV hFreeW) hOld

/-- Ordinary no-fork on the complete pool now excludes both structural
tests of the actual planned closure. This does not assert B3. -/
theorem oneGap_planned_closure_structural_of_pool_columns
    (family : List (NormalizedForbidden 1 0 1))
    (A : EnumeratedPartialStructure 1 0 1)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (I : Set Nat) (X : Set (AdmissibleKptNode family))
    (U V : Set (Fin A.size))
    (hX : X ⊆ ambientPrefixPool family A hAvoid U)
    (hUV : U ⊆ V)
    (hRet : ∀ i : Fin A.size, i.val ∈ I → 0 < A.freeLevel i.val → i ∈ V)
    (cut : Nat)
    (hSeed : ∀ z ∈ X, LevelTree.lev z ≠ cut)
    (hEnd : ∀ v ∈ V, A.freeLevel v.val ≠ cut)
    (hSym : ∀ x y, A.L.binary x y (0 : Fin 1) = A.L.binary y x (0 : Fin 1))
    (hLoop : ∀ x, A.L.binary x x (0 : Fin 1) = false)
    (hDiag : ∀ x, A.L.diagonal x (0 : Fin 1) = false)
    (hColumns : ∀ v ∈ V, ∀ w ∈ V,
      cut+1 ≤ A.freeLevel v.val → cut+1 ≤ A.freeLevel w.val →
      (∀ p < cut, A.L.binary p v.val 0 = A.L.binary p w.val 0) →
      A.L.binary cut v.val 0 = A.L.binary cut w.val 0) :
    (¬ ∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure (admissibleKptSTree family) I X ∧
        LevelTree.lev z = cut) ∧
    (¬ ∃ a : AdmissibleKptNode family,
      a ∈ SMTree.Envelope.closure (admissibleKptSTree family) I X ∧
      ∃ b : AdmissibleKptNode family,
        b ∈ SMTree.Envelope.closure (admissibleKptSTree family) I X ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :=
  oneGap_planned_closure_structural_of_full_fibre
    family A hAvoid I X U V hX hUV hRet cut hSeed hEnd
    (oneGap_full_fibre_of_pool_columns A V cut hSym hLoop hDiag hColumns)

/-- A positive selected terminal already has an old neighbour whenever
its complete canonical age is unchanged by restoring the cut. This uses
the exact singleton raw bound and works for every forbidden size at least two. -/
theorem oneGap_old_neighbour_of_equal_selected_age
    (G : Nat → Nat → Bool) (ell d cut : Nat) (hell : 2 ≤ ell)
    (selected : Fin d → Nat)
    (hAge : ∀ T : IntegerGraphSupport d ell,
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound G ell d (Finset.range cut)
          (fun p j => G p (selected j))) T =
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound G ell d (Finset.range (cut+1))
          (fun p j => G p (selected j))) T)
    (i : Fin d) (hPositive : G cut (selected i) = true) :
    ∃ p, p < cut ∧ G p (selected i) = true := by
  classical
  let T : IntegerGraphSupport d ell := trackFSingletonSupport d ell i hell
  let col : Nat → Fin d → Bool := fun p j => G p (selected j)
  have hCanonical (P : Finset Nat) :
      integerGraphAgeCanonical d ell (finiteOldColumnRawBound G ell d P col) T =
        finiteOldColumnRawBound G ell d P col T := by
    apply trackFCanonical_singleton_eq_raw d ell hell
      (finiteOldColumnRawBound G ell d P col)
      (fun U V hUV => finiteOldColumnRawBound_support_mono G ell d P col U V hUV) i
    unfold finiteOldColumnRawBound
    omega
  have hEqual := hAge T
  rw [hCanonical (Finset.range cut), hCanonical (Finset.range (cut+1))] at hEqual
  by_contra hNo
  have hEmpty :
      oldSupportCommonNeighbourPool (Finset.range cut) col T.1 = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro p hp
    change p ∈ (Finset.range cut).filter
      (fun p => ∀ j ∈ T.1, col p j = true) at hp
    obtain ⟨hp,hcol⟩ := Finset.mem_filter.mp hp
    exact hNo ⟨p,Finset.mem_range.mp hp,hcol i (by simp [T,trackFSingletonSupport])⟩
  have hOldZero : finiteDirectedCliqueCapacity G
      (oldSupportCommonNeighbourPool (Finset.range cut) col T.1) = 0 := by
    rw [hEmpty,k4TrackD_empty_old_pool_clique_capacity]
  have hCutMem : cut ∈
      oldSupportCommonNeighbourPool (Finset.range (cut+1)) col T.1 := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (Nat.lt_succ_self cut), ?_⟩
    intro j hj
    have hji : j = i := by simpa [T,trackFSingletonSupport] using hj
    subst j
    exact hPositive
  have hSub : ({cut} : Finset Nat) ⊆
      oldSupportCommonNeighbourPool (Finset.range (cut+1)) col T.1 := by
    intro p hp
    have hpEq := Finset.mem_singleton.mp hp
    simpa [hpEq] using hCutMem
  have hClique : IsDirectedCliqueOn G ({cut} : Finset Nat) := by
    intro x hx y hy hxy
    exact False.elim (hxy
      ((Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm))
  have hOne := directedClique_card_le_capacity G
    (oldSupportCommonNeighbourPool (Finset.range (cut+1)) col T.1)
    ({cut} : Finset Nat) hSub hClique
  have hOne' : 1 ≤ finiteDirectedCliqueCapacity G
      (oldSupportCommonNeighbourPool (Finset.range (cut+1)) col T.1) := by
    simpa using hOne
  unfold finiteOldColumnRawBound at hEqual
  rw [hOldZero] at hEqual
  omega

/-- Derive full-pool ordinary coherence using selected no-split and
selected canonical-age neutrality. The old-neighbour property is proved,
not assumed. The selected list may be empty or have repeated entries. -/
theorem oneGap_pool_columns_of_selected_neutrality
    (A : EnumeratedPartialStructure 1 0 1)
    (ell d cut : Nat) (hell : 2 ≤ ell)
    (V : Set (Fin A.size)) (selected : Fin d → Nat)
    (hPositive : ∀ v ∈ V, cut+1 ≤ A.freeLevel v.val →
      A.L.binary cut v.val 0 = true → ∃ j, v.val = selected j)
    (hNoSplit : ∀ i j : Fin d, cut < selected i → cut < selected j →
      (∀ p < cut, A.L.binary p (selected i) 0 = A.L.binary p (selected j) 0) →
      A.L.binary cut (selected i) 0 = A.L.binary cut (selected j) 0)
    (hOtherZero : ∀ v ∈ V, cut+1 ≤ A.freeLevel v.val →
      (¬ ∃ j, v.val = selected j) →
      ∀ p < cut, A.L.binary p v.val 0 = false)
    (hAge : ∀ T : IntegerGraphSupport d ell,
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound (fun x y => A.L.binary x y 0) ell d
          (Finset.range cut) (fun p j => A.L.binary p (selected j) 0)) T =
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound (fun x y => A.L.binary x y 0) ell d
          (Finset.range (cut+1)) (fun p j => A.L.binary p (selected j) 0)) T) :
    ∀ v ∈ V, ∀ w ∈ V,
      cut+1 ≤ A.freeLevel v.val → cut+1 ≤ A.freeLevel w.val →
      (∀ p < cut, A.L.binary p v.val 0 = A.L.binary p w.val 0) →
      A.L.binary cut v.val 0 = A.L.binary cut w.val 0 := by
  let G : Nat → Nat → Bool := fun x y => A.L.binary x y 0
  let Pool : Nat → Prop := fun n =>
    ∃ v : Fin A.size, v ∈ V ∧ cut+1 ≤ A.freeLevel v.val ∧ v.val = n
  let Selected : Nat → Prop := fun n => ∃ j : Fin d, n = selected j
  have hPos : ∀ n, Pool n → cut < n → G cut n = true → Selected n := by
    rintro n ⟨v,hv,hFree,hvEq⟩ _ hBit
    rw [← hvEq] at hBit ⊢
    exact hPositive v hv hFree hBit
  have hFork : ∀ n m, Selected n → Selected m → cut < n → cut < m →
      (∀ p < cut, G p n = G p m) → G cut n = G cut m := by
    rintro n m ⟨i,rfl⟩ ⟨j,rfl⟩ hi hj hOld
    exact hNoSplit i j hi hj hOld
  have hOld : ∀ n, Pool n → cut < n → G cut n = true →
      ∃ p, p < cut ∧ G p n = true := by
    intro n hn hcn hBit
    obtain ⟨i,hi⟩ := hPos n hn hcn hBit
    rw [hi] at hBit ⊢
    exact oneGap_old_neighbour_of_equal_selected_age
      G ell d cut hell selected hAge i hBit
  have hZero : ∀ n, Pool n → ¬ Selected n → cut < n →
      ∀ p < cut, G p n = false := by
    rintro n ⟨v,hv,hFree,hvEq⟩ hNot _ p hp
    rw [← hvEq] at hNot ⊢
    exact hOtherZero v hv hFree hNot p hp
  intro v hv w hw hFreeV hFreeW hSame
  have hvCut : cut < v.val := by
    have h := A.freeLevel_le v.val
    omega
  have hwCut : cut < w.val := by
    have h := A.freeLevel_le w.val
    omega
  exact oneGap_full_pool_column_fibre G cut Pool Selected
    hPos hFork hOld hZero v.val w.val
    ⟨v,hv,hFreeV,rfl⟩ ⟨w,hw,hFreeW,rfl⟩ hvCut hwCut hSame

/-- Complete selected age neutrality, ordinary source classification,
and selected no-split produce the complete dependent next-type fibre
certificate used by both structural exclusion and prescribed crossing. -/
theorem oneGap_full_fibre_of_selected_neutrality
    (A : EnumeratedPartialStructure 1 0 1)
    (ell d cut : Nat) (hell : 2 ≤ ell)
    (V : Set (Fin A.size)) (selected : Fin d → Nat)
    (hSym : ∀ x y, A.L.binary x y (0 : Fin 1) = A.L.binary y x (0 : Fin 1))
    (hLoop : ∀ x, A.L.binary x x (0 : Fin 1) = false)
    (hDiag : ∀ x, A.L.diagonal x (0 : Fin 1) = false)
    (hPositive : ∀ v ∈ V, cut+1 ≤ A.freeLevel v.val →
      A.L.binary cut v.val 0 = true → ∃ j, v.val = selected j)
    (hNoSplit : ∀ i j : Fin d, cut < selected i → cut < selected j →
      (∀ p < cut, A.L.binary p (selected i) 0 = A.L.binary p (selected j) 0) →
      A.L.binary cut (selected i) 0 = A.L.binary cut (selected j) 0)
    (hOtherZero : ∀ v ∈ V, cut+1 ≤ A.freeLevel v.val →
      (¬ ∃ j, v.val = selected j) →
      ∀ p < cut, A.L.binary p v.val 0 = false)
    (hAge : ∀ T : IntegerGraphSupport d ell,
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound (fun x y => A.L.binary x y 0) ell d
          (Finset.range cut) (fun p j => A.L.binary p (selected j) 0)) T =
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound (fun x y => A.L.binary x y 0) ell d
          (Finset.range (cut+1)) (fun p j => A.L.binary p (selected j) 0)) T) :
    ∀ v ∈ V, ∀ w ∈ V,
      cut+1 ≤ A.freeLevel v.val → cut+1 ≤ A.freeLevel w.val →
      A.partialTypeAt cut v.val = A.partialTypeAt cut w.val →
      A.partialTypeAt (cut+1) v.val = A.partialTypeAt (cut+1) w.val :=
  oneGap_full_fibre_of_pool_columns A V cut hSym hLoop hDiag
    (oneGap_pool_columns_of_selected_neutrality A ell d cut hell V selected
      hPositive hNoSplit hOtherZero hAge)

end Kk
