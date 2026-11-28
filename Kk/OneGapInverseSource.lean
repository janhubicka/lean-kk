import Kk.OneGapFiniteSelection
import Kk.OrderedSourceIdentification
import Kk.ResolvedFairActualPalette
import SuccessorTree.V10.GPlusShapeImageInjective
import Mathlib.Tactic

/-!
# Recover the genuine inverse G+ source from a retained ordinary graph

A prescribed envelope's exact level range determines every source
coordinate. For a one-gap prefix the increasing enumeration of those
levels is the anchor followed by the gap/vertex pairs of the retained
ordinary positions through the selected code. Full shape-image recovery
therefore identifies the actual inverse G+ code with the compressed
ordinary graph, without comparing dependent Kpt parameter histories.
-/

namespace Kk
open SuccessorTree
open SuccessorTree.V10
open SuccessorTree.SMTree.Envelope

theorem oneGapPairedLevels_truncate (P : Finset Nat) (p q : Nat) :
    q ∈ oneGapPairedLevels (P.filter (fun i => i ≤ p)) ↔
      q ∈ oneGapPairedLevels P ∧ q ≤ oneGapAddress p := by
  classical
  simp only [oneGapPairedLevels, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro (rfl | ⟨i, ⟨hi, hip⟩, rfl⟩ | ⟨i, ⟨hi, hip⟩, rfl⟩)
    · exact ⟨Or.inl rfl, Nat.zero_le _⟩
    · exact ⟨Or.inr (Or.inl ⟨i, hi, rfl⟩), by unfold oneGapAddress; omega⟩
    · exact ⟨Or.inr (Or.inr ⟨i, hi, rfl⟩), oneGapAddress_strictMono.monotone hip⟩
  · rintro ⟨h, hb⟩
    rcases h with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨i, ⟨hi, by unfold oneGapAddress at hb; omega⟩, rfl⟩)
    · exact Or.inr (Or.inr ⟨i, ⟨hi, by unfold oneGapAddress at hb; omega⟩, rfl⟩)

/-- The literal increasing finite enumeration of the anchor and pairs. -/
theorem oneGapLift_finset_range (P : Finset Nat) :
    Set.range (fun i : Fin (2 * P.card + 1) =>
      oneGapLift (oneGapFinsetSelectionExtend P) i.val) =
        (oneGapPairedLevels P : Set Nat) := by
  classical
  let f := oneGapFinsetSelectionExtend P
  ext q
  change (∃ i : Fin (2 * P.card + 1), oneGapLift f i.val = q) ↔
    q ∈ oneGapPairedLevels P
  constructor
  · rintro ⟨i, rfl⟩
    by_cases hz : i.val = 0
    · rw [hz, oneGapLift_zero]
      exact oneGapPairedLevels_zero P
    · let k := (i.val - 1) / 2
      have hk : k < P.card := by
        have hb := i.isLt
        dsimp [k]
        omega
      have hf : f k ∈ P :=
        (oneGapFinsetSelectionExtend_prefix P (f k)).mp ⟨k, hk, rfl⟩
      by_cases hOdd : i.val % 2 = 1
      · have hI : i.val = 2*k+1 := by dsimp [k]; omega
        rw [hI, oneGapLift_gap]
        exact Finset.mem_insert_of_mem
          (Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨f k, hf, rfl⟩)))
      · have hI : i.val = oneGapAddress k := by dsimp [k, oneGapAddress]; omega
        rw [hI, oneGapLift_address]
        exact Finset.mem_insert_of_mem
          (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨f k, hf, rfl⟩)))
  · intro hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact ⟨⟨0, by omega⟩, oneGapLift_zero f⟩
    · rcases Finset.mem_union.mp hq with hg | hr
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hg
        obtain ⟨k, hk, hEq⟩ := (oneGapFinsetSelectionExtend_prefix P j).mpr hj
        refine ⟨⟨2*k+1, by omega⟩, ?_⟩
        change oneGapLift f (2*k+1) = 2*j+1
        rw [oneGapLift_gap, show f k = j from hEq]
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
        obtain ⟨k, hk, hEq⟩ := (oneGapFinsetSelectionExtend_prefix P j).mpr hj
        refine ⟨⟨oneGapAddress k, by unfold oneGapAddress; omega⟩, ?_⟩
        change oneGapLift f (oneGapAddress k) = oneGapAddress j
        rw [oneGapLift_address, show f k = j from hEq]

/-- The domain sizes, as well as all coordinates, are forced by the
finite range of a strictly increasing enumeration. -/
theorem strictMono_fin_same_range_cast {m n : Nat}
    (f : Fin m → Nat) (g : Fin n → Nat)
    (hf : StrictMono f) (hg : StrictMono g)
    (hRange : Set.range f = Set.range g) :
    ∃ h : m = n, ∀ i : Fin m, f i = g (Fin.cast h i) := by
  classical
  have hImage : Finset.univ.image f = Finset.univ.image g := by
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact Set.ext_iff.mp hRange v
  have hCardF : (Finset.univ.image f).card = m := by
    rw [Finset.card_image_of_injective _ hf.injective]
    simp
  have hCardG : (Finset.univ.image g).card = n := by
    rw [Finset.card_image_of_injective _ hg.injective]
    simp
  have h : m = n := by rw [← hCardF, hImage, hCardG]
  subst n
  exact ⟨rfl, fun i => congrFun (strictMono_fin_nat_eq_of_same_range f g hf hg hRange) i⟩

/-- At a target code's last coordinate, the exact total level range
cuts down to exactly the image of the whole source code prefix. -/
theorem gPlus_source_prefix_levelRange
    {db du dd : Nat} {family : List (NormalizedForbidden db du dd)}
    (F : SMTree.MMap (normalizedKptSMTree family))
    (I : Finset Nat) (top d : Nat)
    (hRange : F.map.levelRange = {q | q ∈ I ∨ top < q})
    (A : FiniteGPlusVertex family)
    (hSize : (gPlusShapeImage F.map A).val.size = d+1) (hd : d ≤ top) :
    Set.range (fun i : Fin A.val.size => kptShapeLevelMap family F.map i.val) =
      {q | q ∈ I ∧ q ≤ d} := by
  let H := normalizedKptSMTree family
  let lam := kptShapeLevelMap family F.map
  have hMono : StrictMono lam := kptShapeLevelMap_strictMono family F.map
  have hPos := finiteGPlusVertex_size_pos A
  have hLast : lam (A.val.size-1) = d := by
    rw [gPlusShapeImage_size, gPlusShapeImageCut] at hSize
    change lam (A.val.size-1) + 1 = d+1 at hSize
    omega
  have hLamRange : Set.range lam = F.map.levelRange := by
    ext q
    constructor
    · rintro ⟨j, rfl⟩
      obtain ⟨x, hx⟩ := H.level_nonempty j
      refine ⟨x, ?_⟩
      change LevelTree.lev (F.map x) = lam j
      have h := kptShapeLevelMap_eq family F.map x
      change lam (LevelTree.lev x) = LevelTree.lev (F.map x) at h
      rw [hx] at h
      exact h.symm
    · rintro ⟨x, rfl⟩
      exact ⟨LevelTree.lev x, kptShapeLevelMap_eq family F.map x⟩
  ext q
  change (∃ i : Fin A.val.size, lam i.val = q) ↔ q ∈ I ∧ q ≤ d
  constructor
  · rintro ⟨i, rfl⟩
    have hi : i.val ≤ A.val.size-1 := by have hb := i.isLt; omega
    have hb := hMono.monotone hi
    rw [hLast] at hb
    have hMem : lam i.val ∈ Set.range lam := ⟨i.val,rfl⟩
    rw [hLamRange,hRange] at hMem
    change lam i.val ∈ I ∨ top < lam i.val at hMem
    exact ⟨hMem.resolve_right (by omega), hb⟩
  · rintro ⟨hI,hq⟩
    have hMem : q ∈ Set.range lam := by
      rw [hLamRange,hRange]
      exact Or.inl hI
    obtain ⟨j,hj⟩ := hMem
    have hjBound : j < A.val.size := by
      by_contra hNot
      have hlt : A.val.size-1 < j := by omega
      have h := hMono hlt
      rw [hLast,hj] at h
      omega
    exact ⟨⟨j,hjBound⟩,hj⟩

/-- Exact complete inverse-source code at a meaningful selected address.
The actual total map is arbitrary subject to the stated paired range.
No local profile or parameter history is assumed to determine the code. -/
theorem oneGap_inverseSource_code
    {family : List (NormalizedForbidden 1 0 1)}
    (F : SMTree.MMap (normalizedKptSMTree family))
    (E : Nat → Nat → Bool) (P : Finset Nat) (top p : Nat)
    (hRange : F.map.levelRange = {q | q ∈ oneGapPairedLevels P ∨ top < q})
    (hp : oneGapAddress p ≤ top)
    (A : FiniteGPlusVertex family)
    (hImage : (gPlusShapeImage F.map A).val =
      (oneGapPartial E).prefixCode (oneGapAddress p+1)) :
    A.val = oneGapRetainedCode E
      (oneGapFinsetSelectionExtend (P.filter (fun j => j ≤ p)))
      (P.filter (fun j => j ≤ p)).card := by
  classical
  let R := P.filter (fun j => j ≤ p)
  let f := oneGapFinsetSelectionExtend R
  have hSize : (gPlusShapeImage F.map A).val.size = oneGapAddress p+1 :=
    congrArg FinitePartialCode.size hImage
  have hsRange := gPlus_source_prefix_levelRange F
    (oneGapPairedLevels P) top (oneGapAddress p) hRange A hSize hp
  have htRange := oneGapLift_finset_range R
  let s : Fin A.val.size → Nat := fun i => kptShapeLevelMap family F.map i.val
  let t : Fin (2*R.card+1) → Nat := fun i => oneGapLift f i.val
  have hSame : Set.range s = Set.range t := by
    change Set.range (fun i : Fin A.val.size => kptShapeLevelMap family F.map i.val) =
      Set.range (fun i : Fin (2*R.card+1) => oneGapLift f i.val)
    rw [hsRange]
    change {q | q ∈ oneGapPairedLevels P ∧ q ≤ oneGapAddress p} =
      Set.range (fun i : Fin (2*R.card+1) =>
        oneGapLift (oneGapFinsetSelectionExtend R) i.val)
    rw [htRange]
    ext q
    exact (oneGapPairedLevels_truncate P p q).symm
  have hs : StrictMono s := by
    intro i j hij
    exact kptShapeLevelMap_strictMono family F.map hij
  have ht : StrictMono t := by
    intro i j hij
    exact oneGapLift_strictMono f (oneGapFinsetSelectionExtend_strictMono R) hij
  obtain ⟨hLen,hCoord⟩ := strictMono_fin_same_range_cast s t hs ht hSame
  let D := (oneGapPartial E).prefixCode (oneGapAddress p+1)
  have hBound (i : Fin (2*R.card+1)) : oneGapLift f i.val < D.size := by
    have hmem : oneGapLift f i.val ∈ (oneGapPairedLevels R : Set Nat) := by
      rw [← htRange]
      exact ⟨i,rfl⟩
    have hb := (oneGapPairedLevels_truncate P p (oneGapLift f i.val)).mp hmem
    change oneGapLift f i.val < oneGapAddress p+1
    omega
  let rho : Fin (2*R.card+1) → Fin D.size :=
    fun i => ⟨oneGapLift f i.val, hBound i⟩
  have hRecover : shapeImageRetainedCode F.map A = D.reindex (2*R.card+1) rho := by
    unfold shapeImageRetainedCode
    apply FinitePartialCode.reindex_congr hImage hLen
    intro i
    exact hCoord i
  calc
    A.val = shapeImageRetainedCode F.map A := (shapeImageRetainedCode_eq F.map A).symm
    _ = D.reindex (2*R.card+1) rho := hRecover
    _ = oneGapRetainedCode E f R.card := rfl

/-- Instantiate complete inverse-source recovery in the actual resolved
event chronology. All coordinate identifications are derived. -/
theorem resolvedFairEvent_inverseSource_code
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (keep : Nat → Bool) (n i : Nat) (hi : i ≤ n)
    (F : SMTree.MMap (normalizedKptSMTree
      (hensonForbiddenFamily 4 (Nat.le_trans (Nat.le_succ 2) (Nat.le_succ 3)))))
    (hRange : F.map.levelRange = {q | q ∈ resolvedFairRetainedLevels s0 keep n ∨
      resolvedFairRetainedTop s0 n < q})
    (A : FiniteGPlusVertex (hensonForbiddenFamily 4 (Nat.le_trans (Nat.le_succ 2) (Nat.le_succ 3))))
    (hImage : gPlusShapeImage F.map A = resolvedFairEventOneGapOriginal s0 hEmpty i) :
    let R := (resolvedFairRetainedPositions s0 keep n).filter
      (fun p => p ≤ resolvedFairEventCodePosition s0 i)
    A.val = oneGapRetainedCode (resolvedFairEventEdge s0)
      (oneGapFinsetSelectionExtend R) R.card := by
  dsimp only
  have hBound : oneGapAddress (resolvedFairEventCodePosition s0 i) ≤
      resolvedFairRetainedTop s0 n :=
    oneGapAddress_strictMono.monotone ((resolvedFairEventCodePosition_strictMono s0).monotone hi)
  exact oneGap_inverseSource_code F (resolvedFairEventEdge s0)
    (resolvedFairRetainedPositions s0 keep n) (resolvedFairRetainedTop s0 n)
    (resolvedFairEventCodePosition s0 i) hRange hBound A
    (congrArg (fun v => v.val) hImage)

/-- Once the retained prefix graph tables agree, the actual inverse
sources are literally equal, even if their total maps differ. -/
theorem oneGap_inverseSources_eq_of_graph
    {family : List (NormalizedForbidden 1 0 1)}
    (F G : SMTree.MMap (normalizedKptSMTree family))
    (E H : Nat → Nat → Bool) (P Q : Finset Nat) (topF topG p q : Nat)
    (hF : F.map.levelRange = {l | l ∈ oneGapPairedLevels P ∨ topF < l})
    (hG : G.map.levelRange = {l | l ∈ oneGapPairedLevels Q ∨ topG < l})
    (hp : oneGapAddress p ≤ topF) (hq : oneGapAddress q ≤ topG)
    (A B : FiniteGPlusVertex family)
    (hA : (gPlusShapeImage F.map A).val = (oneGapPartial E).prefixCode (oneGapAddress p+1))
    (hB : (gPlusShapeImage G.map B).val = (oneGapPartial H).prefixCode (oneGapAddress q+1))
    (hCard : (P.filter (fun j => j ≤ p)).card = (Q.filter (fun j => j ≤ q)).card)
    (hGraph : ∀ i < (P.filter (fun j => j ≤ p)).card,
      ∀ j < (P.filter (fun j => j ≤ p)).card,
        E (oneGapFinsetSelectionExtend (P.filter (fun l => l ≤ p)) i)
          (oneGapFinsetSelectionExtend (P.filter (fun l => l ≤ p)) j) =
        H (oneGapFinsetSelectionExtend (Q.filter (fun l => l ≤ q)) i)
          (oneGapFinsetSelectionExtend (Q.filter (fun l => l ≤ q)) j)) :
    A = B := by
  apply Subtype.ext
  rw [oneGap_inverseSource_code F E P topF p hF hp A hA,
    oneGap_inverseSource_code G H Q topG q hG hq B hB]
  let R := P.filter (fun j => j ≤ p)
  let T := Q.filter (fun j => j ≤ q)
  change oneGapRetainedCode E (oneGapFinsetSelectionExtend R) R.card =
    oneGapRetainedCode H (oneGapFinsetSelectionExtend T) T.card
  calc
    _ = oneGapRetainedCode H (oneGapFinsetSelectionExtend T) R.card :=
      oneGapRetainedCode_eq_of_finite_graph E H
        (oneGapFinsetSelectionExtend R) (oneGapFinsetSelectionExtend T)
        (oneGapFinsetSelectionExtend_strictMono R) (oneGapFinsetSelectionExtend_strictMono T)
        R.card hGraph
    _ = _ := congrArg (oneGapRetainedCode H (oneGapFinsetSelectionExtend T)) hCard

end Kk
