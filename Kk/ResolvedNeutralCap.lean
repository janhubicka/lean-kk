import Kk.OneGapInverseSource
import Kk.OneGapAgeTransport
import Mathlib.Tactic

/-!
# Neutral finite cap without a further selected original

Truncate the actual ordinary event graph at a chosen coding position
and make every later ordinary vertex isolated. The first such vertex
is a genuine padded upper type. All actual selected prefix codes are
unchanged. The selected-only local tests do not include the cap.
-/

namespace Kk
open SuccessorTree
open SuccessorTree.V10
open SuccessorTree.SMTree.Envelope

def neutralPrefixGraph (G : Nat → Nat → Bool) (p : Nat) (i j : Nat) : Bool :=
  if i ≤ p ∧ j ≤ p then G i j else false

theorem neutralPrefixGraph_positive (G : Nat → Nat → Bool) (p i j : Nat)
    (h : neutralPrefixGraph G p i j = true) : G i j = true := by
  by_cases hOld : i ≤ p ∧ j ≤ p
  · simpa [neutralPrefixGraph, hOld] using h
  · simp [neutralPrefixGraph, hOld] at h

theorem neutralPrefixGraph_avoids (G : Nat → Nat → Bool) (p : Nat)
    (hFree : ∀ C : Finset Nat, IsDirectedCliqueOn G C → C.card < 4)
    (hSym : ∀ i j, G i j = G j i)
    (hLoop : ∀ i, G i i = false) :
    ∀ bad, bad ∈ hensonForbiddenFamily 4 (by decide) →
      bad.Avoids (normalizedGraphModel (neutralPrefixGraph G p)) := by
  apply henson_avoids_of_finite_clique_bound _ 4 (by decide)
  · intro C hC
    apply hFree C
    intro i hi j hj hij
    exact neutralPrefixGraph_positive G p i j (hC i hi j hj hij)
  · intro i j
    by_cases hi : i ≤ p <;> by_cases hj : j ≤ p <;>
      simp [neutralPrefixGraph, hi, hj, hSym]
  · intro i
    simp [neutralPrefixGraph, hLoop]

theorem neutralPrefixGraph_padded_agree (G : Nat → Nat → Bool)
    (p u v : Nat) (hu : u ≤ oneGapAddress p) (hv : v ≤ oneGapAddress p) :
    oneGapEdge (neutralPrefixGraph G p) u v = oneGapEdge G u v := by
  by_cases hur : oneGapReal u <;> by_cases hvr : oneGapReal v
  · have hu' := oneGapAddress_index hur
    have hv' := oneGapAddress_index hvr
    unfold oneGapAddress at hu hv hu' hv'
    have hU : oneGapIndex u ≤ p := by omega
    have hV : oneGapIndex v ≤ p := by omega
    simp [oneGapEdge, hur, hvr, neutralPrefixGraph, hU, hV]
  · simp [oneGapEdge, hur, hvr]
  · simp [oneGapEdge, hur, hvr]
  · simp [oneGapEdge, hur, hvr]

theorem neutralPrefixGraph_padded_zero_right (G : Nat → Nat → Bool)
    (p u v : Nat) (hv : oneGapAddress p < v) :
    oneGapEdge (neutralPrefixGraph G p) u v = false := by
  by_cases hReal : oneGapReal v
  · have h := oneGapAddress_index hReal
    unfold oneGapAddress at hv h
    have hIndex : ¬ oneGapIndex v ≤ p := by omega
    simp [oneGapEdge, hReal, neutralPrefixGraph, hIndex]
  · simp [oneGapEdge, hReal]

/-- Complete prefix equality, including E and all negative atoms. -/
theorem neutralPrefixGraph_prefixCode_eq (G : Nat → Nat → Bool)
    (p m : Nat) (hm : m ≤ oneGapAddress p + 1) :
    (oneGapPartial (neutralPrefixGraph G p)).prefixCode m =
      (oneGapPartial G).prefixCode m := by
  have hBin : (fun i j : Fin m => fun _ : Fin 1 =>
      oneGapEdge (neutralPrefixGraph G p) i.val j.val) =
      (fun i j : Fin m => fun _ : Fin 1 =>
      oneGapEdge G i.val j.val) := by
    funext i j t
    exact neutralPrefixGraph_padded_agree G p i.val j.val
      (by have h := i.isLt; omega) (by have h := j.isLt; omega)
  have hDiag : (fun i : Fin m => fun _ : Fin 1 =>
      oneGapEdge (neutralPrefixGraph G p) i.val i.val) =
      (fun i : Fin m => fun _ : Fin 1 => oneGapEdge G i.val i.val) := by
    funext i t
    exact neutralPrefixGraph_padded_agree G p i.val i.val
      (by have h := i.isLt; omega) (by have h := i.isLt; omega)
  unfold CountableEnumeratedPartialStructure.prefixCode
  simp only [oneGapPartial, normalizedGraphModel, binaryUnaryAgeModel]
  rw [hBin, hDiag]

noncomputable def resolvedNeutralCapTop
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) : Nat :=
  oneGapAddress (resolvedFairEventCodePosition s0 n + 1)

noncomputable def resolvedNeutralCapSize
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) : Nat :=
  resolvedNeutralCapTop s0 n + 1

noncomputable def resolvedNeutralCapGraph
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) : Nat → Nat → Bool :=
  neutralPrefixGraph (resolvedFairEventEdge s0) (resolvedFairEventCodePosition s0 n)

noncomputable def resolvedNeutralCapPlan
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n : Nat) : Finset Nat :=
  oneGapPairedLevels (insert (resolvedFairEventCodePosition s0 n + 1)
    (resolvedFairRetainedPositions s0 keep n))

def resolvedNeutralCapOldPool
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n : Nat) : Set (Fin (resolvedNeutralCapSize s0 n)) :=
  {v | v.val ∈ resolvedFairRetainedLevels s0 keep n}

noncomputable def resolvedNeutralCapFrontSize
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n c : Nat) : Nat :=
  resolvedFairSelectedFrontSize s0 keep (resolvedNeutralCapSize s0 n)
    (resolvedNeutralCapOldPool s0 keep n) c

noncomputable def resolvedNeutralCapFront
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n c : Nat) : Fin (resolvedNeutralCapFrontSize s0 keep n c) → Nat :=
  resolvedFairSelectedFront s0 keep (resolvedNeutralCapSize s0 n)
    (resolvedNeutralCapOldPool s0 keep n) c

theorem resolvedNeutralCapPlan_old_iff
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n q : Nat) (hq : q ≤ resolvedFairRetainedTop s0 n) :
    q ∈ resolvedNeutralCapPlan s0 keep n ↔ q ∈ resolvedFairRetainedLevels s0 keep n := by
  classical
  let p := resolvedFairEventCodePosition s0 n
  let P := resolvedFairRetainedPositions s0 keep n
  have hFilter : (insert (p+1) P).filter (fun j => j ≤ p) = P := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hj,hb⟩
      rcases hj with rfl | hj
      · omega
      · exact hj
    · intro hj
      exact ⟨Or.inr hj, ((resolvedFairRetainedPositions_mem_iff s0 keep n j).mp hj).1⟩
  have hTrunc := oneGapPairedLevels_truncate (insert (p+1) P) p q
  rw [hFilter] at hTrunc
  change q ∈ oneGapPairedLevels (insert (p+1) P) ↔ q ∈ oneGapPairedLevels P
  exact ⟨fun h => hTrunc.mpr ⟨h,hq⟩, fun h => (hTrunc.mp h).1⟩

theorem resolvedNeutralCapPlan_bound
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n q : Nat) (hq : q ∈ resolvedNeutralCapPlan s0 keep n) :
    q ≤ resolvedNeutralCapTop s0 n := by
  classical
  let p := resolvedFairEventCodePosition s0 n
  let P := resolvedFairRetainedPositions s0 keep n
  change q ∈ oneGapPairedLevels (insert (p+1) P) at hq
  have hFilter : (insert (p+1) P).filter (fun j => j ≤ p+1) =
      insert (p+1) P := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · exact And.left
    · intro hj
      refine ⟨hj, ?_⟩
      rcases hj with rfl | hj
      · exact le_rfl
      · have h := ((resolvedFairRetainedPositions_mem_iff s0 keep n j).mp hj).1
        change j ≤ p at h
        omega
  have h := oneGapPairedLevels_truncate (insert (p+1) P) (p+1) q
  rw [hFilter] at h
  exact (h.mp hq).2

theorem resolvedNeutralCapPlan_top
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool) (n : Nat) :
    resolvedNeutralCapTop s0 n ∈ resolvedNeutralCapPlan s0 keep n :=
  (oneGapPairedLevels_address_iff _ _).mpr (Finset.mem_insert_self _ _)

theorem resolvedNeutralCapOldPool_role
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n : Nat) (v : Fin (resolvedNeutralCapSize s0 n))
    (hv : v ∈ resolvedNeutralCapOldPool s0 keep n) :
    ResolvedQRetainedBase (resolvedFairEventRole s0 keep v.val) := by
  by_cases hReal : oneGapReal v.val
  · exact ((resolvedFairRetainedLevels_real_iff s0 keep n v.val hReal).mp hv).2
  · exact Or.inl ((resolvedFairEventRole_dummy_iff s0 keep v.val).mpr hReal)

theorem resolvedNeutralCapFront_bound
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n c : Nat) (i : Fin (resolvedNeutralCapFrontSize s0 keep n c)) :
    resolvedNeutralCapFront s0 keep n c i ≤ resolvedFairRetainedTop s0 n := by
  let N := resolvedNeutralCapSize s0 n
  let V := resolvedNeutralCapOldPool s0 keep n
  let v : Fin N := ⟨resolvedNeutralCapFront s0 keep n c i,
    resolvedFairSelectedFront_lt_size s0 keep N V c i⟩
  have hv : v ∈ V :=
    ((resolvedFairSelectedFront_range s0 keep N V c v).mp ⟨i,rfl⟩).1
  exact resolvedFairRetainedLevels_bound s0 keep n v.val hv

theorem resolvedNeutralCapGraph_avoids
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅) (n : Nat) :
    ∀ bad, bad ∈ hensonForbiddenFamily 4 (by decide) →
      bad.Avoids (normalizedGraphModel (resolvedNeutralCapGraph s0 n)) :=
  neutralPrefixGraph_avoids (resolvedFairEventEdge s0) _
    (resolvedFairEventEdge_free s0 hEmpty)
    (resolvedFairEventEdge_sym s0) (resolvedFairEventEdge_loops s0)

noncomputable def resolvedNeutralCapType
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅) (n : Nat) :
    AdmissibleKptNode (hensonForbiddenFamily 4 (by decide)) :=
  ((oneGapPartial (resolvedNeutralCapGraph s0 n)).finitePrefix
    (resolvedNeutralCapSize s0 n)).kptOriginal (hensonForbiddenFamily 4 (by decide))
    (oneGap_finitePrefix_avoids _ 4 (by decide) (resolvedNeutralCapGraph_avoids s0 hEmpty n)
      (resolvedNeutralCapSize s0 n))
    ⟨resolvedNeutralCapTop s0 n, Nat.lt_succ_self _⟩

theorem resolvedNeutralCapType_level
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅) (n : Nat) :
    LevelTree.lev (resolvedNeutralCapType s0 hEmpty n) =
      resolvedNeutralCapTop s0 n - 1 := by
  change ((oneGapPartial (resolvedNeutralCapGraph s0 n)).finitePrefix
    (resolvedNeutralCapSize s0 n)).freeLevel (resolvedNeutralCapTop s0 n) = _
  rw [oneGapPartial_freeLevel (resolvedNeutralCapGraph s0 n)
    (resolvedNeutralCapSize s0 n) (resolvedNeutralCapTop s0 n)
    (show resolvedNeutralCapTop s0 n < resolvedNeutralCapSize s0 n from Nat.lt_succ_self _)]
  exact if_pos (show oneGapReal (resolvedNeutralCapTop s0 n) from oneGapAddress_real _)

/-- Actual neutral cap envelope from the old selected-only local tests.
Every other local hypothesis is constructed or derived from verified
event geometry. The cap is NOT another selected coding terminal. -/
theorem resolvedNeutralCap_envelope
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (keep : Nat → Bool) (n : Nat)
    (hNoSplit : ∀ c, c ≤ resolvedFairRetainedTop s0 n →
      c ∉ resolvedFairRetainedLevels s0 keep n → oneGapReal c →
      ∀ i j : Fin (resolvedNeutralCapFrontSize s0 keep n c),
      (∀ b < c, oneGapEdge (resolvedFairEventEdge s0) b (resolvedNeutralCapFront s0 keep n c i) =
        oneGapEdge (resolvedFairEventEdge s0) b (resolvedNeutralCapFront s0 keep n c j)) →
      oneGapEdge (resolvedFairEventEdge s0) c (resolvedNeutralCapFront s0 keep n c i) =
        oneGapEdge (resolvedFairEventEdge s0) c (resolvedNeutralCapFront s0 keep n c j))
    (hAge : ∀ c, c ≤ resolvedFairRetainedTop s0 n →
      c ∉ resolvedFairRetainedLevels s0 keep n → oneGapReal c →
      resolvedTargetAge (oneGapEdge (resolvedFairEventEdge s0)) 4 (Finset.range c)
        (resolvedNeutralCapFront s0 keep n c) =
      resolvedTargetAge (oneGapEdge (resolvedFairEventEdge s0)) 4 (Finset.range (c+1))
        (resolvedNeutralCapFront s0 keep n c)) :
    ∃ F : SMTree.MMap (normalizedKptSMTree (hensonForbiddenFamily 4 (by decide))),
      StageFullInvariant (normalizedKptSMTree (hensonForbiddenFamily 4 (by decide)))
        ({resolvedNeutralCapType s0 hEmpty n} : Set _) (resolvedNeutralCapTop s0 n) 0
        (resolvedNeutralCapPlan s0 keep n : Set Nat) F ∧
      F.map.levelRange = {q | q ∈ resolvedNeutralCapPlan s0 keep n ∨
        resolvedNeutralCapTop s0 n < q} := by
  classical
  let p := resolvedFairEventCodePosition s0 n
  let G := resolvedFairEventEdge s0
  let G' := resolvedNeutralCapGraph s0 n
  let top := resolvedNeutralCapTop s0 n
  let N := resolvedNeutralCapSize s0 n
  let I := resolvedNeutralCapPlan s0 keep n
  let V0 := resolvedNeutralCapOldPool s0 keep n
  let V : Set (Fin N) := {v | v.val ∈ I}
  let vcap : Fin N := ⟨top, Nat.lt_succ_self _⟩
  let X : Set (AdmissibleKptNode (hensonForbiddenFamily 4 (by decide))) :=
    {resolvedNeutralCapType s0 hEmpty n}
  let d := resolvedNeutralCapFrontSize s0 keep n
  let target := resolvedNeutralCapFront s0 keep n
  have hI0 : ∀ c, c < top → c ∉ I → oneGapReal c →
      c ≤ resolvedFairRetainedTop s0 n ∧ c ∉ resolvedFairRetainedLevels s0 keep n := by
    intro c hc hn hr
    have hOld : c ≤ resolvedFairRetainedTop s0 n := by
      change c < oneGapAddress (p+1) at hc
      change c ≤ oneGapAddress p
      unfold oneGapReal at hr
      unfold oneGapAddress at hc ⊢
      omega
    exact ⟨hOld, fun hm => hn ((resolvedNeutralCapPlan_old_iff s0 keep n c hOld).mpr hm)⟩
  have hAgree (u v : Nat) (hu : u ≤ resolvedFairRetainedTop s0 n)
      (hv : v ≤ resolvedFairRetainedTop s0 n) :
      oneGapEdge G' u v = oneGapEdge G u v :=
    neutralPrefixGraph_padded_agree G p u v hu hv
  have hTarget (c : Nat) (i : Fin (d c)) :
      target c i ≤ resolvedFairRetainedTop s0 n :=
    resolvedNeutralCapFront_bound s0 keep n c i
  have hCapLev := resolvedNeutralCapType_level s0 hEmpty n
  have hTopMem : top ∈ I := resolvedNeutralCapPlan_top s0 keep n
  have hCapReal : oneGapReal top := oneGapAddress_real _
  have hOldPool (v : Fin N) (hv : v ∈ V)
      (hOld : v.val ≤ resolvedFairRetainedTop s0 n) : v ∈ V0 :=
    (resolvedNeutralCapPlan_old_iff s0 keep n v.val hOld).mp hv
  have hOldRole (v : Fin N) (hv : v ∈ V0) :
      ResolvedQRetainedBase (resolvedFairEventRole s0 keep v.val) :=
    resolvedNeutralCapOldPool_role s0 keep n v hv
  have hEligible (c : Nat) (v : Fin N)
      (h : c+1 ≤ ((oneGapPartial G').finitePrefix N).freeLevel v.val) :
      c+1 ≤ ((oneGapPartial G).finitePrefix N).freeLevel v.val := by
    rw [oneGapPartial_freeLevel _ _ _ v.isLt] at h ⊢
    exact h
  refine oneGap_planned_envelope_of_real_selected_neutrality G' 4 (by decide)
    (resolvedNeutralCapGraph_avoids s0 hEmpty n) N X top (Nat.lt_succ_self _)
    ?_ (I : Set Nat) (oneGapPairedLevels_zero _) hTopMem
    (fun q hq => resolvedNeutralCapPlan_bound s0 keep n q hq)
    ({vcap} : Set (Fin N)) V ?_ ?_ ?_ ?_ ?_ d target ?_ ?_ ?_ ?_
  · intro z hz
    have heq : z = resolvedNeutralCapType s0 hEmpty n := hz
    subst z
    change LevelTree.lev (resolvedNeutralCapType s0 hEmpty n) ≤ top
    rw [hCapLev]
    exact Nat.sub_le _ _
  · intro z hz
    have heq : z = resolvedNeutralCapType s0 hEmpty n := hz
    subst z
    exact ⟨resolvedNeutralCapType s0 hEmpty n, ⟨vcap, rfl, rfl⟩, le_rfl⟩
  · intro v hv
    have heq : v = vcap := hv
    subst v
    exact hTopMem
  · intro v hv _
    exact hv
  · intro z hz
    have heq : z = resolvedNeutralCapType s0 hEmpty n := hz
    subst z
    change LevelTree.lev (resolvedNeutralCapType s0 hEmpty n) ∈ I
    rw [hCapLev]
    exact oneGapPairedLevels_preceding_gap _ _ hTopMem hCapReal
  · intro v hv hr
    exact oneGapPairedLevels_preceding_gap _ _ hv hr
  · intro c hc hn hr v hv he hEdge
    obtain ⟨hOldC,hNot⟩ := hI0 c hc hn hr
    have hOldV : v.val ≤ resolvedFairRetainedTop s0 n := by
      by_contra h
      have hz := neutralPrefixGraph_padded_zero_right G p c v.val (Nat.lt_of_not_ge h)
      exact Bool.false_ne_true (hz.symm.trans hEdge)
    have hOmit : ¬ ResolvedQRetainedBase (resolvedFairEventRole s0 keep c) :=
      fun h => hNot ((resolvedFairRetainedLevels_real_iff s0 keep n c hr).mpr ⟨hOldC,h⟩)
    exact resolvedFairSelectedFront_positive s0 hEmpty keep N V0 hOldRole c hOmit v
      (hOldPool v hv hOldV) (hEligible c v he) ((hAgree c v.val hOldC hOldV).symm.trans hEdge)
  · intro c hc hn hr i j _ _ hOld
    obtain ⟨hOldC,hNot⟩ := hI0 c hc hn hr
    have heq : ∀ b < c, oneGapEdge G b (target c i) = oneGapEdge G b (target c j) := by
      intro b hb
      exact (hAgree b _ (by omega) (hTarget c i)).symm.trans
        ((hOld b hb).trans (hAgree b _ (by omega) (hTarget c j)))
    exact (hAgree c _ hOldC (hTarget c i)).trans
      ((hNoSplit c hOldC hNot hr i j heq).trans
        (hAgree c _ hOldC (hTarget c j)).symm)
  · intro c hc hn hr v hv he hNotSel b hb
    obtain ⟨hOldC,hNot⟩ := hI0 c hc hn hr
    by_cases hOldV : v.val ≤ resolvedFairRetainedTop s0 n
    · have hOmit : ¬ ResolvedQRetainedBase (resolvedFairEventRole s0 keep c) :=
        fun h => hNot ((resolvedFairRetainedLevels_real_iff s0 keep n c hr).mpr ⟨hOldC,h⟩)
      exact (hAgree b v.val (by omega) hOldV).trans
        (resolvedFairSelectedFront_other_zero s0 hEmpty keep N V0 hOldRole c hOmit v
          (hOldPool v hv hOldV) (hEligible c v he) hNotSel b hb)
    · exact neutralPrefixGraph_padded_zero_right G p b v.val (Nat.lt_of_not_ge hOldV)
  · intro c hc hn hr T
    obtain ⟨hOldC,hNot⟩ := hI0 c hc hn hr
    have hAgeEq (k : Nat) (hk : k ≤ c+1) :
        resolvedTargetAge (oneGapEdge G') 4 (Finset.range k) (target c) =
          resolvedTargetAge (oneGapEdge G) 4 (Finset.range k) (target c) := by
      unfold resolvedTargetAge
      have h := integerGraphAgeCanonical_induced_image_eq
        (oneGapEdge G) (oneGapEdge G') 4 (d c) (Finset.range k)
        (fun b i => oneGapEdge G b (target c i))
        (fun b i => oneGapEdge G' b (target c i)) id Function.injective_id
        (fun x hx y hy _ => hAgree x y
          (by have h := Finset.mem_range.mp hx; omega)
          (by have h := Finset.mem_range.mp hy; omega))
        (fun x hx i => hAgree x (target c i)
          (by have h := Finset.mem_range.mp hx; omega) (hTarget c i))
      simpa using h
    have h := (hAgeEq c (by omega)).trans
      ((hAge c hOldC hNot hr).trans (hAgeEq (c+1) le_rfl).symm)
    exact congrFun h T

/-- Every retained actual original prefix has a genuine representing
pair with the neutral cap as its common upper type. -/
theorem resolvedNeutralCap_actualPair
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (keep : Nat → Bool) (n i : Nat) (hi : i ≤ n)
    (hRet : resolvedFairOriginalAddress s0 i ∈ resolvedFairRetainedLevels s0 keep n) :
    ∃ P : GPlusRepresentingPair (hensonForbiddenFamily 4 (by decide)),
      P.vertex = resolvedFairEventOneGapOriginal s0 hEmpty i ∧
      P.upper = resolvedNeutralCapType s0 hEmpty n ∧
      LevelTree.lev P.lower ∈ resolvedNeutralCapPlan s0 keep n := by
  let U := resolvedNeutralCapType s0 hEmpty n
  let A := resolvedFairEventOneGapOriginal s0 hEmpty i
  let p := resolvedFairEventCodePosition s0 n
  let C := oneGapPartial (resolvedNeutralCapGraph s0 n)
  let N := resolvedNeutralCapSize s0 n
  let v : Fin N := ⟨resolvedNeutralCapTop s0 n, Nat.lt_succ_self _⟩
  have hOrd : RawPartialTypeNode.ordinaryCode U.1 = C.prefixCode (LevelTree.lev U) :=
    countableOriginal_ordinaryCode (hensonForbiddenFamily 4 (by decide)) C N v
      (oneGap_finitePrefix_avoids _ 4 (by decide) (resolvedNeutralCapGraph_avoids s0 hEmpty n) N)
  have hAddr : resolvedFairOriginalAddress s0 i ≤ resolvedFairRetainedTop s0 n :=
    (resolvedFairOriginalAddress_strictMono s0).monotone hi
  have hSize : A.val.size ≤ oneGapAddress p+1 := by
    change resolvedFairOriginalAddress s0 i+1 ≤ oneGapAddress p+1
    exact Nat.succ_le_succ hAddr
  have hCapLev : LevelTree.lev U = oneGapAddress p+1 := by
    change LevelTree.lev (resolvedNeutralCapType s0 hEmpty n) = _
    rw [resolvedNeutralCapType_level]
    change oneGapAddress (p+1)-1 = oneGapAddress p+1
    unfold oneGapAddress
    omega
  have hLen : A.val.size ≤ LevelTree.lev U := by rw [hCapLev]; exact hSize
  have hPrefix : A.val.IsPrefix (RawPartialTypeNode.ordinaryCode U.1) := by
    rw [hOrd]
    refine ⟨hLen, ?_⟩
    change A.val = (C.prefixCode (LevelTree.lev U)).restrict A.val.size hLen
    rw [C.prefixCode_restrict _ _ hLen]
    exact (neutralPrefixGraph_prefixCode_eq (resolvedFairEventEdge s0) p A.val.size hSize).symm
  let P := GPlusRepresentingPair.fromUpper U A.val.size
    (finiteGPlusVertex_size_pos A) hPrefix.1
  refine ⟨P, GPlusRepresentingPair.fromUpper_vertex_eq_of_prefix U A hPrefix, rfl, ?_⟩
  have hLower : LevelTree.lev P.lower = resolvedFairOriginalAddress s0 i := by
    change resolvedFairOriginalAddress s0 i+1-1 = _
    omega
  rw [hLower]
  exact (resolvedNeutralCapPlan_old_iff s0 keep n _ hAddr).mpr hRet

end Kk
