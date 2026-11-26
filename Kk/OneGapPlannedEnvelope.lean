import Kk.OneGapFullClosure
import SuccessorTree.V10.KptE1EnvelopeIntegration
import SuccessorTree.EnvelopeInvariantLevels
import SuccessorTree.V10.GPlusRetainedCodeRecovery
import Mathlib.Tactic

/-!
# Forced retained envelope
A predetermined finite retained set need not consist of interesting
levels. Use the already proved full stage invariant retaining and
skipping lemmas directly, not the stricter minimal AlgorithmRun.
-/
namespace Kk
open SuccessorTree
open SuccessorTree.V10
open SuccessorTree.SMTree.Envelope
universe u v

theorem planned_retained_envelope
    {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
    {S : STree T Label} (H : SMTree S)
    (hE1 : OneLevelPullback H)
    (X : Set T) (top : Nat) (hX : X ⊆ levelLe top)
    (I : Set Nat) (hTop : top ∈ I)
    (hBound : ∀ q ∈ I, q ≤ top)
    (hSkip : ∀ c : Nat, c < top → c ∉ I →
      (∀ z ∈ closure S {q | q ∈ I ∧ c+1 ≤ q} X, LevelTree.lev z ≠ c) ∧
      ∃ D : SMTree.MMap H, D.map.SkipsOnly c ∧
        (∀ ⦃z : T⦄, z ∈ closure S {q | q ∈ I ∧ c+1 ≤ q} X →
          ∀ (hc : c < LevelTree.lev z),
            D (LevelTree.ancestor z c (Nat.le_of_lt hc)) =
              LevelTree.ancestor z (c+1) (Nat.succ_le_iff.mpr hc))) :
    ∃ F : SMTree.MMap H, StageFullInvariant H X top 0 I F := by
  classical
  let J : Nat → Set Nat := fun c => {q | q ∈ I ∧ c ≤ q}
  have hBase : J top = {top} := by
    ext q
    change (q ∈ I ∧ top ≤ q) ↔ q ∈ ({top} : Set Nat)
    constructor
    · rintro ⟨hq,hlo⟩
      have hhi := hBound q hq
      exact Set.mem_singleton_iff.mpr (by omega)
    · intro hq
      have heq := Set.mem_singleton_iff.mp hq
      subst q
      exact ⟨hTop,le_rfl⟩
  have hMain : ∀ n : Nat, ∀ c : Nat, c ≤ top → top-c = n →
      ∃ F : SMTree.MMap H, StageFullInvariant H X top c (J c) F := by
    intro n
    induction n with
    | zero =>
      intro c hc hn
      have heq : c = top := by omega
      subst c
      rw [hBase]
      exact ⟨SMTree.MMap.id H,stageFullInvariant_base H X top⟩
    | succ n ih =>
      intro c hc hn
      have hlt : c < top := by omega
      obtain ⟨F,hF⟩ := ih (c+1) (by omega) (by omega)
      by_cases hRet : c ∈ I
      · have hEq : J c = insert c (J (c+1)) := by
          ext q
          change (q ∈ I ∧ c ≤ q) ↔ q = c ∨ (q ∈ I ∧ c+1 ≤ q)
          constructor
          · rintro ⟨hq,hcq⟩
            by_cases h : q = c
            · exact Or.inl h
            · exact Or.inr ⟨hq,by omega⟩
          · rintro (rfl | ⟨hq,hcq⟩)
            · exact ⟨hRet,le_rfl⟩
            · exact ⟨hq,by omega⟩
        rw [hEq]
        exact ⟨F,stageFullInvariant_interesting H X top c (J (c+1)) F hlt hF⟩
      · have hEq : J c = J (c+1) := by
          ext q
          change (q ∈ I ∧ c ≤ q) ↔ (q ∈ I ∧ c+1 ≤ q)
          constructor
          · rintro ⟨hq,hcq⟩
            have hne : q ≠ c := fun h => hRet (h ▸ hq)
            exact ⟨hq,by omega⟩
          · rintro ⟨hq,hcq⟩
            exact ⟨hq,by omega⟩
        obtain ⟨hNo,D,hDskip,hDcross⟩ := hSkip c hlt hRet
        rw [hEq]
        exact ⟨SMTree.MMap.comp H F D,
          stageFullInvariant_noninteresting H hE1 X top c hX
            (J (c+1)) F D hlt hF hDskip hNo hDcross⟩
  obtain ⟨F,hF⟩ := hMain top 0 (Nat.zero_le top) (by omega)
  have hZero : J 0 = I := by ext q; simp [J]
  rw [hZero] at hF
  exact ⟨F,hF⟩

/-- A complete prescribed crossing plus corrected B3 yields an
actual one-gap monoid map covering every crossing. -/
theorem oneGap_skip_of_complete_prescribed_B3
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family))
    (cut : Nat) (hPos : 0 < cut)
    (F : PrescribedBoringData cut db du dd)
    (hCover : CoversClosureCrossing family Z cut F)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨cut+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hB3 : F.CorrectedB3 family) :
    ∃ D : SMTree.MMap (normalizedKptSMTree family),
      D.map.SkipsOnly cut ∧
      ∀ ⦃z : AdmissibleKptNode family⦄, z ∈ Z →
        ∀ (hc : cut < LevelTree.lev z),
          D (LevelTree.ancestor z cut (Nat.le_of_lt hc)) =
            LevelTree.ancestor z (cut+1) (Nat.succ_le_iff.mpr hc) := by
  obtain ⟨Φ,hMem,hSkip,hVal⟩ :=
    F.prescribedKpt_boring_extension_exists family hB3 hTargets hPos
  let D : SMTree.MMap (normalizedKptSMTree family) := ⟨Φ,hMem⟩
  refine ⟨D,hSkip,?_⟩
  intro z hz hc
  obtain ⟨T,hT,hOld,hNew⟩ := hCover z hz hc
  let oldNode := LevelTree.ancestor z cut (Nat.le_of_lt hc)
  let nextNode := LevelTree.ancestor z (cut+1) (Nat.succ_le_iff.mpr hc)
  have hAd : IsAdmissibleRawType family
      (⟨cut,T⟩ : RawPartialTypeNode db du dd) := by
    rw [hOld]
    exact oldNode.property
  have hOldEq : (⟨⟨cut,T⟩,hAd⟩ : AdmissibleKptNode family) = oldNode :=
    Subtype.ext hOld
  apply Subtype.ext
  change (Φ oldNode).val = nextNode.val
  rw [← hOldEq]
  exact (hVal T hT hAd).trans hNew

/-- E1 is discharged by the already proved normalized Kpt theorem. -/
theorem oneGap_planned_Kpt_envelope
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat) (hX : X ⊆ levelLe top)
    (I : Set Nat) (hZero : 0 ∈ I) (hTop : top ∈ I)
    (hBound : ∀ q ∈ I, q ≤ top)
    (hLocal : ∀ c : Nat, c < top → c ∉ I →
      let Z := closure (admissibleKptSTree family) {q | q ∈ I ∧ c+1 ≤ q} X
      (∀ z ∈ Z, LevelTree.lev z ≠ c) ∧
        ∃ F : PrescribedBoringData c db du dd,
          CoversClosureCrossing family Z c F ∧
          (∀ S, S ∈ F.source → IsAdmissibleRawType family
            (⟨c+1,F.target S⟩ : RawPartialTypeNode db du dd)) ∧
          F.CorrectedB3 family) :
    ∃ F : SMTree.MMap (normalizedKptSMTree family),
      StageFullInvariant (normalizedKptSMTree family) X top 0 I F := by
  apply planned_retained_envelope (normalizedKptSMTree family)
    (normalizedKpt_oneLevelPullback_for_envelopes family)
    X top hX I hTop hBound
  intro c hc hnot
  have hPos : 0 < c := by
    by_contra h
    have heq : c = 0 := by omega
    exact hnot (heq.symm ▸ hZero)
  obtain ⟨hNo,F,hCover,hTargets,hB3⟩ := hLocal c hc hnot
  exact ⟨hNo,oneGap_skip_of_complete_prescribed_B3 family _ c hPos
    F hCover hTargets hB3⟩

end Kk
