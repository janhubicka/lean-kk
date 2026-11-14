import Kk.NumericHPrefixB3Stability
import Mathlib.Tactic

/-!
# Track C: REAL old H+ source survives adding NEW BASE Henson originals

English mathematical proof / 18 hostile checks committed BEFORE Lean:
  docs/track_c_base_extension_coherence_english_audit.md

Two base age-test models K,L need only have identical atomic tables
on old ORIGINAL BLOCKS [0,b). Their new Henson original columns at
j>=b can be different; no global equality K=L is assumed.

If N <= hPosition k b 0, ALL real numerical coordinates x<N
belong to original blocks i<b. Thus the entire old generated
numerical L table agrees even though the ambient base graph changed.

Combine this literal old L agreement with the generated target-
clipped E constructor (independent of base K) and with Track C's
already verified fixed-base numerical-carrier growth N<=M.
The whole old Kpt original, its E free level, all dependent
complete L+ types, and EVERY old seed/parameter/meet closure node
then retain their physical original prefix representation.

We do NOT construct newly reserved columns, prove that a proposed
unbounded resolved schedule is safe, or compare distinct diary
occurrences. New-column K-free certificates belong to Tracks A/B.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- If a real numerical coordinate lies below the FIRST coordinate
of base-original block b, its base original index lies below b.
The generation q need not even be bounded for this direction. -/
theorem hPosition_old_block_of_lt_frontier
    (k b x i q : Nat)
    (hOld : x < hPosition k b 0)
    (hPos : x = hPosition k i q) :
    i < b := by
  by_contra hNot
  have hbi : b ≤ i := by omega
  have hMul := Nat.mul_le_mul_left (2*(k+1)) hbi
  unfold hPosition at hOld hPos
  omega

/-- Complete directed NUMERICAL L atom below an old block boundary
does not depend on NEW base-original edges. The old base table
must agree on both directed pairs of indices strictly below b. -/
theorem hNumericBinary_old_block_base_eq
    {db : Nat}
    (B C : Nat → Nat → Fin db → Bool)
    (k b x y : Nat)
    (hx : x < hPosition k b 0)
    (hy : y < hPosition k b 0)
    (hBase : ∀ i j : Nat, i < b → j < b →
      ∀ r : Fin db, B i j r = C i j r)
    (r : Fin db) :
    hNumericBinary B k x y r = hNumericBinary C k x y r := by
  have hIff :
      hNumericBinary B k x y r = true ↔
        hNumericBinary C k x y r = true := by
    rw [hNumericBinary_true_iff, hNumericBinary_true_iff]
    constructor
    · rintro ⟨i,j,q,m,hij,hq,hm,hGate,hDir⟩
      refine ⟨i,j,q,m,hij,hq,hm,hGate,?_⟩
      rcases hDir with ⟨hX,hY,hBit⟩ | ⟨hX,hY,hBit⟩
      · have hi := hPosition_old_block_of_lt_frontier
          k b x i q hx hX
        have hj := hPosition_old_block_of_lt_frontier
          k b y j m hy hY
        exact Or.inl ⟨hX,hY,(hBase i j hi hj r).symm.trans hBit⟩
      · have hj := hPosition_old_block_of_lt_frontier
          k b x j m hx hX
        have hi := hPosition_old_block_of_lt_frontier
          k b y i q hy hY
        exact Or.inr ⟨hX,hY,(hBase j i hj hi r).symm.trans hBit⟩
    · rintro ⟨i,j,q,m,hij,hq,hm,hGate,hDir⟩
      refine ⟨i,j,q,m,hij,hq,hm,hGate,?_⟩
      rcases hDir with ⟨hX,hY,hBit⟩ | ⟨hX,hY,hBit⟩
      · have hi := hPosition_old_block_of_lt_frontier
          k b x i q hx hX
        have hj := hPosition_old_block_of_lt_frontier
          k b y j m hy hY
        exact Or.inl ⟨hX,hY,(hBase i j hi hj r).trans hBit⟩
      · have hj := hPosition_old_block_of_lt_frontier
          k b x j m hx hX
        have hi := hPosition_old_block_of_lt_frontier
          k b y i q hy hY
        exact Or.inr ⟨hX,hY,(hBase j i hj hi r).trans hBit⟩
  cases hB : hNumericBinary B k x y r with
  | false =>
      cases hC : hNumericBinary C k x y r with
      | false => rfl
      | true =>
          have hImpossible := hIff.mpr hC
          simp [hB] at hImpossible
  | true =>
      cases hC : hNumericBinary C k x y r with
      | true => rfl
      | false =>
          have hImpossible := hIff.mp hB
          simp [hC] at hImpossible

/-- Each old real-generation coordinate sees precisely the old
unary/diagonal singleton fields of its original base index. Fake
coordinates see false in BOTH models. -/
theorem hNumericSingleton_old_block_base_eq
    {d : Nat}
    (U V : Nat → Fin d → Bool)
    (k b x : Nat)
    (hx : x < hPosition k b 0)
    (hBase : ∀ i : Nat, i < b → ∀ r : Fin d,
      U i r = V i r) :
    hNumericSingleton U k x = hNumericSingleton V k x := by
  classical
  by_cases hReal : ∃ i g : Nat, g ≤ k ∧ x = hPosition k i g
  · obtain ⟨g,hg,hxPos⟩ := Classical.choose_spec hReal
    have hi : Classical.choose hReal < b :=
      hPosition_old_block_of_lt_frontier
        k b x (Classical.choose hReal) g hx hxPos
    simp only [hNumericSingleton, dif_pos hReal]
    funext r
    exact hBase (Classical.choose hReal) hi r
  · simp [hNumericSingleton, hReal]

/-- Canonical E free cut of an old numerical coordinate stays EXACT
when the underlying base K is replaced by L and the finite numerical
carrier grows N<=M. E depends on fixed k and the target clipping
ONLY; all old incoming E pairs are unchanged even if base L differs. -/
theorem finiteNumericH_baseExtension_old_freeLevel_eq
    {db du dd : Nat}
    (K L : AgeTestModel db du dd)
    (k N M : Nat) (hNM : N ≤ M)
    (v : Nat) (hv : v < N) :
    (finiteNumericH K k N).freeLevel v =
      (finiteNumericH L k M).freeLevel v := by
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  let B : EnumeratedPartialStructure db du dd := finiteNumericH L k N
  have hColumn : ∀ u : Nat, A.E u v = B.E u v := by
    intro u
    rfl
  have hCutA : IsFreeCut A.E v (A.freeLevel v) :=
    canonicalFreeLevel_isFreeCut A.E A.spaced A.downward v
  have hCutB : IsFreeCut B.E v (A.freeLevel v) := by
    constructor
    · intro u hu
      rw [← hColumn u]
      exact hCutA.1 u hu
    · rw [← hColumn (A.freeLevel v)]
      exact hCutA.2
  have hB : IsFreeCut B.E v (B.freeLevel v) :=
    canonicalFreeLevel_isFreeCut B.E B.spaced B.downward v
  have hOld : A.freeLevel v = B.freeLevel v :=
    freeCut_unique B.E v (A.freeLevel v) (B.freeLevel v) hCutB hB
  exact hOld.trans
    (finiteNumericH_prefix_old_freeLevel_eq L k N M hNM v hv)

/-- The COMPLETE dependent old L+ type of a genuine old numerical
coordinate is preserved after inserting NEW BASE Henson originals
and growing the numerical-H+ carrier.

Both base models have identical old original columns through b.
Old numerical carrier N ends BEFORE the first new base block b.
Cuts must remain within N to avoid new E target atoms.
No assumption K=L, nor equality of their carrier fields. -/
theorem finiteNumericH_baseExtension_old_full_Lplus_type_eq
    {db du dd : Nat}
    (K L : AgeTestModel db du dd)
    (k b N M : Nat) (hNM : N ≤ M)
    (hBlock : N ≤ hPosition k b 0)
    (hBin : ∀ i j : Nat, i < b → j < b →
      ∀ r : Fin db, K.binary i j r = L.binary i j r)
    (hUn : ∀ i : Nat, i < b → ∀ r : Fin du,
      K.unary i r = L.unary i r)
    (hDiag : ∀ i : Nat, i < b → ∀ r : Fin dd,
      K.diagonal i r = L.diagonal i r)
    (cut v : Nat) (hCut : cut ≤ N) (hv : v < N) :
    (finiteNumericH K k N).partialTypeAt cut v =
      (finiteNumericH L k M).partialTypeAt cut v := by
  have hSameN :
      (finiteNumericH K k N).partialTypeAt cut v =
        (finiteNumericH L k N).partialTypeAt cut v := by
    apply PartialTypeWithE.eq_of_atoms
    · apply RelationalPrefixType.eq_of_atoms
      · intro x y r
        have hIndex : ∀ z : Option (Fin cut),
            prefixVertexIndex v z < N := by
          intro z
          cases z with
          | none => exact hv
          | some t => exact lt_of_lt_of_le t.isLt hCut
        change hNumericBinary K.binary k
            (prefixVertexIndex v x) (prefixVertexIndex v y) r =
          hNumericBinary L.binary k
            (prefixVertexIndex v x) (prefixVertexIndex v y) r
        exact hNumericBinary_old_block_base_eq
          K.binary L.binary k b
          (prefixVertexIndex v x) (prefixVertexIndex v y)
          (lt_of_lt_of_le (hIndex x) hBlock)
          (lt_of_lt_of_le (hIndex y) hBlock)
          hBin r
      · intro x r
        have hIndex : prefixVertexIndex v x < N := by
          cases x with
          | none => exact hv
          | some t => exact lt_of_lt_of_le t.isLt hCut
        change hNumericSingleton K.unary k
          (prefixVertexIndex v x) r =
          hNumericSingleton L.unary k (prefixVertexIndex v x) r
        exact congrFun
          (hNumericSingleton_old_block_base_eq
            K.unary L.unary k b (prefixVertexIndex v x)
            (lt_of_lt_of_le hIndex hBlock) hUn) r
      · intro x r
        have hIndex : prefixVertexIndex v x < N := by
          cases x with
          | none => exact hv
          | some t => exact lt_of_lt_of_le t.isLt hCut
        change hNumericSingleton K.diagonal k
          (prefixVertexIndex v x) r =
          hNumericSingleton L.diagonal k (prefixVertexIndex v x) r
        exact congrFun
          (hNumericSingleton_old_block_base_eq
            K.diagonal L.diagonal k b (prefixVertexIndex v x)
            (lt_of_lt_of_le hIndex hBlock) hDiag) r
    · intro x y
      rfl
  exact hSameN.trans
    (finiteNumericH_prefix_old_full_Lplus_type_eq
      L k N M hNM cut v hCut hv)

/-- E-free level AND full old L+ records give literally the SAME
raw Kpt source node after the base Henson graph and numeric
carrier both grow. This is the actual free-level source,
not a fictitious node at numeric coordinate v. -/
theorem finiteNumericH_baseExtension_old_rawOriginal_eq
    {db du dd : Nat}
    (K L : AgeTestModel db du dd)
    (k b N M : Nat) (hNM : N ≤ M)
    (hBlock : N ≤ hPosition k b 0)
    (hBin : ∀ i j : Nat, i < b → j < b →
      ∀ r : Fin db, K.binary i j r = L.binary i j r)
    (hUn : ∀ i : Nat, i < b → ∀ r : Fin du,
      K.unary i r = L.unary i r)
    (hDiag : ∀ i : Nat, i < b → ∀ r : Fin dd,
      K.diagonal i r = L.diagonal i r)
    (v : Nat) (hv : v < N) :
    (finiteNumericH K k N).rawTypeAtFree v =
      (finiteNumericH L k M).rawTypeAtFree v := by
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  let B : EnumeratedPartialStructure db du dd := finiteNumericH L k M
  have hFree : A.freeLevel v = B.freeLevel v :=
    finiteNumericH_baseExtension_old_freeLevel_eq
      K L k N M hNM v hv
  have hCut : A.freeLevel v ≤ N :=
    (A.freeLevel_le v).trans (Nat.le_of_lt hv)
  have hType : A.partialTypeAt (A.freeLevel v) v =
      B.partialTypeAt (A.freeLevel v) v :=
    finiteNumericH_baseExtension_old_full_Lplus_type_eq
      K L k b N M hNM hBlock hBin hUn hDiag
      (A.freeLevel v) v hCut hv
  change
    (⟨A.freeLevel v, A.partialTypeAt (A.freeLevel v) v⟩ :
      RawPartialTypeNode db du dd) =
    (⟨B.freeLevel v, B.partialTypeAt (B.freeLevel v) v⟩ :
      RawPartialTypeNode db du dd)
  rw [← hFree]
  exact congrArg
    (fun T : PartialTypeWithE (A.freeLevel v) db du dd =>
      (⟨A.freeLevel v, T⟩ : RawPartialTypeNode db du dd)) hType

/-- Actual admissible Kpt ORIGINAL old nodes are equal on the nose,
not just L-equivalent, after fresh base graph extension.

No new E is introduced by transport: each full L+ source
has exactly the original numeric-H E free cut and all L atoms.
The two different forbidden-avoidance proofs are irrelevant
by subtype proof irrelevance. -/
theorem finiteNumericH_baseExtension_old_KptOriginal_eq
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K L : AgeTestModel db du dd)
    (k b N M : Nat) (hNM : N ≤ M)
    (hBlock : N ≤ hPosition k b 0)
    (hBin : ∀ i j : Nat, i < b → j < b →
      ∀ r : Fin db, K.binary i j r = L.binary i j r)
    (hUn : ∀ i : Nat, i < b → ∀ r : Fin du,
      K.unary i r = L.unary i r)
    (hDiag : ∀ i : Nat, i < b → ∀ r : Fin dd,
      K.diagonal i r = L.diagonal i r)
    (hAvoidK : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hAvoidL : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (v : Fin N) :
    (finiteNumericH K k N).kptOriginal family hAvoidK v =
      (finiteNumericH L k M).kptOriginal family hAvoidL
        (Fin.castLE hNM v) := by
  apply Subtype.ext
  change (finiteNumericH K k N).rawTypeAtFree v.val =
    (finiteNumericH L k M).rawTypeAtFree v.val
  exact finiteNumericH_baseExtension_old_rawOriginal_eq
    K L k b N M hNM hBlock hBin hUn hDiag v.val v.isLt

/-- Old genuine Kpt seed prefixes remain below the SAME ACTUAL
original Kpt nodes after adding new base Henson originals AND
enlarging their finite numeric-H carrier. A root pool U is
relocated only by its physical Fin.castLE address inclusion. -/
theorem finiteNumericH_baseExtension_old_seedPool_lifts
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K L : AgeTestModel db du dd)
    (k b N M : Nat) (hNM : N ≤ M)
    (hBlock : N ≤ hPosition k b 0)
    (hBin : ∀ i j : Nat, i < b → j < b →
      ∀ r : Fin db, K.binary i j r = L.binary i j r)
    (hUn : ∀ i : Nat, i < b → ∀ r : Fin du,
      K.unary i r = L.unary i r)
    (hDiag : ∀ i : Nat, i < b → ∀ r : Fin dd,
      K.diagonal i r = L.diagonal i r)
    (hAvoidK : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hAvoidL : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (U : Set (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hSeeds : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoidK U) :
    X ⊆ ambientPrefixPool family
      (finiteNumericH L k M) hAvoidL
        ((Fin.castLE hNM) '' U) := by
  intro z hz
  obtain ⟨o,⟨v,hv,rfl⟩,hBelow⟩ := hSeeds hz
  refine ⟨(finiteNumericH L k M).kptOriginal family hAvoidL
      (Fin.castLE hNM v), ?_, ?_⟩
  · exact ⟨Fin.castLE hNM v, ⟨v,hv,rfl⟩, rfl⟩
  · rw [← finiteNumericH_baseExtension_old_KptOriginal_eq
      family K L k b N M hNM hBlock hBin hUn hDiag
      hAvoidK hAvoidL v]
    exact hBelow

/-- The ENTIRE old genuine Kpt meet-and-parameter closure
of unchanged X and selected-level set I has a REAL old-prefix
source representation in the enlarged finite numerical-H+ of
an EXTENDED base Henson graph.

This is an induction interface across TWO kinds of growth:
new base original blocks and new numerical-H carrier coordinates.
It does not certify the newly introduced reserved originals'
negative clique certificates or their prescribed fresh columns. -/
theorem finiteNumericH_baseExtension_full_closure_pool_lifts
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K L : AgeTestModel db du dd)
    (k b N M : Nat) (hNM : N ≤ M)
    (hBlock : N ≤ hPosition k b 0)
    (hBin : ∀ i j : Nat, i < b → j < b →
      ∀ r : Fin db, K.binary i j r = L.binary i j r)
    (hUn : ∀ i : Nat, i < b → ∀ r : Fin du,
      K.unary i r = L.unary i r)
    (hDiag : ∀ i : Nat, i < b → ∀ r : Fin dd,
      K.diagonal i r = L.diagonal i r)
    (hAvoidK : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hAvoidL : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (U : Set (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hSeeds : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoidK U)
    (I : Set Nat) :
    SMTree.Envelope.closure (admissibleKptSTree family) I X ⊆
      ambientPrefixPool family (finiteNumericH L k M) hAvoidL
        (ambientStagePool (finiteNumericH L k M)
          ((Fin.castLE hNM) '' U) I) := by
  have hLift := finiteNumericH_baseExtension_old_seedPool_lifts
    family K L k b N M hNM hBlock hBin hUn hDiag
    hAvoidK hAvoidL U X hSeeds
  exact admissibleKpt_stage_closure_subset_pool
    family (finiteNumericH L k M) hAvoidL
    ((Fin.castLE hNM) '' U) I X hLift

#print axioms Kk.hPosition_old_block_of_lt_frontier
#print axioms Kk.hNumericBinary_old_block_base_eq
#print axioms Kk.hNumericSingleton_old_block_base_eq
#print axioms Kk.finiteNumericH_baseExtension_old_freeLevel_eq
#print axioms Kk.finiteNumericH_baseExtension_old_full_Lplus_type_eq
#print axioms Kk.finiteNumericH_baseExtension_old_rawOriginal_eq
#print axioms Kk.finiteNumericH_baseExtension_old_KptOriginal_eq
#print axioms Kk.finiteNumericH_baseExtension_old_seedPool_lifts
#print axioms Kk.finiteNumericH_baseExtension_full_closure_pool_lifts

end Kk
