import Kk.PrefixEnvelopeLift
import Mathlib.Tactic

/-!
# Recovering labels from the order of finite prefix codes

The generic envelope theorem compares unlabelled inverse-image sets.
For an ordered selected copy in the G+ prefix presentation, however,
the source vertices have distinct, strictly increasing code sizes.

A finite set with a strictly increasing enumeration by code size has
ONLY ONE such enumeration. Thus equality of the unlabelled sets of
source codes already forces equality of the labelled tuples.

This is weaker than comparing every labelled singleton preimage
separately. The unresolved diary-specific step becomes equality of
the unlabelled source-code sets under envelopes, together with actual
target prefix-chain and endpoint coverage.

The uniqueness lemma is purely finite order theory; the application
uses the actual G+ prefix reflection theorem.
-/

namespace Kk

open SuccessorTree.V10

universe u

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- Two strictly increasing finite enumerations of the same subset
of natural numbers coincide pointwise. The proof works also for
the empty indexed set and has no finiteness axiom. -/
theorem strictMono_fin_nat_eq_of_same_range
    {n : Nat} (f g : Fin n → Nat)
    (hf : StrictMono f) (hg : StrictMono g)
    (hRange : Set.range f = Set.range g) : f = g := by
  have hByVal : ∀ k : Nat, ∀ i : Fin n, i.val = k → f i = g i := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hik
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hMember : f i ∈ Set.range g := by
          rw [← hRange]
          exact ⟨i, rfl⟩
        obtain ⟨j, hj⟩ := hMember
        have hji : j < i := by
          by_contra hnot
          have hij : i ≤ j := le_of_not_gt hnot
          have hmono := hg.monotone hij
          rw [hj] at hmono
          exact (not_le_of_gt hlt) hmono
        have hjk : j.val < k := by
          have hval : j.val < i.val := hji
          omega
        have hEq : f j = g j := ih j.val hjk j rfl
        have hstrict := hf hji
        rw [hEq, hj] at hstrict
        exact (lt_irrefl _) hstrict
      · have hMember : g i ∈ Set.range f := by
          rw [hRange]
          exact ⟨i, rfl⟩
        obtain ⟨j, hj⟩ := hMember
        have hji : j < i := by
          by_contra hnot
          have hij : i ≤ j := le_of_not_gt hnot
          have hmono := hf.monotone hij
          rw [hj] at hmono
          exact (not_le_of_gt hgt) hmono
        have hjk : j.val < k := by
          have hval : j.val < i.val := hji
          omega
        have hEq : f j = g j := ih j.val hjk j rfl
        have hstrict := hg hji
        rw [← hEq, hj] at hstrict
        exact (lt_irrefl _) hstrict
  funext i
  exact hByVal i.val i rfl

/-- For actual finite G+ vertices, the ordinary length supplies
the strictly increasing rank. If two labelled lists have equal
UNLABELLED code sets and both are increasing by length, they are
the same labelled copy, without checking singleton preimages. -/
theorem labelled_codes_eq_of_same_range
    {n : Nat}
    (f g : Fin n → FiniteGPlusVertex family)
    (hf : StrictMono (fun i : Fin n => (f i).val.size))
    (hg : StrictMono (fun i : Fin n => (g i).val.size))
    (hRange : Set.range f = Set.range g) : f = g := by
  have hSizeRange :
      Set.range (fun i : Fin n => (f i).val.size) =
      Set.range (fun i : Fin n => (g i).val.size) := by
    ext m
    constructor
    · rintro ⟨i, rfl⟩
      have hMem : f i ∈ Set.range g := by
        rw [← hRange]
        exact ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := hMem
      exact ⟨j, congrArg
        (fun v : FiniteGPlusVertex family => v.val.size) hj⟩
    · rintro ⟨i, rfl⟩
      have hMem : g i ∈ Set.range f := by
        rw [hRange]
        exact ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := hMem
      exact ⟨j, congrArg
        (fun v : FiniteGPlusVertex family => v.val.size) hj⟩
  have hSizes : (fun i : Fin n => (f i).val.size) =
      (fun i : Fin n => (g i).val.size) :=
    strictMono_fin_nat_eq_of_same_range
      (fun i => (f i).val.size) (fun i => (g i).val.size)
      hf hg hSizeRange
  funext i
  have hMem : f i ∈ Set.range g := by
    rw [← hRange]
    exact ⟨i, rfl⟩
  obtain ⟨j, hj⟩ := hMem
  have hSizeEq : (g j).val.size = (g i).val.size := by
    calc
      (g j).val.size = (f i).val.size :=
        congrArg (fun v : FiniteGPlusVertex family => v.val.size) hj
      _ = (g i).val.size := congrArg (fun h : Fin n → Nat => h i) hSizes
  have hji : j = i := hg.injective hSizeEq
  rw [hji] at hj
  exact hj.symm

/-- Under genuine shape maps, a target labelled strict prefix chain
has an increasing source-code size sequence. Hence two such source
families with the same UNLABELLED range must coincide labelwise.

This can potentially replace the much stronger individual singleton-
preimage equalities in the cross-occurrence diary comparison. -/
theorem labelled_prefix_sources_eq_of_unlabelled_range
    {n : Nat}
    (F G : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (targetF targetG : Fin n → FiniteGPlusVertex family)
    (sourceF sourceG : Fin n → FiniteGPlusVertex family)
    (hTargetF : ∀ i, gPlusShapeImage F.map (sourceF i) = targetF i)
    (hTargetG : ∀ i, gPlusShapeImage G.map (sourceG i) = targetG i)
    (hStrictF : ∀ i j : Fin n, i < j →
       (targetF i).IsProperPrefix (targetF j))
    (hStrictG : ∀ i j : Fin n, i < j →
       (targetG i).IsProperPrefix (targetG j))
    (hSameSourceSet : Set.range sourceF = Set.range sourceG) :
    sourceF = sourceG := by
  have hFSize : StrictMono (fun i : Fin n => (sourceF i).val.size) := by
    intro i j hij
    have hPrefix : (sourceF i).IsProperPrefix (sourceF j) := by
      apply (gPlusShapeImage_properPrefix_iff F.map _ _).mp
      rw [hTargetF i, hTargetF j]
      exact hStrictF i j hij
    exact hPrefix.2
  have hGSize : StrictMono (fun i : Fin n => (sourceG i).val.size) := by
    intro i j hij
    have hPrefix : (sourceG i).IsProperPrefix (sourceG j) := by
      apply (gPlusShapeImage_properPrefix_iff G.map _ _).mp
      rw [hTargetG i, hTargetG j]
      exact hStrictG i j hij
    exact hPrefix.2
  exact labelled_codes_eq_of_same_range sourceF sourceG
    hFSize hGSize hSameSourceSet


/-- The source vertices representing ALL members of a target copy
are precisely the full inverse image of the target vertex set under
the genuine injective G+ action.

Crucially, the equality includes no hidden source vertices: the
induced action is injective, so an image lying in the finite target
set must be the unique prescribed source vertex of some label. -/
theorem source_range_eq_inverse_image
    {n : Nat}
    (F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (target source : Fin n → FiniteGPlusVertex family)
    (hImage : ∀ i, gPlusShapeImage F.map (source i) = target i) :
    Set.range source =
      (gPlusShapeImage F.map) ⁻¹' (Set.range target) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    change gPlusShapeImage F.map (source i) ∈ Set.range target
    exact ⟨i, (hImage i).symm⟩
  · intro hx
    change gPlusShapeImage F.map x ∈ Set.range target at hx
    obtain ⟨i, hi⟩ := hx
    have hEq : source i = x :=
      (gPlusShapeImage_injective F.map) ((hImage i).trans hi)
    exact ⟨i, hEq⟩

/-- The exact application-facing comparison lemma: equality of the
UNLABELLED inverse images of two target selected sets, under their
actual induced Kpt/G+ maps, already forces equality of the labelled
source prefix chains.

This directly matches the weakened obligation displayed in the
olive diary-envelope proof. It does not establish the inverse-image
equality, which remains the K_k-specific parameter-closed age step. -/
theorem labelled_prefix_sources_eq_of_inverse_image_sets
    {n : Nat}
    (F G : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (targetF targetG : Fin n → FiniteGPlusVertex family)
    (sourceF sourceG : Fin n → FiniteGPlusVertex family)
    (hTargetF : ∀ i, gPlusShapeImage F.map (sourceF i) = targetF i)
    (hTargetG : ∀ i, gPlusShapeImage G.map (sourceG i) = targetG i)
    (hStrictF : ∀ i j : Fin n, i < j →
       (targetF i).IsProperPrefix (targetF j))
    (hStrictG : ∀ i j : Fin n, i < j →
       (targetG i).IsProperPrefix (targetG j))
    (hInverse :
      (gPlusShapeImage F.map) ⁻¹' (Set.range targetF) =
      (gPlusShapeImage G.map) ⁻¹' (Set.range targetG)) :
    sourceF = sourceG := by
  have hRange : Set.range sourceF = Set.range sourceG := by
    calc
      Set.range sourceF =
          (gPlusShapeImage F.map) ⁻¹' (Set.range targetF) :=
        source_range_eq_inverse_image F targetF sourceF hTargetF
      _ = (gPlusShapeImage G.map) ⁻¹' (Set.range targetG) := hInverse
      _ = Set.range sourceG :=
        (source_range_eq_inverse_image G targetG sourceG hTargetG).symm
  exact labelled_prefix_sources_eq_of_unlabelled_range
    F G targetF targetG sourceF sourceG
    hTargetF hTargetG hStrictF hStrictG hRange

end Kk
