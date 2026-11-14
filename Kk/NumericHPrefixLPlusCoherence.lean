import Kk.NumericHMultiRootPreservation
import Mathlib.Tactic

/-!
# Track C: exact old-source preservation across growing numerical H+ prefixes

English proof and 16 hostile checks were COMMITTED BEFORE Lean:
  docs/track_c_numeric_prefix_Lplus_coherence_english_audit.md

For FIXED base K and generation k, enlarging the finite physical
numerical-H+ carrier N to M preserves the COMPLETE old dependent L+
types of every original v<N, including its entire E column and
canonical E free level. This is not merely a graph-language
age-preservation statement.

The key guards are:
  v<N and (for partial types) cut<=N.
The auxiliary finite E relation is CLIPPED BY ITS TARGET; extending
the carrier may create new E targets outside the old prefix. Hence
unqualified equality at arbitrary cuts is FALSE.

As a geometric application, genuine old Kpt originals, seed prefix
pools and selected-positive parameter-root stage pools all transport
to the enlarged physical structure. No new reserved-column
realization, cross-generation change, or common labelled orbit is
asserted.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Exact incoming auxiliary E column of an OLD numerical H+ target
does not change when the finite carrier grows. This holds for ALL
possible source u, including odd fake coordinates, because the
literal finite E constructor clips only its target v. -/
theorem finiteNumericH_prefix_old_E_column_eq
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N M : Nat) (hNM : N ≤ M)
    (u v : Nat) (hv : v < N) :
    (finiteNumericH K k N).E u v =
      (finiteNumericH K k M).E u v := by
  change finiteNumericHE k N u v = finiteNumericHE k M u v
  have hvM : v < M := lt_of_lt_of_le hv hNM
  simp [finiteNumericHE, hv, hvM]

/-- Canonical E free cut of a physical OLD target is independent
of a larger finite prefix. The proof transports the actual entire
incoming E column and appeals to uniqueness of the FIRST MISSING
E coordinate; it does not infer anything from old L adjacency. -/
theorem finiteNumericH_prefix_old_freeLevel_eq
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N M : Nat) (hNM : N ≤ M)
    (v : Nat) (hv : v < N) :
    (finiteNumericH K k N).freeLevel v =
      (finiteNumericH K k M).freeLevel v := by
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  let B : EnumeratedPartialStructure db du dd := finiteNumericH K k M
  have hColumn : ∀ u : Nat, A.E u v = B.E u v := by
    intro u
    exact finiteNumericH_prefix_old_E_column_eq K k N M hNM u v hv
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
  exact freeCut_unique B.E v (A.freeLevel v) (B.freeLevel v)
    hCutB hB

/-- Every old complete dependent partial type in the literal H+ model
is preserved at every OLD cut. This includes binary atoms in BOTH
orientations, unary and diagonal atoms, auxiliary E and all absent
atoms, with no extra E assigned to an L-only age witness.

The cut bound cut<=N is ESSENTIAL: E targets in a new socle
[N,M) can differ between the two finite models. -/
theorem finiteNumericH_prefix_old_full_Lplus_type_eq
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N M : Nat) (hNM : N ≤ M)
    (cut v : Nat) (hCut : cut ≤ N) (hv : v < N) :
    (finiteNumericH K k N).partialTypeAt cut v =
      (finiteNumericH K k M).partialTypeAt cut v := by
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro x y r
      rfl
    · intro x r
      rfl
    · intro x r
      rfl
  · intro x y
    have hTargetN : prefixVertexIndex v y < N := by
      cases y with
      | none =>
          simpa only [prefixVertexIndex] using hv
      | some i =>
          simpa only [prefixVertexIndex] using
            (lt_of_lt_of_le i.isLt hCut)
    have hTargetM : prefixVertexIndex v y < M :=
      lt_of_lt_of_le hTargetN hNM
    change
      finiteNumericHE k N (prefixVertexIndex v x)
          (prefixVertexIndex v y) =
        finiteNumericHE k M (prefixVertexIndex v x)
          (prefixVertexIndex v y)
    simp [finiteNumericHE, hTargetN, hTargetM]

/-- The FULL raw Kpt original of an old physical H+ vertex is the
same sigma-coded L+ type in both finite prefixes. Its level is the
canonical E FREE CUT, not its physical coordinate v. -/
theorem finiteNumericH_prefix_old_rawOriginal_eq
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N M : Nat) (hNM : N ≤ M)
    (v : Nat) (hv : v < N) :
    (finiteNumericH K k N).rawTypeAtFree v =
      (finiteNumericH K k M).rawTypeAtFree v := by
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  let B : EnumeratedPartialStructure db du dd := finiteNumericH K k M
  have hFree : A.freeLevel v = B.freeLevel v :=
    finiteNumericH_prefix_old_freeLevel_eq K k N M hNM v hv
  have hCut : A.freeLevel v ≤ N :=
    (A.freeLevel_le v).trans (Nat.le_of_lt hv)
  have hType :
      A.partialTypeAt (A.freeLevel v) v =
        B.partialTypeAt (A.freeLevel v) v :=
    finiteNumericH_prefix_old_full_Lplus_type_eq
      K k N M hNM (A.freeLevel v) v hCut hv
  change
    (⟨A.freeLevel v, A.partialTypeAt (A.freeLevel v) v⟩ :
      RawPartialTypeNode db du dd) =
    (⟨B.freeLevel v, B.partialTypeAt (B.freeLevel v) v⟩ :
      RawPartialTypeNode db du dd)
  rw [← hFree]
  exact congrArg
    (fun T : PartialTypeWithE (A.freeLevel v) db du dd =>
      (⟨A.freeLevel v, T⟩ : RawPartialTypeNode db du dd)) hType

/-- Genuine forbidden-free Kpt originals of old physical vertices
are LITERALLY equal when N grows: not only their L-reducts or
incoming E columns, but all dependent original type bits.
The two finite avoidance witnesses can differ by proof irrelevance.
-/
theorem finiteNumericH_prefix_old_KptOriginal_eq
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N M : Nat) (hNM : N ≤ M)
    (hAvoidN : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hAvoidM : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k M).L)
    (v : Fin N) :
    (finiteNumericH K k N).kptOriginal family hAvoidN v =
      (finiteNumericH K k M).kptOriginal family hAvoidM
        (Fin.castLE hNM v) := by
  apply Subtype.ext
  change (finiteNumericH K k N).rawTypeAtFree v.val =
    (finiteNumericH K k M).rawTypeAtFree v.val
  exact finiteNumericH_prefix_old_rawOriginal_eq
    K k N M hNM v.val v.isLt

/-- ALL old genuine seed Kpt prefixes, including meet/parameter
nodes already generated at an earlier stage, remain represented
by the SAME physical original addresses when N grows to M.

The enlarged root set is the actual Fin.castLE image of the old
finite H+ root pool. Nothing is inferred about fresh roots. -/
theorem finiteNumericH_prefix_seed_pool_lifts
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N M : Nat) (hNM : N ≤ M)
    (hAvoidN : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hAvoidM : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k M).L)
    (U : Set (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hSeeds :
      X ⊆ ambientPrefixPool family (finiteNumericH K k N)
        hAvoidN U) :
    X ⊆ ambientPrefixPool family (finiteNumericH K k M)
      hAvoidM ((Fin.castLE hNM) '' U) := by
  intro z hz
  obtain ⟨o, ⟨v,hv,rfl⟩,hBelow⟩ := hSeeds hz
  refine ⟨(finiteNumericH K k M).kptOriginal family hAvoidM
      (Fin.castLE hNM v), ?_, ?_⟩
  · exact ⟨Fin.castLE hNM v, ⟨v,hv,rfl⟩, rfl⟩
  · rw [← finiteNumericH_prefix_old_KptOriginal_eq
        family K k N M hNM hAvoidN hAvoidM v]
    exact hBelow

/-- The ACTUAL selected-positive original-name stage pool of a
finite numerical H+ prefix embeds into the enlarged stage pool.
Old positive E-free cuts are preserved exactly.

This is inclusion, NOT equality: new selected physical addresses
in [N,M) can introduce extra genuine parameter originals. -/
theorem finiteNumericH_prefix_stage_pool_lifts
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N M : Nat) (hNM : N ≤ M)
    (U : Set (Fin N)) (I : Set Nat)
    (v : Fin N)
    (hv : v ∈ ambientStagePool (finiteNumericH K k N) U I) :
    Fin.castLE hNM v ∈
      ambientStagePool (finiteNumericH K k M)
        ((Fin.castLE hNM) '' U) I := by
  rcases hv with hU | ⟨hI,hFree⟩
  · exact Or.inl ⟨v,hU,rfl⟩
  · right
    have hEq : (finiteNumericH K k N).freeLevel v.val =
      (finiteNumericH K k M).freeLevel v.val :=
      finiteNumericH_prefix_old_freeLevel_eq
        K k N M hNM v.val v.isLt
    exact ⟨hI,by rw [← hEq]; exact hFree⟩

/-- The ENTIRE actual Kpt meet-and-parameter closure at a fixed
selected set I retains a concrete original-prefix representation
inside the enlarged physical H+ scaffold. This is genuine
closure preservation through increasing numerical carrier sizes.

It does NOT assert that a proposed new resolved-copy root or
its intended complete backward column has been realized. -/
theorem finiteNumericH_prefix_full_closure_pool_lifts
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N M : Nat) (hNM : N ≤ M)
    (hAvoidN : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hAvoidM : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k M).L)
    (U : Set (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hSeeds :
      X ⊆ ambientPrefixPool family (finiteNumericH K k N)
        hAvoidN U)
    (I : Set Nat) :
    SMTree.Envelope.closure (admissibleKptSTree family) I X ⊆
      ambientPrefixPool family (finiteNumericH K k M)
        hAvoidM (ambientStagePool (finiteNumericH K k M)
          ((Fin.castLE hNM) '' U) I) := by
  have hSeedsM :=
    finiteNumericH_prefix_seed_pool_lifts
      family K k N M hNM hAvoidN hAvoidM U X hSeeds
  exact admissibleKpt_stage_closure_subset_pool
    family (finiteNumericH K k M) hAvoidM
    ((Fin.castLE hNM) '' U) I X hSeedsM

#print axioms Kk.finiteNumericH_prefix_old_E_column_eq
#print axioms Kk.finiteNumericH_prefix_old_freeLevel_eq
#print axioms Kk.finiteNumericH_prefix_old_full_Lplus_type_eq
#print axioms Kk.finiteNumericH_prefix_old_rawOriginal_eq
#print axioms Kk.finiteNumericH_prefix_old_KptOriginal_eq
#print axioms Kk.finiteNumericH_prefix_seed_pool_lifts
#print axioms Kk.finiteNumericH_prefix_stage_pool_lifts
#print axioms Kk.finiteNumericH_prefix_full_closure_pool_lifts

end Kk
