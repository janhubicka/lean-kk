import Kk.LabelledCopies

/-!
# The precise labelled comparison needed between two Kpt envelopes

The unlabelled minimal embedding type of two finite selected sets is
not enough to identify which source vertex carries each label.
This file supplies the missing *generic* logical bridge:

If two genuine Kpt maps cover the endpoints of their labelled target
representing pairs, and their inverse singleton sets agree for EACH
label and EACH endpoint separately, then one identical labelled
source pair family maps to both target copies.

All inverse sets are literal preimages under genuine monoid maps, not
isomorphism classes. The application-specific task still is to prove
these equalities for two occurrences with the same resolved diary,
including the complete parameter-closed age tests. No Ramsey
theorem or new axiom is introduced.
-/

namespace Kk

open SuccessorTree.V10

universe u

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}
variable {Λ : Type u}

private theorem representingPair_ext
    {P Q : GPlusRepresentingPair family}
    (hLower : P.lower = Q.lower)
    (hUpper : P.upper = Q.upper) : P = Q := by
  cases P with
  | mk l u hp =>
    cases Q with
    | mk l' u' hq =>
      dsimp at hLower hUpper
      cases hLower
      cases hUpper
      rfl

/-- Equality of the labelled endpoint singleton-preimages gives the
same actual source representing pairs for two genuine Kpt envelopes.

The labels and both endpoints remain explicit. This is stronger than
an unlabelled isomorphism of minimal envelope closures, and is the
concrete datum the K_k diary comparison still needs to establish. -/
theorem common_source_pairs_of_equal_labelled_preimages
    (F G : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (P Q : Λ → GPlusRepresentingPair family)
    (hLowerIn : ∀ a, (P a).lower ∈ Set.range F.map)
    (hUpperIn : ∀ a, (P a).upper ∈ Set.range F.map)
    (hLowerInverse : ∀ a,
      F.map ⁻¹' ({(P a).lower} : Set (AdmissibleKptNode family)) =
        G.map ⁻¹' ({(Q a).lower} : Set (AdmissibleKptNode family)))
    (hUpperInverse : ∀ a,
      F.map ⁻¹' ({(P a).upper} : Set (AdmissibleKptNode family)) =
        G.map ⁻¹' ({(Q a).upper} : Set (AdmissibleKptNode family))) :
    ∃ R : Λ → GPlusRepresentingPair family,
      ∀ a, (R a).image F.map = P a ∧
        (R a).image G.map = Q a := by
  classical
  have hLift : ∀ a, ∃ R : GPlusRepresentingPair family,
      R.image F.map = P a := by
    intro a
    exact (P a).lifts_from_shapeMap_range F.map
      (hLowerIn a) (hUpperIn a)
  choose R hR using hLift
  refine ⟨R, ?_⟩
  intro a
  refine ⟨hR a, ?_⟩
  have hFLower : F.map (R a).lower = (P a).lower :=
    congrArg GPlusRepresentingPair.lower (hR a)
  have hFUpper : F.map (R a).upper = (P a).upper :=
    congrArg GPlusRepresentingPair.upper (hR a)
  have hGLower : G.map (R a).lower = (Q a).lower := by
    have hMem : (R a).lower ∈
        F.map ⁻¹' ({(P a).lower} : Set (AdmissibleKptNode family)) := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hFLower
    rw [hLowerInverse a] at hMem
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hMem
  have hGUpper : G.map (R a).upper = (Q a).upper := by
    have hMem : (R a).upper ∈
        F.map ⁻¹' ({(P a).upper} : Set (AdmissibleKptNode family)) := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hFUpper
    rw [hUpperInverse a] at hMem
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hMem
  exact representingPair_ext hGLower hGUpper

/-- The pair-level comparison yields one and the same labelled G+
source copy. Both target copies are then actual induced monoid images
of this source. We explicitly retain injectivity of BOTH target labels;
the common source is deduced using injectivity of the induced action. -/
theorem common_labelled_copy_of_equal_endpoint_preimages
    (F G : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (P Q : Λ → GPlusRepresentingPair family)
    (hPInj : Function.Injective (fun a => (P a).vertex))
    (hQInj : Function.Injective (fun a => (Q a).vertex))
    (hLowerIn : ∀ a, (P a).lower ∈ Set.range F.map)
    (hUpperIn : ∀ a, (P a).upper ∈ Set.range F.map)
    (hLowerInverse : ∀ a,
      F.map ⁻¹' ({(P a).lower} : Set (AdmissibleKptNode family)) =
        G.map ⁻¹' ({(Q a).lower} : Set (AdmissibleKptNode family)))
    (hUpperInverse : ∀ a,
      F.map ⁻¹' ({(P a).upper} : Set (AdmissibleKptNode family)) =
        G.map ⁻¹' ({(Q a).upper} : Set (AdmissibleKptNode family))) :
    ∃ e : LabelledGPlusCopy family Λ,
      LabelledGPlusCopy.map F e =
        (⟨(fun a => (P a).vertex), hPInj⟩ : LabelledGPlusCopy family Λ) ∧
      LabelledGPlusCopy.map G e =
        (⟨(fun a => (Q a).vertex), hQInj⟩ : LabelledGPlusCopy family Λ) := by
  obtain ⟨R, hR⟩ :=
    common_source_pairs_of_equal_labelled_preimages
      F G P Q hLowerIn hUpperIn hLowerInverse hUpperInverse
  have hRInj : Function.Injective (fun a => (R a).vertex) := by
    intro a b hab
    apply hPInj
    have hImage := congrArg (gPlusShapeImage F.map) hab
    rw [← (R a).image_vertex_eq_canonicalShapeImage F.map,
        ← (R b).image_vertex_eq_canonicalShapeImage F.map,
        (hR a).1, (hR b).1] at hImage
    exact hImage
  refine ⟨⟨(fun a => (R a).vertex), hRInj⟩, ?_, ?_⟩
  · apply Subtype.ext
    funext a
    change gPlusShapeImage F.map ((R a).vertex) = (P a).vertex
    rw [← (R a).image_vertex_eq_canonicalShapeImage F.map, (hR a).1]
  · apply Subtype.ext
    funext a
    change gPlusShapeImage G.map ((R a).vertex) = (Q a).vertex
    rw [← (R a).image_vertex_eq_canonicalShapeImage G.map, (hR a).2]

end Kk
