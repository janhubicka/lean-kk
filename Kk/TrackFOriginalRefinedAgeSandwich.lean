import Kk.TrackFCanonicalFullSupportBridge
import Mathlib.Tactic

/-!
# Track F: original/refined source-age sandwich under nonmonotone embeddings

English proof and 18 adversarial scope checks committed FIRST:
docs/track_f_original_refined_raw_sandwich_english_audit_20261119.md

The final refined source types provide rank-large ACTUAL target coding fibres.
The ORIGINAL (not refined) source types provide old positive-neighbour
certificates whose images lie below the chosen target prefix H.

This avoids the circular demand that images of every NEW source positive
marker lie below a target cutoff chosen before those markers exist.

A separate exact preservation hypothesis identifies original and refined
source raw support bounds. No simultaneous target-front construction,
full diary persistence, or BRD lower bound is asserted.
-/

namespace Kk

/-- Actual large target coding fibres above REFINED source roots certify
the raw target-upper bound against the ORIGINAL source roots. The only
required image cutoff is for old original positive neighbours.

The refined roots need not have their new positive-neighbour images
below H. This is essential for arbitrary induced embeddings that
do not preserve the chronological enumeration. -/
theorem trackFCommonRawAge_target_le_original_of_refined_fibres
    (d ell m H : Nat)
    (Esrc Etgt : Nat → Nat → Bool)
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (uOld uNew : Fin d → HensonOneType ell Esrc)
    (v : Fin d → HensonOneType ell Etgt)
    (_hOldLevel : ∀ i, (uOld i).level = m)
    (hVLevel : ∀ i, (v i).level = H)
    (hRefine : ∀ i, uOld i ≤ uNew i)
    (hImageBelowOld : ∀ i c, c ∈ (uOld i).neighbours → e c < H)
    (hLargeNew : ∀ i,
      RankLargeness.Large HensonOneType.rank
        (HensonOneType.sourceCodingFibre (E := Esrc)
          Etgt e (v i))
        (HensonOneType.rank (uNew i)) (uNew i)) :
    ∀ S : Finset (Fin d), S.Nonempty →
      trackFCommonRawAge d ell H Etgt
        (fun i => (v i).neighbours) S ≤
      trackFCommonRawAge d ell m Esrc
        (fun i => (uOld i).neighbours) S := by
  classical
  have hVBelow : ∀ i x, x ∈ (v i).neighbours → x < H := by
    intro i x hx
    have hxLt : x < (v i).level := (v i).below x hx
    simpa only [hVLevel i] using hxLt
  have hImages :
      ∀ i : Fin d, ((uOld i).neighbours).image e ⊆
        (v i).neighbours := by
    intro i
    obtain ⟨x, hNewx, hxFibre⟩ :=
      RankLargeness.large_has_member HensonOneType.rank
        (HensonOneType.sourceCodingFibre (E := Esrc)
          Etgt e (v i))
        (HensonOneType.rank (uNew i)) (uNew i)
        rfl (hLargeNew i)
    have hOldx : uOld i ≤ x :=
      le_trans (hRefine i) hNewx
    apply HensonOneType.old_source_neighbour_images_in_target
      ell Esrc Etgt e hInduced (uOld i) (v i)
      (by
        intro c hc
        simpa only [hVLevel i] using hImageBelowOld i c hc)
      x hOldx hxFibre
  intro S hS
  exact trackFCommonRawAge_target_le_source_of_images
    d ell m H Esrc Etgt e he hInduced
    (fun i => (uOld i).neighbours)
    (fun i => (v i).neighbours)
    hVBelow hImages S hS

/-- Finite sorted graph classes agree between ORIGINAL source roots
and TARGET roots, provided that (a) the actual target coding fibres
are rank-large above source REFINEMENTS, (b) old and refined source
raw support bounds agree, and (c) target H exceeds only images of
the ORIGINAL old neighbours.

No cutoff assumption for freshly added positive markers is present.
No original-root largeness is inferred from refined-root largeness. -/
theorem trackFOriginalRefined_source_target_clique_feasibility_iff
    (d ell m M H N : Nat) (hell : 2 ≤ ell)
    (Esrc Etgt B : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (uOld uNew : Fin d → HensonOneType ell Esrc)
    (v : Fin d → HensonOneType ell Etgt)
    (σ : Nat → Fin d)
    (hOldLevel : ∀ i, (uOld i).level = m)
    (hNewLevel : ∀ i, (uNew i).level = M)
    (hVLevel : ∀ i, (v i).level = H)
    (hRefine : ∀ i, uOld i ≤ uNew i)
    (hImageBelowOld : ∀ i c, c ∈ (uOld i).neighbours → e c < H)
    (hLargeNew : ∀ i,
      RankLargeness.Large HensonOneType.rank
        (HensonOneType.sourceCodingFibre (E := Esrc)
          Etgt e (v i))
        (HensonOneType.rank (uNew i)) (uNew i))
    (hRawSame : ∀ S : Finset (Fin d), S.Nonempty →
      trackFCommonRawAge d ell m Esrc
        (fun i => (uOld i).neighbours) S =
      trackFCommonRawAge d ell M Esrc
        (fun i => (uNew i).neighbours) S)
    (hSymB : ∀ i j, B i j = B j i) :
    (∀ C : Finset Nat,
      C ⊆ Finset.range N → C.Nonempty →
      IsDirectedCliqueOn B C →
      C.card ≤ trackFCommonRawAge d ell m Esrc
        (fun i => (uOld i).neighbours) (C.image σ)) ↔
    (∀ C : Finset Nat,
      C ⊆ Finset.range N → C.Nonempty →
      IsDirectedCliqueOn B C →
      C.card ≤ trackFCommonRawAge d ell H Etgt
        (fun i => (v i).neighbours) (C.image σ)) := by
  classical
  have hUpper :=
    trackFCommonRawAge_target_le_original_of_refined_fibres
      d ell m H Esrc Etgt e he hInduced
      uOld uNew v hOldLevel hVLevel hRefine
      hImageBelowOld hLargeNew
  constructor
  · intro hSource
    have hNew :
        ∀ C : Finset Nat,
          C ⊆ Finset.range N → C.Nonempty →
          IsDirectedCliqueOn B C →
          C.card ≤ trackFCommonRawAge d ell M Esrc
            (fun i => (uNew i).neighbours) (C.image σ) := by
      intro C hCSub hCNonempty hClique
      have hImageNonempty : (C.image σ).Nonempty := by
        obtain ⟨x, hx⟩ := hCNonempty
        exact ⟨σ x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
      calc
        C.card ≤ trackFCommonRawAge d ell m Esrc
            (fun i => (uOld i).neighbours) (C.image σ) :=
          hSource C hCSub hCNonempty hClique
        _ = trackFCommonRawAge d ell M Esrc
            (fun i => (uNew i).neighbours) (C.image σ) :=
          hRawSame (C.image σ) hImageNonempty
    exact trackFAllRanks_source_feasible_implies_target_feasible
      d ell M H N hell Esrc Etgt B hAvoid e he hInduced
      uNew v σ hNewLevel hVLevel hLargeNew hSymB hNew
  · intro hTarget C hCSub hCNonempty hClique
    have hImageNonempty : (C.image σ).Nonempty := by
      obtain ⟨x, hx⟩ := hCNonempty
      exact ⟨σ x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
    exact (hTarget C hCSub hCNonempty hClique).trans
      (hUpper (C.image σ) hImageNonempty)

/-- The same original/refined sandwich for the manuscript's COMPLETE
canonical integer-witness graph-age acceptance tests.

The finite abstract graph B is separately required to be K_ell-free
so its clique sort supports belong to the nonempty bounded integer-age
domain. Rank-large ACTUAL source fibres are only assumed above uNew.
No pointwise raw/canonical target-source age equality is asserted. -/
theorem trackFOriginalRefined_source_target_canonical_full_support_iff
    (d ell m M H N : Nat) (hell : 2 ≤ ell)
    (Esrc Etgt B : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (uOld uNew : Fin d → HensonOneType ell Esrc)
    (v : Fin d → HensonOneType ell Etgt)
    (σ : Nat → Fin d)
    (hOldLevel : ∀ i, (uOld i).level = m)
    (hNewLevel : ∀ i, (uNew i).level = M)
    (hVLevel : ∀ i, (v i).level = H)
    (hRefine : ∀ i, uOld i ≤ uNew i)
    (hImageBelowOld : ∀ i c, c ∈ (uOld i).neighbours → e c < H)
    (hLargeNew : ∀ i,
      RankLargeness.Large HensonOneType.rank
        (HensonOneType.sourceCodingFibre (E := Esrc)
          Etgt e (v i))
        (HensonOneType.rank (uNew i)) (uNew i))
    (hRawSame : ∀ S : Finset (Fin d), S.Nonempty →
      trackFCommonRawAge d ell m Esrc
        (fun i => (uOld i).neighbours) S =
      trackFCommonRawAge d ell M Esrc
        (fun i => (uNew i).neighbours) S)
    (hSymB : ∀ i j, B i j = B j i)
    (hBFree : finitePoolCliqueCheck B ell (Finset.range N) = false) :
    (∀ C : Finset Nat,
      C ⊆ Finset.range N →
      IsDirectedCliqueOn B C →
      ∀ T : IntegerGraphSupport d ell,
        (C.filter (fun x => σ x ∈ T.1)).card ≤
          integerGraphAgeCanonical d ell
            (fun Q : IntegerGraphSupport d ell =>
              trackFCommonRawAge d ell m Esrc
                (fun i => (uOld i).neighbours) Q.1) T) ↔
    (∀ C : Finset Nat,
      C ⊆ Finset.range N →
      IsDirectedCliqueOn B C →
      ∀ T : IntegerGraphSupport d ell,
        (C.filter (fun x => σ x ∈ T.1)).card ≤
          integerGraphAgeCanonical d ell
            (fun Q : IntegerGraphSupport d ell =>
              trackFCommonRawAge d ell H Etgt
                (fun i => (v i).neighbours) Q.1) T) := by
  classical
  have hCanonSource :=
    finiteClique_all_constraints_integerCanonical_iff
      B (Finset.range N) σ
      (fun Q : IntegerGraphSupport d ell =>
        trackFCommonRawAge d ell m Esrc
          (fun i => (uOld i).neighbours) Q.1) hBFree
  have hCanonTarget :=
    finiteClique_all_constraints_integerCanonical_iff
      B (Finset.range N) σ
      (fun Q : IntegerGraphSupport d ell =>
        trackFCommonRawAge d ell H Etgt
          (fun i => (v i).neighbours) Q.1) hBFree
  have hExactSource :=
    trackFExactClique_iff_fullRawIntegerSupport
      d ell m N Esrc B (fun i => (uOld i).neighbours) σ hBFree
  have hExactTarget :=
    trackFExactClique_iff_fullRawIntegerSupport
      d ell H N Etgt B (fun i => (v i).neighbours) σ hBFree
  have hExactIff :=
    trackFOriginalRefined_source_target_clique_feasibility_iff
      d ell m M H N hell Esrc Etgt B hAvoid e he hInduced
      uOld uNew v σ hOldLevel hNewLevel hVLevel hRefine
      hImageBelowOld hLargeNew hRawSame hSymB
  exact hCanonSource.trans
    (hExactSource.symm.trans
      (hExactIff.trans
        (hExactTarget.trans hCanonTarget.symm)))

end Kk
