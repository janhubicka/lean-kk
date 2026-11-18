import Kk.TrackFMultiSortRawIsolation
import Kk.TrackFActualCodingFibre
import Kk.TrackFTargetUpperRankCertificate
import Kk.FiniteCliqueEmbeddingTransport
import Mathlib.Tactic

/-!
# Track F: actual source old mixed-clique certificates bound target raw ages

English-first proof and ten hostile checks:
docs/track_f_all_support_target_raw_upper_english_audit.md

This formalizes the TARGET-RAW-AGE ≤ SOURCE-RAW-AGE direction
on EVERY NONEMPTY support of an arbitrary finite sorted front,
under an arbitrary injective INDUCED graph embedding e which
need not preserve natural-number order.

Each coordinate's old positive source-neighbour image is first
shown to belong to its target old-neighbour set. The image of
their true common-neighbour clique pool then lies in the
target common pool. Exact finite induced-image clique capacity
and monotonicity yield the raw numerical bound.

No claim of equality of canonical mixed ages, simultaneous
source/target graph richness, or diary/BRD degree is made.
-/

namespace Kk

/-- For any NONEMPTY support S, coordinatewise inclusions
e[U_i] ⊆ V_i imply inclusion of the images of ALL genuine
old common-neighbour vertices into the target common pool.

The support must be nonempty: for S=∅, the common pool is
the whole prefix, which need not map below target level H.
Only the actual target old-neighbour bounds are required. -/
theorem trackFCommonNeighbourPool_image_subset
    (d m H : Nat)
    (e : Nat → Nat)
    (U V : Fin d → Finset Nat)
    (hVBelow : ∀ i x, x ∈ V i → x < H)
    (hImages : ∀ i : Fin d, (U i).image e ⊆ V i)
    (S : Finset (Fin d)) (hS : S.Nonempty) :
    (trackFCommonNeighbourPool d m U S).image e ⊆
      trackFCommonNeighbourPool d H V S := by
  classical
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  have hxPool : x < m ∧ ∀ i ∈ S, x ∈ U i := by
    simpa only [trackFCommonNeighbourPool, Finset.mem_filter,
      Finset.mem_range] using hx
  obtain ⟨i0, hi0⟩ := hS
  have hxImage0 : e x ∈ V i0 :=
    hImages i0 (Finset.mem_image.mpr
      ⟨x, hxPool.2 i0 hi0, rfl⟩)
  have hxTarget : e x < H := hVBelow i0 (e x) hxImage0
  change e x ∈ (Finset.range H).filter
    (fun t => ∀ i ∈ S, t ∈ V i)
  refine Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr hxTarget, ?_⟩
  intro i hi
  exact hImages i (Finset.mem_image.mpr
    ⟨x, hxPool.2 i hi, rfl⟩)

/-- On every NONEMPTY support, an injective INDUCED map
whose source old positive neighbour images are included
in target old neighbourhoods forces the true TARGET
directed-clique RAW age to be NO GREATER than the source
raw age. All finite support sizes, including triples,
are covered; no canonical numerical equality is asserted. -/
theorem trackFCommonRawAge_target_le_source_of_images
    (d ell m H : Nat)
    (Esrc Etgt : Nat → Nat → Bool)
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (U V : Fin d → Finset Nat)
    (hVBelow : ∀ i x, x ∈ V i → x < H)
    (hImages : ∀ i : Fin d, (U i).image e ⊆ V i)
    (S : Finset (Fin d)) (hS : S.Nonempty) :
    trackFCommonRawAge d ell H Etgt V S ≤
      trackFCommonRawAge d ell m Esrc U S := by
  classical
  let P : Finset Nat := trackFCommonNeighbourPool d m U S
  let Q : Finset Nat := trackFCommonNeighbourPool d H V S
  have hPool : P.image e ⊆ Q :=
    trackFCommonNeighbourPool_image_subset
      d m H e U V hVBelow hImages S hS
  have hInj : Set.InjOn e (↑P : Set Nat) := by
    intro a _ b _ hab
    exact he hab
  have hCapImage :
      finiteDirectedCliqueCapacity Etgt (P.image e) =
        finiteDirectedCliqueCapacity Esrc P :=
    finiteDirectedCliqueCapacity_induced_image_eq
      Esrc Etgt P e hInj
      (by intro a _ b _ hab; exact hInduced a b hab)
  have hCapMon :
      finiteDirectedCliqueCapacity Etgt (P.image e) ≤
        finiteDirectedCliqueCapacity Etgt Q :=
    finiteDirectedCliqueCapacity_mono
      Etgt (P.image e) Q hPool
  change ell - 1 - finiteDirectedCliqueCapacity Etgt Q ≤
    ell - 1 - finiteDirectedCliqueCapacity Esrc P
  omega

/-- APPLICATION to ACTUAL source/target Henson types at common
source level m and target level H.

For every source sort i, an ACTUAL rank-large coding-node
fibre of target type v_i supplies a genuine coding witness.
If H exceeds the image of every old source positive neighbour,
the verified old-source-neighbour transport theorem yields
e[U_i]⊆V_i. Thus every NONEMPTY mixed target raw support
age is bounded above by its genuine old source raw age.

No hypothesis that target and source singleton ranks already
match is needed. No source/target enumeration monotonicity,
diary history or simultaneous graph richness is used. -/
theorem trackFCommonRawAge_target_le_source_of_large_fibres
    (d ell m H : Nat)
    (Esrc Etgt : Nat → Nat → Bool)
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (u : Fin d → HensonOneType ell Esrc)
    (v : Fin d → HensonOneType ell Etgt)
    (hULevel : ∀ i, (u i).level = m)
    (hVLevel : ∀ i, (v i).level = H)
    (hImageBelow : ∀ i c, c ∈ (u i).neighbours → e c < H)
    (hLarge : ∀ i,
      RankLargeness.Large HensonOneType.rank
        (HensonOneType.sourceCodingFibre (E := Esrc) Etgt e (v i))
        (HensonOneType.rank (u i)) (u i)) :
    ∀ S : Finset (Fin d), S.Nonempty →
      trackFCommonRawAge d ell H Etgt
        (fun i => (v i).neighbours) S ≤
      trackFCommonRawAge d ell m Esrc
        (fun i => (u i).neighbours) S := by
  classical
  have hVBelow : ∀ i x, x ∈ (v i).neighbours → x < H := by
    intro i x hx
    have hxLt : x < (v i).level := (v i).below x hx
    simpa only [hVLevel i] using hxLt
  have hImages : ∀ i : Fin d,
      ((u i).neighbours).image e ⊆ (v i).neighbours := by
    intro i
    obtain ⟨x, hux, hxFibre⟩ :=
      RankLargeness.large_has_member HensonOneType.rank
        (HensonOneType.sourceCodingFibre (E := Esrc) Etgt e (v i))
        (HensonOneType.rank (u i)) (u i) rfl (hLarge i)
    apply HensonOneType.old_source_neighbour_images_in_target
      ell Esrc Etgt e hInduced (u i) (v i)
      (by
        intro c hc
        simpa only [hVLevel i] using hImageBelow i c hc)
      x hux hxFibre
  intro S hS
  exact trackFCommonRawAge_target_le_source_of_images
    d ell m H Esrc Etgt e he hInduced
    (fun i => (u i).neighbours)
    (fun i => (v i).neighbours)
    hVBelow hImages S hS

end Kk
