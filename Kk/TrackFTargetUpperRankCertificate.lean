import Kk.TrackFActualCodingFibre
import Kk.FiniteCliqueEmbeddingTransport
import Mathlib.Tactic

/-!
# Track F: source old-clique certificates bound target singleton rank

The English proof / hostile audit was committed first:
docs/track_f_target_upper_rank_certificate_english_audit.md

For an actual source coding node in a target type fibre under
an injective INDUCED graph embedding, images of all source OLD
neighbours are target OLD neighbours, once the finite target
prefix contains the whole finite image of that source set.
The exact finite directed clique-capacity image theorem gives
target rank ≤ source rank.

This is one direction of the manuscript rank equality; the
opposite direction needs an ACTUAL large-fibre clique witness
and is not asserted here. The full BRD lower theorem remains open.
-/

namespace Kk.HensonOneType

/-- A genuine source coding vertex x above old type u is adjacent
to every old source neighbour c∈u.neighbours in the ACTUAL graph.
When its target image has the prefix type v and the target prefix
includes images of all source old neighbours, every such e(c)
belongs to the genuine target old-neighbourhood set.

No order-preservation is assumed for the index map e. -/
theorem old_source_neighbour_images_in_target
    (ell : Nat)
    (Esrc Etgt : Nat → Nat → Bool)
    (e : Nat → Nat)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (u : HensonOneType ell Esrc)
    (v : HensonOneType ell Etgt)
    (hImageBelow : ∀ c ∈ u.neighbours, e c < v.level)
    (x : HensonOneType ell Esrc)
    (hux : u ≤ x)
    (hxFibre : x ∈ sourceCodingFibre (E := Esrc) Etgt e v) :
    u.neighbours.image e ⊆ v.neighbours := by
  classical
  intro z hz
  obtain ⟨c, hcOld, hzc⟩ := Finset.mem_image.mp hz
  have hcLt : c < x.level :=
    lt_of_lt_of_le (u.below c hcOld) hux.1
  have hcNe : c ≠ x.level := by omega
  have hcX : c ∈ x.neighbours :=
    (hux.2 c (u.below c hcOld)).mp hcOld
  have hSourceBit : Esrc c x.level = true := by
    have hCols := hxFibre.1 c hcLt
    simpa [hcX] using hCols.1
  have hTargetBit : Etgt (e c) (e x.level) = true :=
    (hInduced c x.level hcNe).symm.trans hSourceBit
  have hOldTarget := (hxFibre.2.2 (e c)
    (hImageBelow c hcOld)).1
  have hMem : e c ∈ v.neighbours := by
    have hDec : decide (e c ∈ v.neighbours) = true :=
      hOldTarget.symm.trans hTargetBit
    simpa only [decide_eq_true_eq] using hDec
  exact hzc ▸ hMem

/-- Exact target singleton-rank upper bound from an actual coding
witness and the image of the old positive-neighbour clique
certificate. This uses an injected INDUCED graph map.

A singleton target type v can have a *smaller* rank than u;
this theorem does not prove equality. -/
theorem target_rank_le_source_of_old_neighbours
    (ell : Nat)
    (Esrc Etgt : Nat → Nat → Bool)
    (e : Nat → Nat)
    (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (u : HensonOneType ell Esrc)
    (v : HensonOneType ell Etgt)
    (hImageBelow : ∀ c ∈ u.neighbours, e c < v.level)
    (x : HensonOneType ell Esrc)
    (hux : u ≤ x)
    (hxFibre : x ∈ sourceCodingFibre (E := Esrc) Etgt e v) :
    rank v ≤ rank u := by
  have hSub : u.neighbours.image e ⊆ v.neighbours :=
    old_source_neighbour_images_in_target
      ell Esrc Etgt e hInduced u v hImageBelow
      x hux hxFibre
  have hInj : Set.InjOn e ↑u.neighbours := by
    intro a _ b _ hab
    exact he hab
  have hCapacityImage :
      finiteDirectedCliqueCapacity Etgt (u.neighbours.image e) =
        finiteDirectedCliqueCapacity Esrc u.neighbours :=
    finiteDirectedCliqueCapacity_induced_image_eq
      Esrc Etgt u.neighbours e hInj
      (by
        intro a ha b hb hab
        exact hInduced a b hab)
  have hCapMon :
      finiteDirectedCliqueCapacity Etgt
        (u.neighbours.image e) ≤
      finiteDirectedCliqueCapacity Etgt v.neighbours :=
    finiteDirectedCliqueCapacity_mono
      Etgt (u.neighbours.image e) v.neighbours hSub
  unfold rank finiteHensonTypeRank
  omega

/-- Rank largeness of an ACTUAL source coding-node fibre supplies a
genuine coding witness, so the old-clique transport applies.
This gives target rank ≤ source rank without constructing a
new source clique; the reverse inequality remains separate. -/
theorem target_rank_le_source_of_large_fibre
    (ell : Nat)
    (Esrc Etgt : Nat → Nat → Bool)
    (e : Nat → Nat)
    (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (u : HensonOneType ell Esrc)
    (v : HensonOneType ell Etgt)
    (hImageBelow : ∀ c ∈ u.neighbours, e c < v.level)
    (hLarge : RankLargeness.Large rank
      (sourceCodingFibre (E := Esrc) Etgt e v)
      (rank u) u) :
    rank v ≤ rank u := by
  obtain ⟨x, hux, hxFibre⟩ :=
    RankLargeness.large_has_member rank
      (sourceCodingFibre (E := Esrc) Etgt e v)
      (rank u) u rfl hLarge
  exact target_rank_le_source_of_old_neighbours
    ell Esrc Etgt e he hInduced u v
    hImageBelow x hux hxFibre

end Kk.HensonOneType
