import Kk.TrackFActualCodingFibre
import Kk.TrackFColouredRankLargeFan
import Mathlib.Tactic

/-!
# Track F: finite target-prefix refinement without monotone embeddings

English-first mathematical proof / hostile audit:
docs/track_f_nonroot_prefix_fibre_english_audit.md

For an arbitrary INJECTIVE original-index map e, every fixed finite
target prefix has only finitely many source preimages. This is
formalized as an eventual source-level cutoff; no order-preservation
of the embedding is assumed.

Cone-local recursive largeness monotonicity then permits a selected
finite target-prefix colour to retain largeness after restricting to
actual source originals whose images are beyond that target prefix.

This is a proper conditional component of the pending non-root
source-target compatibility theorem. Target Henson type existence,
target rank equality and multi-sort gluing are not assumed or claimed.
-/

namespace Kk.HensonOneType

variable {ell : Nat} {E : Nat → Nat → Bool}

/-- For any injective enumeration map e, all source originals above
SOME finite index have images beyond the requested target cutoff H.
No monotonicity or lower bound e(x)≥x is assumed. -/
theorem injective_eventually_beyond_target_prefix
    (e : Nat → Nat) (he : Function.Injective e)
    (H : Nat) :
    ∃ M : Nat, ∀ x : Nat, M ≤ x → H ≤ e x := by
  classical
  let pick : Fin H → Nat := fun i =>
    if h : ∃ x : Nat, e x = i.val then Classical.choose h else 0
  let M : Nat := Finset.univ.sup pick + 1
  refine ⟨M, ?_⟩
  intro x hx
  by_contra hBad
  have hSmall : e x < H := by omega
  let i : Fin H := ⟨e x, hSmall⟩
  have hi : ∃ z : Nat, e z = i.val := ⟨x, rfl⟩
  have hPickE : e (pick i) = i.val := by
    simp only [pick, dif_pos hi]
    exact Classical.choose_spec hi
  have hPickX : pick i = x := he hPickE
  have hSup : pick i ≤ Finset.univ.sup pick :=
    Finset.le_sup (f := pick) (Finset.mem_univ i)
  dsimp only [M] at hx
  omega

/-- Enlarging a set ONLY on the source cone above u preserves
recursive rank largeness at u. Global S⊆T is not necessary.

This is needed because the condition e(x.level)≥H holds
eventually on descendants, not on every hypothetical source type. -/
theorem rank_large_cone_local_mono
    (S T : Set (HensonOneType ell E)) :
    ∀ n (u : HensonOneType ell E),
      (∀ x, u ≤ x → x ∈ S → x ∈ T) →
      RankLargeness.Large rank S n u →
      RankLargeness.Large rank T n u := by
  intro n
  induction n with
  | zero =>
      intro u hST hLarge v huv
      obtain ⟨w, hvw, hwS⟩ := hLarge v huv
      exact ⟨w, hvw, hST w (le_trans huv hvw) hwS⟩
  | succ n ih =>
      intro u hST hLarge v huv hv
      obtain ⟨w, hvw, hwrank, hwLarge⟩ :=
        hLarge v huv hv
      refine ⟨w, hvw, hwrank, ?_⟩
      apply ih w
      · intro x hwx hxS
        exact hST x (le_trans huv (le_trans hvw hwx)) hxS
      · exact hwLarge

/-- Conditional non-root target-prefix refinement of a rank-large
source-type fibre. The only additional hypothesis on an arbitrary
source-to-target index map e is INJECTIVITY.

There is a same-rank source refinement w, a single genuine ordered
two-column target prefix j, and an actual source type x in the chosen
colour class, whose image is AFTER target prefix H. Moreover the
whole colour class restricted to such future images remains LARGE.

No target type or target-rank equality is asserted here. -/
theorem rank_large_target_prefix_class
    (S : Set (HensonOneType ell E))
    (Etgt : Nat → Nat → Bool)
    (e : Nat → Nat) (he : Function.Injective e)
    (H : Nat)
    (u : HensonOneType ell E)
    (hLarge : RankLargeness.Large rank S (rank u) u) :
    ∃ j : (Fin H → Bool) × (Fin H → Bool),
    ∃ w x : HensonOneType ell E,
      u ≤ w ∧ rank w = rank u ∧ w ≤ x ∧
      RankLargeness.Large rank
        {t | t ∈ S ∧ targetPrefixColour Etgt e H t = j ∧
          H ≤ e t.level}
        (rank u) w ∧
      x ∈ S ∧ targetPrefixColour Etgt e H x = j ∧
        H ≤ e x.level := by
  classical
  obtain ⟨M, hEventually⟩ :=
    injective_eventually_beyond_target_prefix e he H
  let m : Nat := max u.level M
  let z : HensonOneType ell E :=
    zeroPad u m (le_max_left _ _)
  have huz : u ≤ z := le_zeroPad u m (le_max_left _ _)
  have hzRank : rank z = rank u := rank_zeroPad u m (le_max_left _ _)
  have hzLarge : RankLargeness.Large rank S (rank u) z :=
    RankLargeness.large_mono_cone rank S (rank u) u z huz hLarge
  obtain ⟨j, w, hzw, hwRank, hwLarge⟩ :=
    RankLargeness.large_finite_colour_partition
      rank rank_antitone S (targetPrefixColour Etgt e H)
      (rank u) z hzRank hzLarge
  have hwAboveM : M ≤ w.level := by
    have hM : M ≤ m := le_max_right _ _
    exact hM.trans hzw.1
  have hFutureLarge :
      RankLargeness.Large rank
        {t | t ∈ S ∧ targetPrefixColour Etgt e H t = j ∧
          H ≤ e t.level}
        (rank u) w := by
    apply rank_large_cone_local_mono
      {t : HensonOneType ell E |
        t ∈ S ∧ targetPrefixColour Etgt e H t = j}
      {t : HensonOneType ell E |
        t ∈ S ∧ targetPrefixColour Etgt e H t = j ∧
          H ≤ e t.level} (rank u) w
    · intro t hwt ht
      have hAbove : M ≤ t.level := hwAboveM.trans hwt.1
      exact ⟨ht.1, ht.2, hEventually t.level hAbove⟩
    · exact hwLarge
  obtain ⟨x, hwx, hx⟩ :=
    RankLargeness.large_has_member rank
      {t : HensonOneType ell E |
        t ∈ S ∧ targetPrefixColour Etgt e H t = j ∧
          H ≤ e t.level}
      (rank u) w hwRank hFutureLarge
  exact ⟨j, w, x, le_trans huz hzw, hwRank,
    hwx, hFutureLarge, hx.1, hx.2.1, hx.2.2⟩

/-- Direct application to the exact ACTUAL coding-node fibre
of a previous target type v. This is the finite-colour
combinatorial part of the manuscript's non-root transport lemma;
it does NOT assume that target type ranks already agree. -/
theorem sourceCodingFibre_target_prefix_class
    (Esrc Etgt : Nat → Nat → Bool)
    (e : Nat → Nat) (he : Function.Injective e)
    (v : HensonOneType ell Etgt)
    (H : Nat) (_hOldLevel : v.level ≤ H)
    (u : HensonOneType ell Esrc)
    (hLarge : RankLargeness.Large rank
      (sourceCodingFibre (E := Esrc) Etgt e v)
      (rank u) u) :
    ∃ j : (Fin H → Bool) × (Fin H → Bool),
    ∃ w x : HensonOneType ell Esrc,
      u ≤ w ∧ rank w = rank u ∧ w ≤ x ∧
      RankLargeness.Large rank
        {t | t ∈ sourceCodingFibre (E := Esrc) Etgt e v ∧
          targetPrefixColour Etgt e H t = j ∧ H ≤ e t.level}
        (rank u) w ∧
      x ∈ sourceCodingFibre (E := Esrc) Etgt e v ∧
        targetPrefixColour Etgt e H x = j ∧
          H ≤ e x.level := by
  exact rank_large_target_prefix_class
    (sourceCodingFibre (E := Esrc) Etgt e v)
    Etgt e he H u hLarge

end Kk.HensonOneType
