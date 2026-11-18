import Kk.TrackFTwoSourceRankLargeFans
import Mathlib.Tactic

/-!
# Track F: private dense rank-zero daughter for each source request

English-first argument and twelve hostile checks:
docs/track_f_private_rankzero_descendants_english_audit.md

An arbitrary recursively rank-large ACTUAL chronological Henson type
admits a rank-zero descendant carrying the SAME coding-node set densely.
First zero-pad the ORIGINAL root beyond any finite bound to ensure all
new positive-neighbour markers lie beyond that bound.

Iterating over ANY finite family of source requests (possibly repeated
original root/fibre pairs, and different original ranks), choose one
rank-zero large daughter for each. Their new positive markers
relative to THEIR OWN original roots are pairwise disjoint.
Finally zero-pad all descendants to a common source level.

This is genuine source type geometry, not the full finite sorted B
realization or target-side graph-age synchronization.
-/

namespace Kk.HensonOneType

variable {ell : Nat} {E : Nat → Nat → Bool}

/-- Recursive rank-largeness descends to a GENUINE rank-zero type
whose fibre remains rank-zero large/dense. The source rank may be
arbitrary. No diary or left-density axiom is required. -/
theorem rank_large_has_rank_zero_descendant
    (S : Set (HensonOneType ell E)) :
    ∀ r (u : HensonOneType ell E),
      rank u = r →
      RankLargeness.Large rank S r u →
      ∃ v : HensonOneType ell E,
        u ≤ v ∧ rank v = 0 ∧
          RankLargeness.Large rank S 0 v := by
  intro r
  induction r with
  | zero =>
      intro u hu hLarge
      exact ⟨u, le_refl _, hu, hLarge⟩
  | succ r ih =>
      intro u hu hLarge
      obtain ⟨w, huw, hwrank, hwLarge⟩ :=
        hLarge u (le_refl _) hu
      obtain ⟨v, hwv, hvRank, hvLarge⟩ :=
        ih w hwrank hwLarge
      exact ⟨v, le_trans huw hwv, hvRank, hvLarge⟩

/-- Descend to rank zero AFTER zero-padding an ORIGINAL source root
to the prescribed height H. Therefore the new positive marker set
relative to the original root has no element below H.

The exact full-prefix order preserves BOTH positive and negative
old bits; arbitrary extensions would not provide this guarantee. -/
theorem rank_large_rank_zero_after_padding
    (S : Set (HensonOneType ell E))
    (u : HensonOneType ell E)
    (hLarge : RankLargeness.Large rank S (rank u) u)
    (H : Nat) (huH : u.level ≤ H) :
    ∃ v : HensonOneType ell E,
      zeroPad u H huH ≤ v ∧
      rank v = 0 ∧ RankLargeness.Large rank S 0 v := by
  have hPad : u ≤ zeroPad u H huH :=
    le_zeroPad u H huH
  have hLargePad :
      RankLargeness.Large rank S (rank u)
        (zeroPad u H huH) :=
    RankLargeness.large_mono_cone rank S (rank u)
      u (zeroPad u H huH) hPad hLarge
  have hPadRank : rank (zeroPad u H huH) = rank u :=
    rank_zeroPad u H huH
  exact rank_large_has_rank_zero_descendant
    S (rank u) (zeroPad u H huH) hPadRank hLargePad

/-- Every finite list of INDEPENDENT rank-large source requests
admits a private rank-zero large descendant, with fresh positive
marker sets disjoint across EVERY PAIR of different request indices.

Distinct requests may have the SAME original root and fibre; they
still acquire disjoint fresh markers because each new request is
chosen only after zero-padding its original root beyond ALL earlier
daughter levels.

The complete all-zero spine calculation is the separately verified
two-source lemma from PR #283. -/
theorem rank_large_private_rank_zero_families
    (d : Nat)
    (root : Fin d → HensonOneType ell E)
    (S : Fin d → Set (HensonOneType ell E))
    (hLarge : ∀ i : Fin d,
      RankLargeness.Large rank (S i)
        (rank (root i)) (root i)) :
    ∃ G : Fin d → HensonOneType ell E,
      (∀ i : Fin d, root i ≤ G i ∧ rank (G i) = 0 ∧
        RankLargeness.Large rank (S i) 0 (G i)) ∧
      (∀ i j : Fin d, i ≠ j →
        Disjoint
          ((G i).neighbours \ (root i).neighbours)
          ((G j).neighbours \ (root j).neighbours)) := by
  classical
  let Node := HensonOneType ell E
  have hPartial :
      ∀ Q : Finset (Fin d),
        ∃ G : Fin d → Node,
          (∀ i ∈ Q, root i ≤ G i ∧ rank (G i) = 0 ∧
            RankLargeness.Large rank (S i) 0 (G i)) ∧
          (∀ i ∈ Q, ∀ j ∈ Q, i ≠ j →
            Disjoint
              ((G i).neighbours \ (root i).neighbours)
              ((G j).neighbours \ (root j).neighbours)) := by
    intro Q
    induction Q using Finset.induction_on with
    | empty =>
        refine ⟨root, ?_, ?_⟩
        · intro i hi
          simp at hi
        · intro i hi
          simp at hi
    | @insert i Q hi ih =>
        obtain ⟨G, hOldValid, hOldCross⟩ := ih
        let H : Nat :=
          max (root i).level
            ((Q.sup (fun j : Fin d => (G j).level)) + 1)
        have hiH : (root i).level ≤ H := le_max_left _ _
        let zi : Node := zeroPad (root i) H hiH
        obtain ⟨w, hzw, hwRank, hwLarge⟩ :=
          rank_large_rank_zero_after_padding
            (S i) (root i) (hLarge i) H hiH
        have hiw : root i ≤ w :=
          le_trans (le_zeroPad (root i) H hiH) hzw
        have hFreshCross :
            ∀ j ∈ Q,
              Disjoint
                ((G j).neighbours \ (root j).neighbours)
                (w.neighbours \ (root i).neighbours) := by
          intro j hjQ
          have hjH : (G j).level ≤ H := by
            have hjSup : (G j).level ≤
                Q.sup (fun t : Fin d => (G t).level) :=
              Finset.le_sup
                (f := fun t : Fin d => (G t).level) hjQ
            have hSupH :
                Q.sup (fun t : Fin d => (G t).level) + 1 ≤ H :=
              le_max_right _ _
            omega
          exact fresh_markers_disjoint_of_later_zeroPad
            (root j) (G j) (root i) w
            H hjH hiH hzw
        let G' : Fin d → Node :=
          fun j => if j = i then w else G j
        have hG'i : G' i = w := by simp [G']
        have hG'old (j : Fin d) (hj : j ∈ Q) :
            G' j = G j := by
          have hji : j ≠ i := by
            intro hji
            exact hi (hji ▸ hj)
          simp [G', hji]
        refine ⟨G', ?_, ?_⟩
        · intro j hj
          rcases Finset.mem_insert.mp hj with hji | hjQ
          · subst j
            simpa only [hG'i] using
              (show root i ≤ w ∧ rank w = 0 ∧
                RankLargeness.Large rank (S i) 0 w
                from ⟨hiw, hwRank, hwLarge⟩)
          · rw [hG'old j hjQ]
            exact hOldValid j hjQ
        · intro j hj k hk hne
          by_cases hji : j = i
          · subst j
            have hki : k ≠ i := by
              intro heq
              exact hne heq.symm
            have hkQ : k ∈ Q := by
              rcases Finset.mem_insert.mp hk with hkI | hkOld
              · exact False.elim (hki hkI)
              · exact hkOld
            rw [hG'i, hG'old k hkQ]
            exact (hFreshCross k hkQ).symm
          · by_cases hki : k = i
            · subst k
              have hjQ : j ∈ Q := by
                rcases Finset.mem_insert.mp hj with hjI | hjOld
                · exact False.elim (hji hjI)
                · exact hjOld
              rw [hG'old j hjQ, hG'i]
              exact hFreshCross j hjQ
            · have hjQ : j ∈ Q := by
                rcases Finset.mem_insert.mp hj with hjI | hjOld
                · exact False.elim (hji hjI)
                · exact hjOld
              have hkQ : k ∈ Q := by
                rcases Finset.mem_insert.mp hk with hkI | hkOld
                · exact False.elim (hki hkI)
                · exact hkOld
              rw [hG'old j hjQ, hG'old k hkQ]
              exact hOldCross j hjQ k hkQ hne
  obtain ⟨G, hValid, hCross⟩ :=
    hPartial (Finset.univ : Finset (Fin d))
  exact ⟨G,
    (by intro i; exact hValid i (Finset.mem_univ i)),
    (by
      intro i j hij
      exact hCross i (Finset.mem_univ i)
        j (Finset.mem_univ j) hij)⟩

/-- All private rank-zero daughters can be padded to ONE common
chronological source level H, without changing old-neighbour sets,
rank-zero density or cross-request fresh-marker disjointness.

This is the exact source geometry interface needed by the
physical raw-age disjoint-marker collapse and the verified
full finite rank-zero graph realization theorem #355. -/
theorem rank_large_private_rank_zero_common_front
    (d : Nat)
    (root : Fin d → HensonOneType ell E)
    (S : Fin d → Set (HensonOneType ell E))
    (hLarge : ∀ i : Fin d,
      RankLargeness.Large rank (S i)
        (rank (root i)) (root i)) :
    ∃ H : Nat, ∃ G : Fin d → HensonOneType ell E,
      (∀ i : Fin d, (G i).level = H ∧
        root i ≤ G i ∧ rank (G i) = 0 ∧
        RankLargeness.Large rank (S i) 0 (G i)) ∧
      (∀ i j : Fin d, i ≠ j →
        Disjoint
          ((G i).neighbours \ (root i).neighbours)
          ((G j).neighbours \ (root j).neighbours)) := by
  classical
  obtain ⟨F, hFValid, hFCross⟩ :=
    rank_large_private_rank_zero_families d root S hLarge
  let H : Nat :=
    (Finset.univ : Finset (Fin d)).sup
      (fun i => (F i).level)
  have hBound : ∀ i : Fin d, (F i).level ≤ H := by
    intro i
    exact Finset.le_sup
      (f := fun j : Fin d => (F j).level)
      (Finset.mem_univ i)
  let G : Fin d → HensonOneType ell E :=
    fun i => zeroPad (F i) H (hBound i)
  have hValid : ∀ i : Fin d, (G i).level = H ∧
      root i ≤ G i ∧ rank (G i) = 0 ∧
      RankLargeness.Large rank (S i) 0 (G i) := by
    intro i
    obtain ⟨hRoot, hRank, hLarge0⟩ := hFValid i
    have hFG : F i ≤ G i :=
      le_zeroPad (F i) H (hBound i)
    have hGLarge : RankLargeness.Large rank (S i) 0 (G i) :=
      RankLargeness.large_mono_cone rank (S i) 0
        (F i) (G i) hFG hLarge0
    exact ⟨rfl, le_trans hRoot hFG,
      (rank_zeroPad (F i) H (hBound i)).trans hRank,
      hGLarge⟩
  refine ⟨H, G, hValid, ?_⟩
  intro i j hij
  change Disjoint
      ((F i).neighbours \ (root i).neighbours)
      ((F j).neighbours \ (root j).neighbours)
  exact hFCross i j hij

end Kk.HensonOneType
