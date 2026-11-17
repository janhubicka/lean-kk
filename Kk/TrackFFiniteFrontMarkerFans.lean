import Kk.TrackFLabelledHistoryFan
import Mathlib.Tactic

/-!
# Track F: arbitrary finite-front rank-large daughter fans

The English proof and hostile audit were committed BEFORE Lean:
docs/track_f_finite_front_fans_english_audit.md

Each sort i : Fin d has its OWN actual finite Henson source root,
possibly different zero-based rank, its OWN recursively rank-large
set S_i of future coding type nodes, and an arbitrary target number
k_i of rank-lowered daughter cones.

We induct over the FINITE set of source sort labels. At each step,
the complete previously chosen history is retained as a Finset of
PAIRS (old daughter node, old source root). This prevents losing
fresh-marker obligations when different source sorts choose the
same finite type with distinct roots.

The verified labelled finite-history fan theorem gives new daughters
whose fresh positive-neighbour marker sets are disjoint from EVERY
previous pair; the new fan itself has pairwise incompatible cones
and internally disjoint fresh markers.

This is the finite-front SOURCE marker-scheduling theorem. It does
not realize prescribed old-to-future edges in the selected ACTUAL
coding originals, synchronize source/target finite graph ages, or
prove diary/BRD exactness.
-/

namespace Kk.HensonOneType

variable {ell : Nat} {E : Nat → Nat → Bool}

/-- A concrete request for a rank-lowered daughter fan over one
independently specified source sort. Different sorts may have
different roots, ranks, large sets and target cardinalities. -/
structure FiniteFanRequest (ell : Nat) (E : Nat → Nat → Bool) where
  root : HensonOneType ell E
  lowerRank : Nat
  fibre : Set (HensonOneType ell E)
  rootRank : rank root = lowerRank + 1
  fibreLarge : RankLargeness.Large rank fibre (lowerRank + 1) root
  count : Nat

/-- Exact per-sort fan validity: cardinality, lower-rank largeness
and pairwise incompatible cones with disjoint fresh markers
relative to THIS sort's source root. -/
def FiniteFanValid
    (req : FiniteFanRequest ell E)
    (F : Finset (HensonOneType ell E)) : Prop :=
  F.card = req.count ∧
  (∀ g ∈ F, req.root ≤ g ∧ rank g = req.lowerRank ∧
    RankLargeness.Large rank req.fibre req.lowerRank g) ∧
  (∀ g ∈ F, ∀ h ∈ F, g ≠ h →
    (¬ ∃ t : HensonOneType ell E, g ≤ t ∧ h ≤ t) ∧
    Disjoint (g.neighbours \ req.root.neighbours)
      (h.neighbours \ req.root.neighbours))

/-- For an ARBITRARY finite front of ACTUAL Henson source
one-types, choose all requested lower-rank S_i-large daughter
families simultaneously, with fresh positive-neighbour markers
disjoint for EVERY PAIR of distinct source sort indices.

No equal-rank or same-root assumption occurs anywhere.
The source sort labels are retained in the induction's finite
history, so different roots attached to the same selected
daughter type do NOT get silently identified.

This is source marker disjointness, not the complete mixed
graph-age or target/source compatible fibre synchronization. -/
theorem rank_large_finite_front_marker_fans
    (d : Nat)
    (req : Fin d → FiniteFanRequest ell E) :
    ∃ G : Fin d → Finset (HensonOneType ell E),
      (∀ i : Fin d, FiniteFanValid (req i) (G i)) ∧
      (∀ i j : Fin d, i ≠ j →
        ∀ g ∈ G i, ∀ h ∈ G j,
          Disjoint
            (g.neighbours \ (req i).root.neighbours)
            (h.neighbours \ (req j).root.neighbours)) := by
  classical
  let Node := HensonOneType ell E
  have hPartial :
      ∀ Q : Finset (Fin d),
        ∃ G : Fin d → Finset Node,
          (∀ i ∈ Q, FiniteFanValid (req i) (G i)) ∧
          (∀ i ∈ Q, ∀ j ∈ Q, i ≠ j →
            ∀ g ∈ G i, ∀ h ∈ G j,
              Disjoint
                (g.neighbours \ (req i).root.neighbours)
                (h.neighbours \ (req j).root.neighbours)) := by
    intro Q
    induction Q using Finset.induction_on with
    | empty =>
        refine ⟨fun _ => ∅, ?_, ?_⟩
        · intro i hi
          exact False.elim (Finset.not_mem_empty i hi)
        · intro i hi
          exact False.elim (Finset.not_mem_empty i hi)
    | @insert i Q hi ih =>
        obtain ⟨G, hValidOld, hCrossOld⟩ := ih
        let old : Finset (Node × Node) :=
          Q.biUnion (fun j =>
            (G j).image (fun g => (g, (req j).root)))
        have hOldPair (j : Fin d) (hj : j ∈ Q)
            (g : Node) (hg : g ∈ G j) :
            (g, (req j).root) ∈ old := by
          change (g, (req j).root) ∈
            Q.biUnion (fun k =>
              (G k).image (fun t => (t, (req k).root)))
          exact Finset.mem_biUnion.mpr
            ⟨j, hj, Finset.mem_image.mpr ⟨g, hg, rfl⟩⟩
        obtain ⟨F, hFCard, hFMembers, hFSep, hFCross⟩ :=
          rank_large_new_fan_after_labelled_history
            (req i).fibre (req i).lowerRank
            (req i).root (req i).rootRank
            (req i).fibreLarge old (req i).count
        have hValidNew : FiniteFanValid (req i) F :=
          ⟨hFCard, hFMembers, hFSep⟩
        let G' : Fin d → Finset Node :=
          fun j => if j = i then F else G j
        have hG'i : G' i = F := by
          simp [G']
        have hG'old (j : Fin d) (hj : j ∈ Q) :
            G' j = G j := by
          have hji : j ≠ i := by
            intro h
            exact hi (h ▸ hj)
          simp [G', hji]
        refine ⟨G', ?_, ?_⟩
        · intro j hj
          rcases Finset.mem_insert.mp hj with hji | hjQ
          · subst j
            simpa only [hG'i] using hValidNew
          · rw [hG'old j hjQ]
            exact hValidOld j hjQ
        · intro j hj k hk hne g hg h hH
          by_cases hji : j = i
          · subst j
            have hki : k ≠ i := by
              intro hki
              exact hne hki.symm
            have hkQ : k ∈ Q := by
              rcases Finset.mem_insert.mp hk with hEq | hQ
              · exact False.elim (hki hEq)
              · exact hQ
            have hgF : g ∈ F := by
              simpa only [hG'i] using hg
            have hhOld : h ∈ G k := by
              simpa only [hG'old k hkQ] using hH
            have hOldCross := hFCross
              (h, (req k).root) (hOldPair k hkQ h hhOld)
              g hgF
            exact hOldCross.symm
          · by_cases hki : k = i
            · subst k
              have hjQ : j ∈ Q := by
                rcases Finset.mem_insert.mp hj with hEq | hQ
                · exact False.elim (hji hEq)
                · exact hQ
              have hgOld : g ∈ G j := by
                simpa only [hG'old j hjQ] using hg
              have hhF : h ∈ F := by
                simpa only [hG'i] using hH
              exact hFCross
                (g, (req j).root) (hOldPair j hjQ g hgOld)
                h hhF
            · have hjQ : j ∈ Q := by
                rcases Finset.mem_insert.mp hj with hEq | hQ
                · exact False.elim (hji hEq)
                · exact hQ
              have hkQ : k ∈ Q := by
                rcases Finset.mem_insert.mp hk with hEq | hQ
                · exact False.elim (hki hEq)
                · exact hQ
              have hgOld : g ∈ G j := by
                simpa only [hG'old j hjQ] using hg
              have hhOld : h ∈ G k := by
                simpa only [hG'old k hkQ] using hH
              exact hCrossOld j hjQ k hkQ hne
                g hgOld h hhOld
  obtain ⟨G, hValid, hCross⟩ :=
    hPartial (Finset.univ : Finset (Fin d))
  exact ⟨G,
    (by intro i; exact hValid i (Finset.mem_univ i)),
    (by
      intro i j hij g hg h hh
      exact hCross i (Finset.mem_univ i)
        j (Finset.mem_univ j) hij g hg h hh)⟩

end Kk.HensonOneType
