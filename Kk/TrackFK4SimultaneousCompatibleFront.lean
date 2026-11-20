import Kk.TrackFK4ExactLevelTransport
import Kk.TrackFPrivateRankZeroDescendants
import Kk.TrackFPrivateMarkerFullRawProfile
import Mathlib.Tactic

/-!
# Track F: genuinely simultaneous K4 target-prefix front and private source markers

English proof and 20 hostile checks committed FIRST in
docs/track_f_simultaneous_k4_private_front_english_audit_20261120.md.

This is the first fully GEOMETRIC finite-tuple construction for Track F:
given individually rank-compatible ACTUAL target coding fibres and
any prescribed common target level L, construct ALL target types at
EXACT L with large corresponding actual source fibres, and all source
types at one common source level M, without allowing two distinct
source coordinates to share a NEW positive-neighbour marker.

The proof uses the already checked K4 singleton exact-level transport
and the already checked two-root zero-pad marker separation. It does
NOT assume an ordering-preserving embedding, a pre-existing target
tuple, diary unavoidability or a global BRD.
-/

namespace Kk.HensonOneType

/-- Simultaneously continue an arbitrary finite family of ACTUAL
rank-compatible K4 source/target fibre pairs to ONE prescribed target
level and ONE common source level, without sharing any fresh source
positive-neighbour marker across distinct labelled coordinates.

The source roots and/or target roots may coincide and have different
initial levels. The only geometric target requirements are a normalized
K4-free target, an injective induced source graph map, and the
individually large ACTUAL source coding-node fibres.

The marker difference is measured relative to each OWN original
source root. In particular the same source root can be repeated.

Not yet claimed: target types distinct, target profile equality,
diary-history persistence or a lower BRD. -/
theorem k4_private_exact_target_common_source_front
    (d L : Nat)
    (Esrc Etgt : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily 4 (by decide) →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (u : Fin d → HensonOneType 4 Esrc)
    (v : Fin d → HensonOneType 4 Etgt)
    (hTargetBelow : ∀ i, (v i).level ≤ L)
    (hRank : ∀ i, rank (v i) = rank (u i))
    (hLarge : ∀ i,
      RankLargeness.Large rank
        (sourceCodingFibre (E := Esrc) Etgt e (v i))
        (rank (u i)) (u i)) :
    ∃ M : Nat,
    ∃ uNew : Fin d → HensonOneType 4 Esrc,
    ∃ vNew : Fin d → HensonOneType 4 Etgt,
      (∀ i : Fin d,
        (uNew i).level = M ∧
        u i ≤ uNew i ∧
        v i ≤ vNew i ∧
        (vNew i).level = L ∧
        rank (uNew i) = rank (u i) ∧
        rank (vNew i) = rank (u i) ∧
        RankLargeness.Large rank
          (sourceCodingFibre (E := Esrc) Etgt e (vNew i))
          (rank (u i)) (uNew i)) ∧
      (∀ i j : Fin d, i ≠ j →
        Disjoint
          ((uNew i).neighbours \ (u i).neighbours)
          ((uNew j).neighbours \ (u j).neighbours)) := by
  classical
  let Source := HensonOneType 4 Esrc
  let Target := HensonOneType 4 Etgt
  have hPartial :
      ∀ Q : Finset (Fin d),
        ∃ G : Fin d → Source,
        ∃ T : Fin d → Target,
          (∀ i ∈ Q,
            u i ≤ G i ∧
            rank (G i) = rank (u i) ∧
            v i ≤ T i ∧
            (T i).level = L ∧
            rank (T i) = rank (u i) ∧
            RankLargeness.Large rank
              (sourceCodingFibre (E := Esrc) Etgt e (T i))
              (rank (u i)) (G i)) ∧
          (∀ i ∈ Q, ∀ j ∈ Q, i ≠ j →
            Disjoint
              ((G i).neighbours \ (u i).neighbours)
              ((G j).neighbours \ (u j).neighbours)) := by
    intro Q
    induction Q using Finset.induction_on with
    | empty =>
        refine ⟨u, v, ?_, ?_⟩
        · intro i hi
          simp at hi
        · intro i hi
          simp at hi
    | @insert i Q hi ih =>
        obtain ⟨G, T, hOldValid, hOldCross⟩ := ih
        let H : Nat :=
          max (u i).level
            ((Q.sup (fun j : Fin d => (G j).level)) + 1)
        have hiH : (u i).level ≤ H := le_max_left _ _
        let z : Source := zeroPad (u i) H hiH
        have huz : u i ≤ z := le_zeroPad (u i) H hiH
        have hzRank : rank z = rank (u i) := rank_zeroPad (u i) H hiH
        have hzLarge : RankLargeness.Large rank
            (sourceCodingFibre (E := Esrc) Etgt e (v i))
            (rank z) z := by
          have hLargeZ := RankLargeness.large_mono_cone
            rank (sourceCodingFibre (E := Esrc) Etgt e (v i))
            (rank (u i)) (u i) z huz (hLarge i)
          simpa only [hzRank] using hLargeZ
        have hzTargetRank : rank (v i) = rank z :=
          (hRank i).trans hzRank.symm
        obtain ⟨t, w, hVt, htLevel, hZw, hwRank,
          htRank, hLargeW⟩ :=
          k4_sourceCodingFibre_continue_equal_rank_exact_level
            Esrc Etgt hAvoid e he hInduced
            (v i) L (hTargetBelow i)
            z hzTargetRank hzLarge
        have hUw : u i ≤ w := le_trans huz hZw
        have hwRootRank : rank w = rank (u i) :=
          hwRank.trans hzRank
        have htRootRank : rank t = rank (u i) :=
          htRank.trans hzRank
        have hLargeRoot : RankLargeness.Large rank
            (sourceCodingFibre (E := Esrc) Etgt e t)
            (rank (u i)) w := by
          simpa only [hzRank] using hLargeW
        have hFreshCross :
            ∀ j ∈ Q,
              Disjoint
                ((G j).neighbours \ (u j).neighbours)
                (w.neighbours \ (u i).neighbours) := by
          intro j hjQ
          have hjH : (G j).level ≤ H := by
            have hjSup : (G j).level ≤
                Q.sup (fun k : Fin d => (G k).level) :=
              Finset.le_sup
                (f := fun k : Fin d => (G k).level) hjQ
            have hSupH :
                Q.sup (fun k : Fin d => (G k).level) + 1 ≤ H :=
              le_max_right _ _
            omega
          exact fresh_markers_disjoint_of_later_zeroPad
            (u j) (G j) (u i) w
            H hjH hiH hZw
        let G' : Fin d → Source :=
          fun j => if j = i then w else G j
        let T' : Fin d → Target :=
          fun j => if j = i then t else T j
        have hG'i : G' i = w := by simp [G']
        have hT'i : T' i = t := by simp [T']
        have hG'old (j : Fin d) (hj : j ∈ Q) :
            G' j = G j := by
          have hji : j ≠ i := by
            intro hji
            exact hi (hji ▸ hj)
          simp [G', hji]
        have hT'old (j : Fin d) (hj : j ∈ Q) :
            T' j = T j := by
          have hji : j ≠ i := by
            intro hji
            exact hi (hji ▸ hj)
          simp [T', hji]
        refine ⟨G', T', ?_, ?_⟩
        · intro j hj
          rcases Finset.mem_insert.mp hj with hji | hjQ
          · subst j
            simpa only [hG'i, hT'i] using
              (show u i ≤ w ∧
                rank w = rank (u i) ∧
                v i ≤ t ∧
                t.level = L ∧
                rank t = rank (u i) ∧
                RankLargeness.Large rank
                  (sourceCodingFibre (E := Esrc) Etgt e t)
                  (rank (u i)) w
                from ⟨hUw, hwRootRank, hVt, htLevel,
                  htRootRank, hLargeRoot⟩)
          · rw [hG'old j hjQ, hT'old j hjQ]
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
  obtain ⟨G, T, hGValid, hGCross⟩ :=
    hPartial (Finset.univ : Finset (Fin d))
  let M : Nat :=
    (Finset.univ : Finset (Fin d)).sup
      (fun i => (G i).level)
  have hBound : ∀ i : Fin d, (G i).level ≤ M := by
    intro i
    exact Finset.le_sup
      (f := fun j : Fin d => (G j).level)
      (Finset.mem_univ i)
  let uNew : Fin d → Source :=
    fun i => zeroPad (G i) M (hBound i)
  let vNew : Fin d → Target := T
  have hValid : ∀ i : Fin d,
      (uNew i).level = M ∧
      u i ≤ uNew i ∧
      v i ≤ vNew i ∧
      (vNew i).level = L ∧
      rank (uNew i) = rank (u i) ∧
      rank (vNew i) = rank (u i) ∧
      RankLargeness.Large rank
        (sourceCodingFibre (E := Esrc) Etgt e (vNew i))
        (rank (u i)) (uNew i) := by
    intro i
    obtain ⟨hUG, hGRank, hVT, hTLevel, hTRank, hGLarge⟩ :=
      hGValid i (Finset.mem_univ i)
    have hGPad : G i ≤ uNew i :=
      le_zeroPad (G i) M (hBound i)
    have hLargePad : RankLargeness.Large rank
        (sourceCodingFibre (E := Esrc) Etgt e (vNew i))
        (rank (u i)) (uNew i) :=
      RankLargeness.large_mono_cone rank
        (sourceCodingFibre (E := Esrc) Etgt e (vNew i))
        (rank (u i))
        (G i) (uNew i) hGPad hGLarge
    exact ⟨rfl, le_trans hUG hGPad, hVT, hTLevel,
      (rank_zeroPad (G i) M (hBound i)).trans hGRank,
      hTRank, hLargePad⟩
  refine ⟨M, uNew, vNew, hValid, ?_⟩
  intro i j hij
  change Disjoint
      ((G i).neighbours \ (u i).neighbours)
      ((G j).neighbours \ (u j).neighbours)
  exact hGCross i (Finset.mem_univ i)
    j (Finset.mem_univ j) hij

end Kk.HensonOneType
