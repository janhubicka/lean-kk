import Kk.TrackFTargetRankClique
import Kk.TrackFActualCodingFibre
import Mathlib.Tactic

/-!
# Track F: source-fibre clique certificates bound actual target rank

English proof and hostile audit were committed before Lean:
docs/track_f_fibre_clique_rank_lower_english_audit.md

No diary theorem or assumption that rank-largeness automatically
implies clique richness is used. The exact premise is an ACTUAL
directed source clique of original vertices, with one genuine
source coding-node fibre witness for each selected original.

Its image under an injective INDUCED graph embedding is a complete
future target clique, joined in both directions to the target
old-neighbourhood, so the verified physical target-rank bound
applies. The final corollary converts manuscript rank (one-based)
to Lean zero-based singleton rank.
-/

namespace Kk.HensonOneType

/-- Every actual SOURCE clique of originals contained in one
target coding fibre maps to a true future target clique
joined to the target type's complete positive old neighbourhood.

The coding-fibre membership is supplied as a source witness
at each original index; it is NOT a hypothesis that every
hypothetical source one-type is physically realized. -/
theorem fibre_clique_card_le_target_manuscript_rank
    (ell : Nat) (hell : 2 ≤ ell)
    (Esrc Etgt : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (v : HensonOneType ell Etgt)
    (C : Finset Nat)
    (hClique : IsDirectedCliqueOn Esrc C)
    (hFibre : ∀ c ∈ C, ∃ t : HensonOneType ell Esrc,
      t.level = c ∧
      t ∈ sourceCodingFibre (E := Esrc) Etgt e v) :
    C.card ≤ finiteHensonTypeRank ell Etgt v.neighbours := by
  classical
  let W : Finset Nat := C.image e
  have hInj : Set.InjOn e ↑C := by
    intro a _ b _ hab
    exact he hab
  have hCard : W.card = C.card :=
    Finset.card_image_iff.mpr hInj
  have hFuture : ∀ w ∈ W, v.level ≤ w := by
    intro w hw
    obtain ⟨c, hc, hcw⟩ := Finset.mem_image.mp hw
    obtain ⟨t, ht, htFibre⟩ := hFibre c hc
    have htFuture : v.level ≤ e t.level := htFibre.2.1
    simpa [W, ht, hcw] using htFuture
  have hTargetClique : IsDirectedCliqueOn Etgt W := by
    intro w hw z hz hwz
    obtain ⟨a, ha, haw⟩ := Finset.mem_image.mp hw
    obtain ⟨b, hb, hbz⟩ := Finset.mem_image.mp hz
    have hab : a ≠ b := by
      intro heq
      subst b
      exact hwz (haw.symm.trans hbz)
    have hSource : Esrc a b = true :=
      hClique a ha b hb hab
    have hTarget : Etgt (e a) (e b) = true :=
      (hInduced a b hab).symm.trans hSource
    simpa [W,haw,hbz] using hTarget
  have hJoin : ∀ p ∈ v.neighbours, ∀ w ∈ W,
      Etgt p w = true ∧ Etgt w p = true := by
    intro p hp w hw
    obtain ⟨c, hc, hcw⟩ := Finset.mem_image.mp hw
    obtain ⟨t, ht, htFibre⟩ := hFibre c hc
    have hpBound : p < v.level := v.below p hp
    have hCols := htFibre.2.2 p hpBound
    have hJoinT :
        Etgt p (e t.level) = true ∧
        Etgt (e t.level) p = true := by
      simpa [hp] using hCols
    simpa [ht,hcw] using hJoinT
  have hTargetRank :
      W.card ≤ finiteHensonTypeRank ell Etgt v.neighbours :=
    henson_targetRank_ge_futureClique
      ell v.level hell Etgt hAvoid
      v.neighbours W v.below hFuture hTargetClique hJoin
  simpa only [hCard] using hTargetRank

/-- If one actual target fibre contains a directed source clique
of size at least n+1, then its actual zero-based singleton
Henson rank is at least n. This is an implication with an
EXPLICIT clique witness, not an assertion that rank-largeness
alone provides that witness. -/
theorem target_rank_ge_of_fibre_clique
    (ell : Nat) (hell : 2 ≤ ell)
    (Esrc Etgt : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (v : HensonOneType ell Etgt)
    (C : Finset Nat)
    (hClique : IsDirectedCliqueOn Esrc C)
    (hFibre : ∀ c ∈ C, ∃ t : HensonOneType ell Esrc,
      t.level = c ∧
      t ∈ sourceCodingFibre (E := Esrc) Etgt e v)
    (n : Nat) (hn : n + 1 ≤ C.card) :
    n ≤ rank v := by
  have hLower :
      C.card ≤ finiteHensonTypeRank ell Etgt v.neighbours :=
    fibre_clique_card_le_target_manuscript_rank
      ell hell Esrc Etgt hAvoid e he hInduced
      v C hClique hFibre
  unfold rank
  omega

end Kk.HensonOneType
