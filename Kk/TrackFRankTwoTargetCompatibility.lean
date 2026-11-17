import Kk.TrackFNonrootRankUpperContinuation
import Kk.TrackFRankThreeActualTriangleRichness
import Kk.TrackFFibreCliqueTargetRank
import Mathlib.Tactic

/-!
# Track F: exact rank-three singleton source/target compatibility

English proof and hostile audit committed first:
docs/track_f_rank_three_target_equality_english_audit.md

Here zero-based Lean rank2 equals manuscript singleton rank3.
Verified rank2-large ACTUAL source coding sets contain a directed
triangle (PR #307). Verified all-size source-fibre clique transport
(PR #310) forces target rank≥2. Verified genuine nonroot target
continuation with old source clique certificates (PR #299)
forces target rank≤2. Thus the same-rank rank2 continuation
is now available under ANY injective INDUCED graph embedding,
with no chronological order preservation assumption.

This is one-source singleton rank compatibility, not full
multi-sort graph-age synchronization or BRD characterization.
-/

namespace Kk.HensonOneType

/-- At ZERO-BASED source rank 2 (manuscript singleton rank THREE),
any ACTUAL rank2-large source-coding fibre admits arbitrary
later genuine target/source type refinements with EXACT
matching singleton rank 2 and still-large coding fibre.

The finite triangle C of source ORIGINAL vertex indices is a
genuine source graph clique. All its original source coding nodes
lie in the SAME selected target fibre; the target image clique
rank bound is the previously verified general theorem.

The embedding e is injective and INDUCED, not assumed to
preserve source or target enumeration order. -/
theorem sourceCodingFibre_continue_equal_rank_two
    (ell : Nat) (hell : 2 ≤ ell)
    (Esrc Etgt : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (v0 : HensonOneType ell Etgt)
    (B : Nat) (u : HensonOneType ell Esrc)
    (hu : rank u = 2)
    (hLarge : RankLargeness.Large rank
      (sourceCodingFibre (E := Esrc) Etgt e v0) 2 u) :
    ∃ vH : HensonOneType ell Etgt,
    ∃ uH : HensonOneType ell Esrc,
      v0 ≤ vH ∧ B ≤ vH.level ∧
      u ≤ uH ∧ rank uH = 2 ∧ rank vH = 2 ∧
      RankLargeness.Large rank
        (sourceCodingFibre (E := Esrc) Etgt e vH) 2 uH := by
  classical
  have hSourceLarge :
      RankLargeness.Large rank
        (sourceCodingFibre (E := Esrc) Etgt e v0)
        (rank u) u := by
    simpa only [hu] using hLarge
  obtain ⟨vH, uH, hVExtend, hCut, hUExtend, hUHRank,
    hNewLarge, hTargetLE⟩ :=
    sourceCodingFibre_extend_target_rank_le
      ell hell Esrc Etgt hAvoid e he hInduced
      v0 B u hSourceLarge
  have hRankUH : rank uH = 2 := hUHRank.trans hu
  have hNewLarge2 :
      RankLargeness.Large rank
        (sourceCodingFibre (E := Esrc) Etgt e vH)
        2 uH := by
    simpa only [hu] using hNewLarge
  have hActual : ∀ z : HensonOneType ell Esrc,
      z ∈ sourceCodingFibre (E := Esrc) Etgt e vH →
        IsCodingNode z := by
    intro z hz
    exact hz.1
  obtain ⟨x, y, z, hxS, hyS, hzS, hxy, hyz,
    hXY, hYX, hXZ, hZX, hYZ, hZY⟩ :=
    rank_two_large_actualCoding_contains_triangle
      (sourceCodingFibre (E := Esrc) Etgt e vH)
      uH hRankUH hNewLarge2 hActual
  let C : Finset Nat := {x.level, y.level, z.level}
  have hXZOrder : x.level < z.level := lt_trans hxy hyz
  have hXYNe : x.level ≠ y.level := Nat.ne_of_lt hxy
  have hXZNe : x.level ≠ z.level := Nat.ne_of_lt hXZOrder
  have hYZNe : y.level ≠ z.level := Nat.ne_of_lt hyz
  have hCcard : C.card = 3 := by
    simp [C, hXYNe, hXZNe, hYZNe, Ne.symm hXYNe,
      Ne.symm hXZNe, Ne.symm hYZNe]
  have hCClique : IsDirectedCliqueOn Esrc C := by
    intro a ha b hb hab
    change a ∈ ({x.level, y.level, z.level} : Finset Nat) at ha
    change b ∈ ({x.level, y.level, z.level} : Finset Nat) at hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with haX | haY | haZ
    · subst a
      rcases hb with hbX | hbY | hbZ
      · exact False.elim (hab hbX.symm)
      · subst b; exact hXY
      · subst b; exact hXZ
    · subst a
      rcases hb with hbX | hbY | hbZ
      · subst b; exact hYX
      · exact False.elim (hab hbY.symm)
      · subst b; exact hYZ
    · subst a
      rcases hb with hbX | hbY | hbZ
      · subst b; exact hZX
      · subst b; exact hZY
      · exact False.elim (hab hbZ.symm)
  have hCFibre : ∀ c ∈ C,
      ∃ t : HensonOneType ell Esrc,
        t.level = c ∧
        t ∈ sourceCodingFibre (E := Esrc) Etgt e vH := by
    intro c hc
    change c ∈ ({x.level, y.level, z.level} : Finset Nat) at hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with hcX | hcY | hcZ
    · exact ⟨x, hcX.symm, hxS⟩
    · exact ⟨y, hcY.symm, hyS⟩
    · exact ⟨z, hcZ.symm, hzS⟩
  have hTargetGE : 2 ≤ rank vH :=
    target_rank_ge_of_fibre_clique
      ell hell Esrc Etgt hAvoid e he hInduced
      vH C hCClique hCFibre 2 (by rw [hCcard])
  have hTargetEQ : rank vH = 2 := by
    have hUpper : rank vH ≤ 2 := by
      rw [← hu]
      exact hTargetLE
    omega
  exact ⟨vH, uH, hVExtend, hCut, hUExtend,
    hRankUH, hTargetEQ, hNewLarge2⟩

end Kk.HensonOneType
