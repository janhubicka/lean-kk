import Kk.TrackFNonrootRankUpperContinuation
import Kk.TrackFRankTwoActualEdgeRichness
import Kk.TrackFTargetRankClique
import Mathlib.Tactic

/-!
# Track F: exact non-root rank-one source/target compatibility

English proof and hostile audit committed BEFORE Lean:
docs/track_f_rank_one_target_equality_english_audit.md

Lean rank 1 means manuscript singleton rank 2. The now-verified
rank-one-large ACTUAL coding fibre edge-richness theorem constructs
a genuine source edge, whose induced image lies beyond a selected
target prefix and is joined to ALL of that target type's old
neighbours. The verified target future-clique rank bound supplies
target rank >=1. The verified nonroot continuation/certificate
composition supplies target rank <=source rank=1.

This proves the complete SAME-RANK TARGET-PREFIX CONTINUATION at
manuscript singleton rank TWO, but NOT rank drop, triangle
richness at manuscript rank 3, multi-sort synchronization,
or any global diary/BRD theorem.
-/

namespace Kk.HensonOneType

/-- Every manuscript-rank-two compatible pair has a later
genuine target type and a same-rank source refinement with
EXACT matching singleton rank one (zero-based), and a
still-large ACTUAL source coding-node fibre.

The only map premise is an INJECTIVE INDUCED graph embedding.
It need not preserve chronological enumeration order. -/
theorem sourceCodingFibre_continue_equal_rank_one
    (ell : Nat) (hell : 2 ≤ ell)
    (Esrc Etgt : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (v0 : HensonOneType ell Etgt)
    (B : Nat) (u : HensonOneType ell Esrc)
    (hu : rank u = 1)
    (hLarge : RankLargeness.Large rank
      (sourceCodingFibre (E := Esrc) Etgt e v0) 1 u) :
    ∃ vH : HensonOneType ell Etgt,
    ∃ uH : HensonOneType ell Esrc,
      v0 ≤ vH ∧ B ≤ vH.level ∧
      u ≤ uH ∧ rank uH = 1 ∧ rank vH = 1 ∧
      RankLargeness.Large rank
        (sourceCodingFibre (E := Esrc) Etgt e vH) 1 uH := by
  classical
  have hSourceLarge :
      RankLargeness.Large rank
        (sourceCodingFibre (E := Esrc) Etgt e v0)
        (rank u) u := by
    simpa only [hu] using hLarge
  obtain ⟨vH, uH, hVExtend, hB, hUExtend, hUHRank,
    hFibreLarge, hTargetLE⟩ :=
    sourceCodingFibre_extend_target_rank_le
      ell hell Esrc Etgt hAvoid e he hInduced
      v0 B u hSourceLarge
  have huH : rank uH = 1 := hUHRank.trans hu
  have hSOne :
      RankLargeness.Large rank
        (sourceCodingFibre (E := Esrc) Etgt e vH)
        1 uH := by
    simpa only [hu] using hFibreLarge
  have hActual : ∀ z : HensonOneType ell Esrc,
      z ∈ sourceCodingFibre (E := Esrc) Etgt e vH →
        IsCodingNode z := by
    intro z hz
    exact hz.1
  obtain ⟨x, y, hxS, hyS, hxy, hEsrcXY, hEsrcYX⟩ :=
    rank_one_large_actualCoding_contains_edge
      (sourceCodingFibre (E := Esrc) Etgt e vH)
      uH huH hSOne hActual
  have hXYNe : x.level ≠ y.level := Nat.ne_of_lt hxy
  have hImageNe : e x.level ≠ e y.level := by
    intro h
    exact hXYNe (he h)
  have hTargetXY : Etgt (e x.level) (e y.level) = true :=
    (hInduced x.level y.level hXYNe).symm.trans hEsrcXY
  have hTargetYX : Etgt (e y.level) (e x.level) = true :=
    (hInduced y.level x.level hXYNe.symm).symm.trans hEsrcYX
  let W : Finset Nat := {e x.level, e y.level}
  have hWCard : W.card = 2 := by
    simp [W, hImageNe]
  have hWFuture : ∀ z ∈ W, vH.level ≤ z := by
    intro z hz
    change z ∈ ({e x.level, e y.level} : Finset Nat) at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hzX | hzY
    · subst z
      exact hxS.2.1
    · subst z
      exact hyS.2.1
  have hWClique : IsDirectedCliqueOn Etgt W := by
    intro a ha b hb hab
    change a ∈ ({e x.level, e y.level} : Finset Nat) at ha
    change b ∈ ({e x.level, e y.level} : Finset Nat) at hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with haX | haY
    · subst a
      rcases hb with hbX | hbY
      · exact False.elim (hab hbX.symm)
      · subst b
        exact hTargetXY
    · subst a
      rcases hb with hbX | hbY
      · subst b
        exact hTargetYX
      · exact False.elim (hab hbY.symm)
  have hJoin : ∀ p ∈ vH.neighbours, ∀ z ∈ W,
      Etgt p z = true ∧ Etgt z p = true := by
    intro p hp z hz
    have hpOld : p < vH.level := vH.below p hp
    change z ∈ ({e x.level, e y.level} : Finset Nat) at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hzX | hzY
    · subst z
      have hCols := hxS.2.2 p hpOld
      simpa [hp] using hCols
    · subst z
      have hCols := hyS.2.2 p hpOld
      simpa [hp] using hCols
  have hRankLowerRaw :
      W.card ≤ finiteHensonTypeRank ell Etgt vH.neighbours :=
    henson_targetRank_ge_futureClique
      ell vH.level hell Etgt hAvoid
      vH.neighbours W vH.below hWFuture hWClique hJoin
  have hTargetSafe :
      finiteDirectedCliqueCapacity Etgt vH.neighbours < ell - 1 :=
    (finitePoolCliqueCheck_false_iff_capacity_lt
      Etgt (ell - 1) vH.neighbours).mp vH.safe
  have hTargetGE : 1 ≤ rank vH := by
    dsimp [rank, finiteHensonTypeRank]
    rw [hWCard] at hRankLowerRaw
    omega
  have hTargetEQ : rank vH = 1 := by
    have hTargetUpper : rank vH ≤ 1 := by
      rw [← hu]
      exact hTargetLE
    omega
  refine ⟨vH, uH, hVExtend, hB,
    hUExtend, huH, hTargetEQ, ?_⟩
  exact hSOne

end Kk.HensonOneType
