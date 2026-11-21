import Kk.TrackFK4CompleteTupleSynchronization
import Kk.TrackFPrivateMarkerFullRawProfile
import Mathlib.Tactic

/-!
# Track F: genuine survivor resynchronization after one independent code

Audited English proof FIRST:
docs/track_f_zero_code_survivor_resync_english_audit_20261121.md

Given a finite source/target tuple of ACTUAL initially compatible K4
one-types at common source level m, and a selected source original
index r≥m, first ZERO-PAD every survivor source type past r, preserving
its rank and its genuine sourceCodingFibre largeness. Then invoke the
already verified complete K4 tuple synchronization (#410) beyond the
target image e(r). The synchronized target types retain ZERO old-bit
at the actual target original e(r); their future actual coding nodes
therefore remain nonadjacent to the already selected image in BOTH
orientations. Complete canonical sorted finite graph classes of the
original survivor tuple and the new target tuple coincide.

This is a local physical survivor step, NOT the whole pre/post-code
profile sandwich, actual split/cover history, or a BRD theorem.
-/

namespace Kk

/-- A rank-large ACTUAL target coding fibre above a genuine source
type w whose old bit at r is zero forces its target old type t to
have bit zero at e(r), whenever r<w.level and e(r)<t.level.

The proof extracts one genuine source coding vertex extending w,
reads its exact source two-direction zero column at r, transports
the source edge by inducedness, then reads the target prefix column
of that SAME ACTUAL coding vertex. No order preservation of e. -/
theorem trackFActualFibre_target_old_zero_of_source_zero
    (ell : Nat)
    (Esrc Etgt : Nat → Nat → Bool)
    (e : Nat → Nat)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (w : HensonOneType ell Esrc)
    (t : HensonOneType ell Etgt)
    (r : Nat) (hrw : r < w.level)
    (hNoW : r ∉ w.neighbours)
    (hrt : e r < t.level)
    (hLarge : RankLargeness.Large HensonOneType.rank
      (HensonOneType.sourceCodingFibre (E := Esrc) Etgt e t)
      (HensonOneType.rank w) w) :
    e r ∉ t.neighbours := by
  classical
  obtain ⟨x, hwx, hxFibre⟩ :=
    RankLargeness.large_has_member HensonOneType.rank
      (HensonOneType.sourceCodingFibre (E := Esrc) Etgt e t)
      (HensonOneType.rank w) w rfl hLarge
  have hrx : r < x.level := lt_of_lt_of_le hrw hwx.1
  have hNoX : r ∉ x.neighbours := by
    intro hrxMem
    exact hNoW ((hwx.2 r hrw).mpr hrxMem)
  have hSource : Esrc r x.level = false := by
    have hColumn := hxFibre.1 r hrx
    simpa [hNoX] using hColumn.1
  have hTargetColumn :=
    (hxFibre.2.2 (e r) hrt).1
  have hOldBit : decide (e r ∈ t.neighbours) = false := by
    calc
      decide (e r ∈ t.neighbours) =
          Etgt (e r) (e x.level) := hTargetColumn.symm
      _ = Esrc r x.level :=
          (hInduced r x.level (Nat.ne_of_lt hrx)).symm
      _ = false := hSource
  intro hrMem
  have hTrue : decide (e r ∈ t.neighbours) = true := by
    simp [hrMem]
  rw [hOldBit] at hTrue
  cases hTrue

/-- A given coded source original r≥the common old source level m
can be made an isolated ZERO old bit of the entire SURVIVING target
front after an arbitrary prescribed target cutoff.

The original survivors u_i are genuine distinct same-level K4 source
types, initially rank-compatible with actual target coding fibres v_i.
The selected r itself need not belong to any survivor fibre.

The output constructs source and target front types, not just an
abstract hypothetical mixed-age witness:
  * all source types at common M, all target types at common H;
  * every individual rank and large ACTUAL coding fibre preserved;
  * new target types genuinely injective;
  * r is a zero old-neighbour bit of EVERY new source type and e(r)
    is a zero old-neighbour bit of EVERY new TARGET type;
  * literal original-source RAW age equality on ALL nonempty supports;
  * complete original-source/new-target canonical class equality
    uniformly on ALL finite symmetric K4-free sorted graphs.

Neither the immediate pre-code profile at target cut e(r) nor hidden
age-change absence is yet asserted. -/
theorem k4_survivor_sync_after_zero_code
    (d m r cutoff : Nat) (hmR : m ≤ r)
    (Esrc Etgt : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily 4 (by decide) →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (u : Fin d → HensonOneType 4 Esrc)
    (v : Fin d → HensonOneType 4 Etgt)
    (hOldLevel : ∀ i, (u i).level = m)
    (hOldInj : Function.Injective u)
    (hRank : ∀ i, HensonOneType.rank (v i) =
      HensonOneType.rank (u i))
    (hLarge : ∀ i,
      RankLargeness.Large HensonOneType.rank
        (HensonOneType.sourceCodingFibre (E := Esrc) Etgt e (v i))
        (HensonOneType.rank (u i)) (u i)) :
    ∃ H M : Nat,
    ∃ w : Fin d → HensonOneType 4 Esrc,
    ∃ t : Fin d → HensonOneType 4 Etgt,
      cutoff < H ∧ e r < H ∧
      (∀ i : Fin d,
        (w i).level = M ∧
        u i ≤ w i ∧
        HensonOneType.rank (w i) = HensonOneType.rank (u i) ∧
        r < (w i).level ∧ r ∉ (w i).neighbours) ∧
      (∀ i : Fin d,
        v i ≤ t i ∧ (t i).level = H ∧
        HensonOneType.rank (t i) = HensonOneType.rank (u i) ∧
        RankLargeness.Large HensonOneType.rank
          (HensonOneType.sourceCodingFibre (E := Esrc) Etgt e (t i))
          (HensonOneType.rank (w i)) (w i) ∧
        e r ∉ (t i).neighbours) ∧
      Function.Injective t ∧
      (∀ S : Finset (Fin d), S.Nonempty →
        trackFCommonRawAge d 4 m Esrc
          (fun i => (u i).neighbours) S =
        trackFCommonRawAge d 4 M Esrc
          (fun i => (w i).neighbours) S) ∧
      (∀ N : Nat, ∀ B : Nat → Nat → Bool, ∀ σ : Nat → Fin d,
        (∀ i j, B i j = B j i) →
        finitePoolCliqueCheck B 4 (Finset.range N) = false →
        (k4CanonicalSortedFiniteTest d m N Esrc B u σ ↔
         k4CanonicalSortedFiniteTest d H N Etgt B t σ)) := by
  classical
  have huPadLevel : ∀ i : Fin d,
      (u i).level ≤ r + 1 := by
    intro i
    rw [hOldLevel i]
    omega
  let z : Fin d → HensonOneType 4 Esrc :=
    fun i => HensonOneType.zeroPad (u i) (r + 1) (huPadLevel i)
  have hZLevel : ∀ i, (z i).level = r + 1 := by
    intro i
    rfl
  have hUZ : ∀ i, u i ≤ z i := by
    intro i
    exact HensonOneType.le_zeroPad (u i)
      (r + 1) (huPadLevel i)
  have hZRank : ∀ i,
      HensonOneType.rank (z i) = HensonOneType.rank (u i) := by
    intro i
    exact HensonOneType.rank_zeroPad (u i)
      (r + 1) (huPadLevel i)
  have hZLarge : ∀ i,
      RankLargeness.Large HensonOneType.rank
        (HensonOneType.sourceCodingFibre (E := Esrc) Etgt e (v i))
        (HensonOneType.rank (z i)) (z i) := by
    intro i
    have hLargePad := RankLargeness.large_mono_cone
      HensonOneType.rank
      (HensonOneType.sourceCodingFibre (E := Esrc) Etgt e (v i))
      (HensonOneType.rank (u i))
      (u i) (z i) (hUZ i) (hLarge i)
    simpa only [hZRank i] using hLargePad
  have hZInj : Function.Injective z := by
    intro i j hzij
    have hNeigh : (u i).neighbours = (u j).neighbours := by
      have h := congrArg
        (fun q : HensonOneType 4 Esrc => q.neighbours) hzij
      simpa only [z, HensonOneType.zeroPad] using h
    have hRoots : u i = u j :=
      HensonOneType.eq_of_level_neighbours
        (u i) (u j)
        ((hOldLevel i).trans (hOldLevel j).symm)
        hNeigh
    exact hOldInj hRoots
  have hNoZ : ∀ i : Fin d, r ∉ (z i).neighbours := by
    intro i hr
    have hOld : r ∈ (u i).neighbours := by
      simpa only [z, HensonOneType.zeroPad] using hr
    have hLt : r < m := by
      have hLT := (u i).below r hOld
      simpa only [hOldLevel i] using hLT
    omega
  have hPrivateZ : ∀ i j : Fin d, i ≠ j →
      ∀ x : Nat, m ≤ x →
        ¬ (x ∈ (z i).neighbours ∧ x ∈ (z j).neighbours) := by
    intro i j _ x hmx hBoth
    have hxU : x ∈ (u i).neighbours := by
      simpa only [z, HensonOneType.zeroPad] using hBoth.1
    have hxLt : x < m := by
      have hxOld := (u i).below x hxU
      simpa only [hOldLevel i] using hxOld
    omega
  have hRawUZ :
      ∀ S : Finset (Fin d), S.Nonempty →
        trackFCommonRawAge d 4 m Esrc
          (fun i => (u i).neighbours) S =
        trackFCommonRawAge d 4 (r + 1) Esrc
          (fun i => (z i).neighbours) S :=
    trackFCommonRawAge_eq_of_same_rank_private_markers
      d 4 m (r + 1) Esrc u z
      hOldLevel hZLevel hUZ
      (fun i => (hZRank i).symm) hPrivateZ
  let targetCut : Nat :=
    max (cutoff + 1)
      (max (e r + 1)
        ((Finset.range m).sup (fun a => e a) + 1))
  have hCutoffBound : cutoff + 1 ≤ targetCut :=
    le_max_left _ _
  have hrTargetBound : e r + 1 ≤ targetCut :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hOldImageBound :
      (Finset.range m).sup (fun a => e a) + 1 ≤ targetCut :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hZTargetRank : ∀ i,
      HensonOneType.rank (v i) = HensonOneType.rank (z i) := by
    intro i
    exact (hRank i).trans (hZRank i).symm
  obtain ⟨H, M, w, t, hTargetCut, hWValid, hTValid,
    hTargetInj, _hPrivateW, hRawZW, _hCanonicalZW⟩ :=
    k4_sync_complete_tuple_canonical_class
      d (r + 1) targetCut
      Esrc Etgt hAvoid e he hInduced
      z v hZLevel hZInj hZTargetRank hZLarge
  have hCutoff : cutoff < H := by
    omega
  have hrTarget : e r < H := by
    omega
  have hWLevel : ∀ i, (w i).level = M := by
    intro i
    exact (hWValid i).1
  have hZW : ∀ i, z i ≤ w i := by
    intro i
    exact (hWValid i).2.1
  have hUW : ∀ i, u i ≤ w i := by
    intro i
    exact le_trans (hUZ i) (hZW i)
  have hWRank : ∀ i,
      HensonOneType.rank (w i) = HensonOneType.rank (u i) := by
    intro i
    exact (hWValid i).2.2.trans (hZRank i)
  have hRBelowW : ∀ i, r < (w i).level := by
    intro i
    have hzLt : r < (z i).level := by
      rw [hZLevel i]
      omega
    exact lt_of_lt_of_le hzLt (hZW i).1
  have hNoW : ∀ i, r ∉ (w i).neighbours := by
    intro i hrW
    have hzLt : r < (z i).level := by
      rw [hZLevel i]
      omega
    exact (hNoZ i) (((hZW i).2 r hzLt).mpr hrW)
  have hTLevel : ∀ i, (t i).level = H := by
    intro i
    exact (hTValid i).2.1
  have hLargeW : ∀ i,
      RankLargeness.Large HensonOneType.rank
        (HensonOneType.sourceCodingFibre (E := Esrc) Etgt e (t i))
        (HensonOneType.rank (w i)) (w i) := by
    intro i
    exact (hTValid i).2.2.2
  have hNoT : ∀ i, e r ∉ (t i).neighbours := by
    intro i
    have hrT : e r < (t i).level := by
      rw [hTLevel i]
      exact hrTarget
    exact trackFActualFibre_target_old_zero_of_source_zero
      4 Esrc Etgt e hInduced (w i) (t i)
      r (hRBelowW i) (hNoW i) hrT (hLargeW i)
  have hRawUW :
      ∀ S : Finset (Fin d), S.Nonempty →
        trackFCommonRawAge d 4 m Esrc
          (fun i => (u i).neighbours) S =
        trackFCommonRawAge d 4 M Esrc
          (fun i => (w i).neighbours) S := by
    intro S hS
    exact (hRawUZ S hS).trans (hRawZW S hS)
  have hImageOld : ∀ i a,
      a ∈ (u i).neighbours → e a < H := by
    intro i a ha
    have haM : a < m := by
      have hlt := (u i).below a ha
      simpa only [hOldLevel i] using hlt
    have hSup : e a ≤ (Finset.range m).sup (fun x => e x) :=
      Finset.le_sup (f := fun x => e x)
        (Finset.mem_range.mpr haM)
    omega
  have hCanonical :
      ∀ N : Nat, ∀ B : Nat → Nat → Bool, ∀ σ : Nat → Fin d,
        (∀ i j, B i j = B j i) →
        finitePoolCliqueCheck B 4 (Finset.range N) = false →
        (k4CanonicalSortedFiniteTest d m N Esrc B u σ ↔
         k4CanonicalSortedFiniteTest d H N Etgt B t σ) := by
    intro N B σ hSymB hFree
    exact trackFOriginalRefined_source_target_canonical_full_support_iff
      d 4 m M H N (by decide)
      Esrc Etgt B hAvoid e he hInduced
      u w t σ
      hOldLevel hWLevel hTLevel
      hUW hImageOld hLargeW hRawUW hSymB hFree
  refine ⟨H, M, w, t, hCutoff, hrTarget, ?_, ?_,
    hTargetInj, hRawUW, hCanonical⟩
  · intro i
    exact ⟨hWLevel i, hUW i, hWRank i,
      hRBelowW i, hNoW i⟩
  · intro i
    obtain ⟨hTV, hTL, hTR, _⟩ := hTValid i
    exact ⟨hTV, hTL, hTR.trans (hZRank i),
      hLargeW i, hNoT i⟩

end Kk
