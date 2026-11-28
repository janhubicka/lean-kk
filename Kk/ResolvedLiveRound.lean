import Kk.ResolvedLiveRefinement
import Mathlib.Tactic

/-!
# Actual normalized coding rounds
English proof: docs/resolved_fair_rounds_english_20261126.md.
The coding vertex is first isolated, then its adjacency is made
constant on each class. Saturated cover normalization acts on these
actual occupied classes. All old and live edges are preserved.
-/

namespace Kk

/-- The complete class partition persists through normalization:
every new column is constant on classes, while old columns persist. -/
theorem resolvedClassExact_of_live_extension {d ell : Nat}
    {W : Set Nat} {sort : Nat → Fin d}
    (s t : ResolvedLiveStage d ell W sort)
    (hExact : ResolvedClassExact s.edge s.old W sort)
    (hOld : s.old ⊆ t.old)
    (hKeep : ∀ x y : Nat, (x ∈ s.old ∨ x ∈ W) →
      (y ∈ s.old ∨ y ∈ W) → t.edge x y = s.edge x y) :
    ResolvedClassExact t.edge t.old W sort := by
  intro v hv w hw
  constructor
  · intro h p hp
    calc
      t.edge p v = t.column p (sort v) := (t.columns p hp v hv).1
      _ = t.column p (sort w) := congrArg (t.column p) h
      _ = t.edge p w := (t.columns p hp w hw).1.symm
  · intro h
    apply (hExact v hv w hw).2
    intro p hp
    calc
      s.edge p v = t.edge p v := (hKeep p v (Or.inl hp) (Or.inr hv)).symm
      _ = t.edge p w := h p (hOld hp)
      _ = s.edge p w := hKeep p w (Or.inl hp) (Or.inr hw)

/-- Coding after actual saturation preserves the full fixed-terminal
canonical age. Target labels may repeat classes. A clique witnessing
each old support capacity is assigned actual target labels in that
support, and remains a literal continuation after coding. -/
theorem ResolvedLiveStage.saturatedCode_target_neutral {d ell n : Nat}
    {W : Set Nat} {sort : Nat → Fin d}
    (s : ResolvedLiveStage d ell W sort)
    (r : Nat) (hr : r ∈ W) (hell : 0 < ell)
    (hSingleton : ∀ v ∈ W, sort v = sort r → v = r)
    (hConst : ∀ v ∈ W, ∀ w ∈ W, sort v = sort w → s.edge r v = s.edge r w)
    (hSat : s.oldAge = s.futureAge)
    (target : Fin n → Nat) (hTarget : ∀ i, target i ∈ W ∧ target i ≠ r) :
    resolvedTargetAge s.edge ell (insert r s.old) target =
      resolvedTargetAge s.edge ell s.old target := by
  classical
  let c : Nat → Fin n → Bool := fun p i => s.edge p (target i)
  have hLe := resolvedOldCanonical_antitone (ell := ell)
    s.edge s.old (insert r s.old) (by intro p hp; exact Finset.mem_insert_of_mem hp) c
  funext U
  apply Nat.le_antisymm (hLe U)
  let pi : Fin n → Fin d := fun i => sort (target i)
  obtain ⟨C, hSmall, hMem, hClique, hCard⟩ :=
    resolvedActualAge_attained_supported s.edge W sort hell (integerGraphSupportImage pi U)
  have hBefore : resolvedTargetAge s.edge ell s.old target U = C.card := by
    calc
      _ = s.oldAge (integerGraphSupportImage pi U) :=
        s.targetAge_pullback target (fun i => (hTarget i).1) hell U
      _ = s.futureAge (integerGraphSupportImage pi U) := congrFun hSat _
      _ = C.card := hCard.symm
  have hRep : ∀ x ∈ C, ∃ i ∈ U.1, sort x = sort (target i) := by
    intro x hx
    have hm := (hMem x hx).2
    change sort x ∈ U.1.image pi at hm
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hm
    exact ⟨i,hi,he.symm⟩
  obtain ⟨i0,hi0⟩ := U.2.1
  let label : Nat → Fin n := fun x =>
    if hx : x ∈ C then Classical.choose (hRep x hx) else i0
  have hLabel : ∀ x ∈ C, label x ∈ U.1 ∧ sort x = sort (target (label x)) := by
    intro x hx
    simpa only [label, dif_pos hx] using Classical.choose_spec (hRep x hx)
  have hrNot : r ∉ C := by
    intro hx
    have hSame := (hLabel r hx).2
    exact (hTarget (label r)).2
      (hSingleton _ (hTarget (label r)).1 hSame.symm)
  have hDisj : Disjoint (insert r s.old) C := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    rcases Finset.mem_insert.mp hx with he | hx
    · subst x
      exact hrNot hy
    · exact s.separated x hx (hMem x hy).1
  have hCols : ∀ p ∈ insert r s.old, ∀ x ∈ C,
      s.edge p x = c p (label x) ∧ s.edge x p = c p (label x) := by
    intro p hp x hx
    have hSame := (hLabel x hx).2
    have hForward : s.edge p x = c p (label x) := by
      rcases Finset.mem_insert.mp hp with he | hp
      · subst p
        exact hConst x (hMem x hx).1 _ (hTarget (label x)).1 hSame
      · calc
          s.edge p x = s.column p (sort x) := (s.columns p hp x (hMem x hx).1).1
          _ = s.column p (sort (target (label x))) := congrArg (s.column p) hSame
          _ = c p (label x) := (s.columns p hp _ (hTarget (label x)).1).1.symm
    exact ⟨hForward, (s.sym x p).trans hForward⟩
  have hFree : ResolvedLiveFree s.edge ell (insert r s.old) W := by
    intro D hD hc
    apply s.free D _ hc
    intro x hx
    rcases hD x hx with hp | hw
    · rcases Finset.mem_insert.mp hp with he | hp
      · subst x
        exact Or.inr hr
      · exact Or.inl hp
    · exact Or.inr hw
  have hRaw := finiteOldFuture_free_implies_raw_support s.edge ell n
    (insert r s.old) C label c hDisj hCols
    (resolvedLiveFree_finite_union s.edge (insert r s.old) C W hFree
      (fun x hx => (hMem x hx).1)) C (Finset.Subset.refl C) hClique
  let w := integerCliqueWeightsOfFinset label C hSmall
  have hw : WitnessRespects (integerCliqueOnSupport (d := n) (ell := ell))
      (finiteOldColumnRawBound s.edge ell n (insert r s.old) c) w := by
    intro V
    rw [integerCliqueOnSupport_of_finset]
    exact hRaw V
  have hBound := witnessValue_le_canonical
    (integerCliqueOnSupport (d := n) (ell := ell))
    (finiteOldColumnRawBound s.edge ell n (insert r s.old) c) w hw U
  have hFilter : C.filter (fun x => label x ∈ U.1) = C := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.left,fun hx => ⟨hx,(hLabel x hx).1⟩⟩
  change integerCliqueOnSupport (integerCliqueWeightsOfFinset label C hSmall) U ≤ _ at hBound
  rw [integerCliqueOnSupport_of_finset, hFilter] at hBound
  change resolvedTargetAge s.edge ell s.old target U ≤
    resolvedTargetAge s.edge ell (insert r s.old) target U
  rw [hBefore]
  exact hBound

/-- Proof object for a finite batch of genuine private markers.
The actual state and the precise Boolean test are retained. -/
def ResolvedMarkerBatchStep {W : Set Nat} (s t : ResolvedBareStage 4 W)
    (f : Nat → Bool) : Prop :=
  ∃ (d : Nat) (sort : Nat → Fin d)
    (hEven : ∀ v ∈ W, v % 2 = 0)
    (hSafe : ∀ C : Finset Nat, (∀ x ∈ C, x ∈ W ∧ f x = true) →
      IsDirectedCliqueOn s.edge C → C.card < 3),
    ResolvedClassExact s.edge s.old W sort ∧
    t = s.refineBatch sort f hEven hSafe

/-- Data of one complete finite round, including its two split batches,
the actual saturated cover path, and the literal coding move.
W' is the whole surviving live set, not an independently chosen subset. -/
def ResolvedRoundTrace {W W' : Set Nat} (s : ResolvedBareStage 4 W)
    (r : Nat) (t : ResolvedBareStage 4 W') : Prop :=
  ∃ (s1 s2 : ResolvedBareStage 4 W)
    (d : Nat) (sort : Nat → Fin d)
    (a b : ResolvedLiveStage d 4 W sort),
    ResolvedMarkerBatchStep s s1 (fun v => decide (v = r)) ∧
    ResolvedMarkerBatchStep s1 s2 (fun v => s1.edge r v) ∧
    a.toBare = s2 ∧
    ResolvedLiveCoverPath W sort a b ∧
    ResolvedClassExact a.edge a.old W sort ∧
    b.oldAge = b.futureAge ∧
    ResolvedClassExact b.edge b.old W sort ∧
    (∀ v ∈ W, sort v = sort r → v = r) ∧
    (∀ v ∈ W, ∀ w ∈ W, sort v = sort w → b.edge r v = b.edge r w) ∧
    W' = W \ {r} ∧ t.edge = b.edge ∧ t.old = insert r b.old

structure ResolvedRoundResult {W W' : Set Nat} (s : ResolvedBareStage 4 W)
    (r : Nat) (t : ResolvedBareStage 4 W') : Prop where
  trace : ResolvedRoundTrace s r t
  old_mono : s.old ⊆ t.old
  coded : r ∈ t.old
  preserve : ∀ x y : Nat, (x ∈ s.old ∨ x ∈ W) →
    (y ∈ s.old ∨ y ∈ W) → t.edge x y = s.edge x y

/-- Construct an actual full finite round over the prescribed live
graph, deriving isolation, adjacency refinement, saturated age,
and the full coherent round trace. -/
theorem resolvedBare_exists_round {W W' : Set Nat} (s : ResolvedBareStage 4 W)
    (r : Nat) (hr : r ∈ W) (hEven : ∀ v ∈ W, v % 2 = 0)
    (hNext : W' = W \ {r}) :
    ∃ t : ResolvedBareStage 4 W', ResolvedRoundResult s r t := by
  classical
  have hW : W.Nonempty := ⟨r,hr⟩
  obtain ⟨d0,sort0,a0,hBare0,_hOcc0,hExact0⟩ := s.exists_exact_labels hW
  have hEx0 : ResolvedClassExact s.edge s.old W sort0 := by
    simpa only [← hBare0, ResolvedLiveStage.toBare] using hExact0
  let f0 : Nat → Bool := fun v => decide (v = r)
  let s1 := s.refineBatch sort0 f0 hEven (s.singleton_test_safe r)
  have hSplit0 : ResolvedMarkerBatchStep s s1 f0 :=
    ⟨d0,sort0,hEven,s.singleton_test_safe r,hEx0,rfl⟩
  have hExact1 := s.refineBatch_exact sort0 f0 hEven (s.singleton_test_safe r) hEx0
  have hIso1 : ∀ v ∈ W,
      (∀ p ∈ s1.old, s1.edge p v = s1.edge p r) → v = r := by
    intro v hv h
    have he := (hExact1 v hv r hr).2 h
    have hb := congrArg Prod.snd he
    change decide (v = r) = decide (r = r) at hb
    simpa using hb
  obtain ⟨d1,sort1,a1,hBare1,_hOcc1,hEx1'⟩ := s1.exists_exact_labels hW
  have hEx1 : ResolvedClassExact s1.edge s1.old W sort1 := by
    simpa only [← hBare1, ResolvedLiveStage.toBare] using hEx1'
  let f1 : Nat → Bool := fun v => s1.edge r v
  let s2 := s1.refineBatch sort1 f1 hEven (s1.neighbour_test_safe r hr)
  have hSplit1 : ResolvedMarkerBatchStep s1 s2 f1 :=
    ⟨d1,sort1,hEven,s1.neighbour_test_safe r hr,hEx1,rfl⟩
  have hExact2 := s1.refineBatch_exact sort1 f1 hEven (s1.neighbour_test_safe r hr) hEx1
  obtain ⟨d,sort,a,hBare2,hOcc,hExA⟩ := s2.exists_exact_labels hW
  obtain ⟨b,hPath,hAge,hFuture,hOldAB,hKeepAB⟩ :=
    resolvedLive_normalizes_actual_future_by_covers W sort a (by decide) hOcc
      (fun P n => resolvedFreshOdd W hEven P n)
  have hSat : b.oldAge = b.futureAge := hAge.trans hFuture.symm
  have hExactB := resolvedClassExact_of_live_extension a b hExA hOldAB hKeepAB
  have hIsoB : ∀ v ∈ W, sort v = sort r → v = r := by
    intro v hv he
    have hBitA := (hExA v hv r hr).1 he
    have hBit2 : ∀ p ∈ s2.old, s2.edge p v = s2.edge p r := by
      simpa only [← hBare2, ResolvedLiveStage.toBare] using hBitA
    have hPair := (hExact2 v hv r hr).2 hBit2
    exact hIso1 v hv ((hEx1 v hv r hr).1 (congrArg Prod.fst hPair))
  have hConstB : ∀ v ∈ W, ∀ w ∈ W, sort v = sort w →
      b.edge r v = b.edge r w := by
    intro v hv w hw he
    have hBitA := (hExA v hv w hw).1 he
    have hBit2 : ∀ p ∈ s2.old, s2.edge p v = s2.edge p w := by
      simpa only [← hBare2, ResolvedLiveStage.toBare] using hBitA
    have hPair := (hExact2 v hv w hw).2 hBit2
    have hRV := s1.refineBatch_preserves sort1 f1 hEven (s1.neighbour_test_safe r hr)
      r v (Or.inr hr) (Or.inr hv)
    have hRW := s1.refineBatch_preserves sort1 f1 hEven (s1.neighbour_test_safe r hr)
      r w (Or.inr hr) (Or.inr hw)
    have hEq : a.edge r v = a.edge r w := by
      change a.toBare.edge r v = a.toBare.edge r w
      rw [hBare2]
      exact hRV.trans ((congrArg Prod.snd hPair).trans hRW.symm)
    exact (hKeepAB r v (Or.inr hr) (Or.inr hv)).trans
      (hEq.trans (hKeepAB r w (Or.inr hr) (Or.inr hw)).symm)
  have hSub : W' ⊆ W := by
    intro x hx
    rw [hNext] at hx
    exact hx.1
  have hrNot : r ∉ W' := by
    rw [hNext]
    simp
  have hSep : ∀ p ∈ insert r b.old, p ∉ W' := by
    intro p hp hw
    rcases Finset.mem_insert.mp hp with he | hp
    · subst p; exact hrNot hw
    · exact b.separated p hp (hSub hw)
  have hFree : ResolvedLiveFree b.edge 4 (insert r b.old) W' := by
    intro C hC hc
    apply b.free C _ hc
    intro v hv
    rcases hC v hv with hp | hw
    · rcases Finset.mem_insert.mp hp with he | hp
      · subst v; exact Or.inr hr
      · exact Or.inl hp
    · exact Or.inr (hSub hw)
  let t : ResolvedBareStage 4 W' :=
    ⟨b.edge,insert r b.old,hSep,hFree,b.sym,b.loops⟩
  have h01 : s.old ⊆ s1.old := Finset.subset_union_left
  have h12 : s1.old ⊆ s2.old := Finset.subset_union_left
  have h2A : s2.old = a.old := by
    exact (congrArg ResolvedBareStage.old hBare2).symm
  have h2B : s2.old ⊆ b.old := by rw [h2A]; exact hOldAB
  refine ⟨t,⟨?_,?_,Finset.mem_insert_self r b.old,?_⟩⟩
  · exact ⟨s1,s2,d,sort,a,b,hSplit0,hSplit1,hBare2,hPath,hExA,hSat,
      hExactB,hIsoB,hConstB,hNext,rfl,rfl⟩
  · exact h01.trans (h12.trans (h2B.trans (by
      intro x hx; exact Finset.mem_insert_of_mem hx)))
  · intro x y hx hy
    have hx1 : x ∈ s1.old ∨ x ∈ W := hx.imp (fun h => h01 h) id
    have hy1 : y ∈ s1.old ∨ y ∈ W := hy.imp (fun h => h01 h) id
    have hx2 : x ∈ s2.old ∨ x ∈ W := hx1.imp (fun h => h12 h) id
    have hy2 : y ∈ s2.old ∨ y ∈ W := hy1.imp (fun h => h12 h) id
    have hxA : x ∈ a.old ∨ x ∈ W := by rw [← h2A]; exact hx2
    have hyA : y ∈ a.old ∨ y ∈ W := by rw [← h2A]; exact hy2
    change b.edge x y = s.edge x y
    calc
      b.edge x y = a.edge x y := hKeepAB x y hxA hyA
      _ = s2.edge x y := congrFun (congrFun (congrArg ResolvedBareStage.edge hBare2) x) y
      _ = s1.edge x y := s1.refineBatch_preserves sort1 f1 hEven
        (s1.neighbour_test_safe r hr) x y hx1 hy1
      _ = s.edge x y := s.refineBatch_preserves sort0 f0 hEven
        (s.singleton_test_safe r) x y hx hy

/-- The code checkpoint is exactly the terminal old pool with the coded
name erased. This derives both ordinary certificates for the actual
coding event, including every fixed surviving terminal list. -/
theorem ResolvedRoundResult.coding_neutral {W W' : Set Nat}
    {s : ResolvedBareStage 4 W} {r : Nat} {t : ResolvedBareStage 4 W'}
    (h : ResolvedRoundResult s r t) (hr : r ∈ W)
    {n : Nat} (target : Fin n → Nat) (hTarget : ∀ i, target i ∈ W') :
    resolvedTargetAge t.edge 4 (t.old.erase r) target =
      resolvedTargetAge t.edge 4 t.old target := by
  classical
  obtain ⟨s1,s2,d,sort,a,b,_hSplit0,_hSplit1,_hBare,_hPath,_hExactA,hSat,
    _hExact,hIso,hConst,hNext,hEdge,hOld⟩ := h.trace
  have hrNot : r ∉ b.old := fun hp => b.separated r hp hr
  have hErase : (insert r b.old).erase r = b.old := by
    ext p
    simp only [Finset.mem_erase, Finset.mem_insert]
    constructor
    · rintro ⟨hne,he | hp⟩
      · exact False.elim (hne he)
      · exact hp
    · intro hp
      refine ⟨?_,Or.inr hp⟩
      intro he
      exact hrNot (he ▸ hp)
  have hT : ∀ i, target i ∈ W ∧ target i ≠ r := by
    intro i
    have hMem := hTarget i
    rw [hNext] at hMem
    exact ⟨hMem.1, by simpa using hMem.2⟩
  rw [hEdge,hOld,hErase]
  exact (b.saturatedCode_target_neutral r hr (by decide) hIso hConst hSat target hT).symm

theorem ResolvedRoundResult.coding_no_split {W W' : Set Nat}
    {s : ResolvedBareStage 4 W} {r : Nat} {t : ResolvedBareStage 4 W'}
    (h : ResolvedRoundResult s r t) (hr : r ∈ W)
    (v w : Nat) (hv : v ∈ W') (hw : w ∈ W')
    (hOldBits : ∀ p ∈ t.old.erase r, t.edge p v = t.edge p w) :
    t.edge r v = t.edge r w := by
  classical
  obtain ⟨s1,s2,d,sort,a,b,_hSplit0,_hSplit1,_hBare,_hPath,_hExactA,_hSat,
    hExact,_hIso,hConst,hNext,hEdge,hOld⟩ := h.trace
  rw [hNext] at hv hw
  rw [hEdge,hOld] at hOldBits
  rw [hEdge]
  apply hConst v hv.1 w hw.1
  apply (hExact v hv.1 w hw.1).2
  intro p hp
  have hpr : p ≠ r := by
    intro he
    exact b.separated r (he ▸ hp) hr
  exact hOldBits p (Finset.mem_erase.mpr ⟨hpr,Finset.mem_insert_of_mem hp⟩)

end Kk
