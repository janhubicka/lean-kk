import Kk.ResolvedFairSelectedEnvelope

/-!
# Omitted cuts when every actual auxiliary event is retained

English proof reviewed before implementation:
`docs/all_auxiliary_envelope_english_20261127.md`.
Omitted meaningful cuts are unselected coding addresses. The actual
eligible selected front is decoded into strictly later original indices.
No uniform auxiliary-event or complete-record bound is asserted.
-/

namespace Kk

/-- With every auxiliary event retained, an unretained role is coded false. -/
theorem resolvedFairAllAuxRole_omitted_coded
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (S : Finset Nat)
    (v : Nat)
    (hOmitted : ¬ ResolvedQRetainedBase
      (resolvedFairEventRole s0 (resolvedFairSelectedKeep s0 S (fun _ => true)) v)) :
    resolvedFairEventRole s0 (resolvedFairSelectedKeep s0 S (fun _ => true)) v =
      .coded false := by
  cases hRole : resolvedFairEventRole s0
      (resolvedFairSelectedKeep s0 S (fun _ => true)) v with
  | dummy => exact False.elim (hOmitted (Or.inl hRole))
  | coded b =>
      cases b with
      | false => rfl
      | true => exact False.elim (hOmitted (Or.inr (Or.inl hRole)))
  | auxiliary k b =>
      have hAux := (resolvedFairEventRole_auxiliary_iff s0
        (resolvedFairSelectedKeep s0 S (fun _ => true)) v k b).mp hRole
      have hFlag := resolvedFairSelectedKeep_auxiliary s0 S (fun _ => true) k hAux.2.2.1
      have hb : b = true := hAux.2.2.2.symm.trans hFlag
      subst b
      exact False.elim (hOmitted (Or.inr (Or.inr ⟨k, hRole⟩)))

/-- The omitted coordinate is an actual original outside the coding selection. -/
theorem resolvedFairAllAuxRole_omitted_original
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) (v : Nat)
    (hOmitted : ¬ ResolvedQRetainedBase
      (resolvedFairEventRole s0 (resolvedFairSelectedKeep s0 S (fun _ => true)) v)) :
    ∃ n, n ∉ S ∧ v = resolvedFairOriginalAddress s0 n := by
  obtain ⟨n, hAddress, hFlag⟩ :=
    (resolvedFairEventRole_coded_iff_originalAddress s0 hEmpty
      (resolvedFairSelectedKeep s0 S (fun _ => true)) v false).mp
      (resolvedFairAllAuxRole_omitted_coded s0 S v hOmitted)
  refine ⟨n, ?_, hAddress⟩
  intro hn
  simp [resolvedFairSelectedKeep_code, hn] at hFlag

/-- Every omitted meaningful cut of the finite plan is an unselected code. -/
theorem resolvedFairAllAux_omitted_real
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) (c : Nat)
    (hCut : c < resolvedFairRetainedTop s0 (resolvedFairSelectionCap S))
    (hOmitted : c ∉ resolvedFairRetainedLevels s0
      (resolvedFairFiniteKeep s0 S (fun _ => true)) (resolvedFairSelectionCap S))
    (hReal : oneGapReal c) :
    ∃ n, n ∉ resolvedFairSelectionWithCap S ∧
      c = resolvedFairOriginalAddress s0 n :=
  resolvedFairAllAuxRole_omitted_original s0 hEmpty (resolvedFairSelectionWithCap S) c
    (resolvedFairRetainedLevels_omitted_real_not_retained s0
      (resolvedFairFiniteKeep s0 S (fun _ => true)) (resolvedFairSelectionCap S)
      c hCut hOmitted hReal)

/-- Decode an entry of the actual eligible front into its original index. -/
noncomputable def resolvedFairSelectedFrontIndex
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) (auxKeep : Nat → Bool)
    (N : Nat) (V : Set (Fin N)) (cut : Nat)
    (i : Fin (resolvedFairSelectedFrontSize s0
      (resolvedFairSelectedKeep s0 S auxKeep) N V cut)) : Nat :=
  Classical.choose (resolvedFairSelectedFront_original s0 hEmpty S auxKeep N V cut i)

theorem resolvedFairSelectedFrontIndex_mem
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) (auxKeep : Nat → Bool)
    (N : Nat) (V : Set (Fin N)) (cut : Nat)
    (i : Fin (resolvedFairSelectedFrontSize s0
      (resolvedFairSelectedKeep s0 S auxKeep) N V cut)) :
    resolvedFairSelectedFrontIndex s0 hEmpty S auxKeep N V cut i ∈ S :=
  (Classical.choose_spec
    (resolvedFairSelectedFront_original s0 hEmpty S auxKeep N V cut i)).1

theorem resolvedFairSelectedFrontIndex_address
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) (auxKeep : Nat → Bool)
    (N : Nat) (V : Set (Fin N)) (cut : Nat)
    (i : Fin (resolvedFairSelectedFrontSize s0
      (resolvedFairSelectedKeep s0 S auxKeep) N V cut)) :
    resolvedFairSelectedFront s0 (resolvedFairSelectedKeep s0 S auxKeep) N V cut i =
      resolvedFairOriginalAddress s0
        (resolvedFairSelectedFrontIndex s0 hEmpty S auxKeep N V cut i) :=
  (Classical.choose_spec
    (resolvedFairSelectedFront_original s0 hEmpty S auxKeep N V cut i)).2

theorem resolvedFairSelectedFront_after_cut
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (N : Nat) (V : Set (Fin N)) (cut : Nat)
    (i : Fin (resolvedFairSelectedFrontSize s0 keep N V cut)) :
    cut < resolvedFairSelectedFront s0 keep N V cut i :=
  oneGapCodingFrontSelected_after_cut
    ((oneGapPartial (resolvedFairEventEdge s0)).finitePrefix N)
    (resolvedFairEventRole s0 keep) V cut i

/-- At a coding cut, every decoded front terminal survives that coding round. -/
theorem resolvedFairSelectedFrontIndex_later
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) (auxKeep : Nat → Bool)
    (N : Nat) (V : Set (Fin N)) (n : Nat)
    (i : Fin (resolvedFairSelectedFrontSize s0
      (resolvedFairSelectedKeep s0 S auxKeep) N V (resolvedFairOriginalAddress s0 n))) :
    n < resolvedFairSelectedFrontIndex s0 hEmpty S auxKeep N V
      (resolvedFairOriginalAddress s0 n) i := by
  have hLater := resolvedFairSelectedFront_after_cut s0
    (resolvedFairSelectedKeep s0 S auxKeep) N V (resolvedFairOriginalAddress s0 n) i
  rw [resolvedFairSelectedFrontIndex_address s0 hEmpty S auxKeep N V] at hLater
  exact (resolvedFairOriginalAddress_strictMono s0).lt_iff_lt.mp hLater

end Kk
