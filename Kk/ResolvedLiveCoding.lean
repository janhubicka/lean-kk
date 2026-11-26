import Kk.ResolvedLiveCoverNormalization
import Mathlib.Tactic

/-!
# Actual class columns and normalized survivor coding
The actual clique-witness proof replaces controlled pre-age algebra for
survivor neutrality, but not the separate legal zero-code preprofile
calculation used in the finite history parser.
-/

namespace Kk

/-- Class equality is EXACT equality of the complete old passing columns.
Labels outside the occupied range are irrelevant. -/
def ResolvedClassExact {α : Type*} (E : Nat → Nat → Bool)
    (P : Finset Nat) (W : Set Nat) (cls : Nat → α) : Prop :=
  ∀ v ∈ W, ∀ w ∈ W, cls v = cls w ↔ ∀ p ∈ P, E p v = E p w

theorem resolvedClassExact_refine {α : Type*} (E E' : Nat → Nat → Bool)
    (P : Finset Nat) (W : Set Nat) (cls : Nat → α) (q : Nat)
    (hExact : ResolvedClassExact E P W cls)
    (hOld : ∀ p ∈ P, ∀ v ∈ W, E' p v = E p v) :
    ResolvedClassExact E' (insert q P) W (fun v => (cls v, E' q v)) := by
  intro v hv w hw
  constructor
  · intro h p hp
    rcases Finset.mem_insert.mp hp with he | hp
    · subst p
      exact congrArg Prod.snd h
    · rw [hOld p hp v hv, hOld p hp w hw]
      exact (hExact v hv w hw).1 (congrArg Prod.fst h) p hp
  · intro h
    apply Prod.ext
    · apply (hExact v hv w hw).2
      intro p hp
      rw [← hOld p hp v hv, ← hOld p hp w hw]
      exact h p (Finset.mem_insert_of_mem hp)
    · exact h q (Finset.mem_insert_self q P)

theorem resolvedClassExact_insert_constant {α : Type*} (E E' : Nat → Nat → Bool)
    (P : Finset Nat) (W : Set Nat) (cls : Nat → α) (q : Nat)
    (hExact : ResolvedClassExact E P W cls)
    (hOld : ∀ p ∈ P, ∀ v ∈ W, E' p v = E p v)
    (hConst : ∀ v ∈ W, ∀ w ∈ W, cls v = cls w → E' q v = E' q w) :
    ResolvedClassExact E' (insert q P) W cls := by
  intro v hv w hw
  constructor
  · intro h p hp
    rcases Finset.mem_insert.mp hp with he | hp
    · subst p
      exact hConst v hv w hw h
    · rw [hOld p hp v hv, hOld p hp w hw]
      exact (hExact v hv w hw).1 h p hp
  · intro h
    apply (hExact v hv w hw).2
    intro p hp
    rw [← hOld p hp v hv, ← hOld p hp w hw]
    exact h p (Finset.mem_insert_of_mem hp)

theorem resolvedClassExact_restrict {α : Type*} (E : Nat → Nat → Bool)
    (P : Finset Nat) (W W' : Set Nat) (cls : Nat → α)
    (hW : W' ⊆ W) (hExact : ResolvedClassExact E P W cls) :
    ResolvedClassExact E P W' cls :=
  fun v hv w hw => hExact v (hW hv) w (hW hw)

/-- If a literal column changes only outside P it gives the same old
canonical age. Useful when defining the new passing bit at a fresh pivot. -/
theorem resolvedOldCanonical_congr_columns {d ell : Nat}
    (E : Nat → Nat → Bool) (P : Finset Nat)
    (c c' : Nat → Fin d → Bool)
    (hCol : ∀ p ∈ P, ∀ i, c' p i = c p i) :
    integerGraphAgeCanonical d ell (finiteOldColumnRawBound E ell d P c') =
      integerGraphAgeCanonical d ell (finiteOldColumnRawBound E ell d P c) := by
  classical
  have hRaw : finiteOldColumnRawBound E ell d P c' =
      finiteOldColumnRawBound E ell d P c := by
    funext T
    have hPool : oldSupportCommonNeighbourPool P c' T.1 =
        oldSupportCommonNeighbourPool P c T.1 := by
      ext p
      simp only [oldSupportCommonNeighbourPool, Finset.mem_filter]
      constructor
      · rintro ⟨hp,hbits⟩
        refine ⟨hp,?_⟩
        intro i hi
        rw [← hCol p hp i]
        exact hbits i hi
      · rintro ⟨hp,hbits⟩
        refine ⟨hp,?_⟩
        intro i hi
        rw [hCol p hp i]
        exact hbits i hi
    unfold finiteOldColumnRawBound
    rw [hPool]
  rw [hRaw]

/-- Move one genuine normalized coding vertex into the old pool.
The remaining whole classes are reindexed injectively, and the new
coding bit is constant on each of these classes. The literal graph
is unchanged. The output derives complete survivor canonical neutrality
from actual clique witnesses; no controlled-pre-age premise is used. -/
theorem resolvedLive_code_normalized_survivors {d e ell : Nat}
    {W : Set Nat} {sort : Nat → Fin d}
    (s : ResolvedLiveStage d ell W sort)
    (p : Nat) (hp : p ∈ W)
    (W' : Set Nat) (sort' : Nat → Fin e)
    (pi : Fin e → Fin d) (hell : 0 < ell)
    (hInj : Function.Injective pi)
    (hW : ∀ v, v ∈ W' ↔ v ∈ W ∧ ∃ i, sort v = pi i)
    (hSort : ∀ v ∈ W', sort v = pi (sort' v))
    (hpNot : p ∉ W')
    (bit : Fin e → Bool)
    (hBit : ∀ v ∈ W', s.edge p v = bit (sort' v))
    (hSat : s.oldAge = s.futureAge) :
    ∃ t : ResolvedLiveStage e ell W' sort',
      t.edge = s.edge ∧ t.old = insert p s.old ∧
      (∀ U : IntegerGraphSupport e ell,
        t.oldAge U = s.oldAge (integerGraphSupportImage pi U)) ∧
      t.oldAge = t.futureAge := by
  classical
  let c : Nat → Fin e → Bool :=
    fun q i => if q = p then bit i else s.column q (pi i)
  have hpOld : p ∉ s.old := fun h => s.separated p h hp
  have hSub : W' ⊆ W := by
    intro v hv
    exact ((hW v).1 hv).1
  have hSep : ∀ q ∈ insert p s.old, q ∉ W' := by
    intro q hq hqW
    rcases Finset.mem_insert.mp hq with he | hOld
    · subst q; exact hpNot hqW
    · exact s.separated q hOld (hSub hqW)
  have hCols : ResolvedLiveColumns s.edge (insert p s.old) W' sort' c := by
    intro q hq v hv
    rcases Finset.mem_insert.mp hq with he | hOld
    · subst q
      simpa [c, s.sym v p] using And.intro (hBit v hv) (hBit v hv)
    · have hqp : q ≠ p := by intro h; exact hpOld (h ▸ hOld)
      have h := s.columns q hOld v (hSub hv)
      simpa [c, hqp, hSort v hv] using h
  have hFree : ResolvedLiveFree s.edge ell (insert p s.old) W' := by
    intro C hC hc
    apply s.free C _ hc
    intro v hv
    rcases hC v hv with hOld | hNew
    · rcases Finset.mem_insert.mp hOld with he | hV
      · subst v; exact Or.inr hp
      · exact Or.inl hV
    · exact Or.inr (hSub hNew)
  let t : ResolvedLiveStage e ell W' sort' :=
    { edge := s.edge, old := insert p s.old, column := c,
      separated := hSep, columns := hCols, free := hFree,
      sym := s.sym, loops := s.loops }
  have hBefore : integerGraphAgeCanonical e ell
      (finiteOldColumnRawBound s.edge ell e s.old c) =
        resolvedActualAge s.edge ell W' sort' := by
    have hColEq : ∀ q ∈ s.old, ∀ i, c q i = s.column q (pi i) := by
      intro q hq i
      have hqp : q ≠ p := by intro h; exact hpOld (h ▸ hq)
      simp [c,hqp]
    rw [resolvedOldCanonical_congr_columns (ell := ell) s.edge s.old
      (fun q i => s.column q (pi i)) c hColEq]
    funext U
    calc
      _ = s.oldAge (integerGraphSupportImage pi U) :=
        finiteOldColumnCanonical_reindex s.edge s.old s.column pi hell U
      _ = s.futureAge (integerGraphSupportImage pi U) := by rw [hSat]
      _ = resolvedActualAge s.edge ell W' sort' U :=
        (resolvedActualAge_survivor_reindex s.edge W W' sort sort' pi hell
          hInj hW hSort U).symm
  have hAfter : t.oldAge = integerGraphAgeCanonical e ell
      (finiteOldColumnRawBound s.edge ell e s.old c) :=
    resolvedLive_survivor_neutral_of_saturation s.edge s.old (insert p s.old)
      W' sort' c (by intro q hq; exact Finset.mem_insert_of_mem hq)
      hSep hCols hFree hBefore
  refine ⟨t,rfl,rfl,?_,hAfter.trans hBefore⟩
  intro U
  rw [hAfter,hBefore]
  exact (resolvedActualAge_survivor_reindex s.edge W W' sort sort' pi hell
    hInj hW hSort U).trans (congrFun hSat (integerGraphSupportImage pi U)).symm

end Kk
