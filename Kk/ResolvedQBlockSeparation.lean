import Kk.TrackDPlannedStageRoles

/-!
# Ordinary-Q separation across an omitted non-dummy base

The English proof and independent audit precede this reconstruction in
`docs/audits/2026-11-23-upper-reconstruction-english.md`.

The block interval condition permits isolated dummies between members.
At a dummy base the new cut-column is zero, but auxiliary old columns
need not be zero. The theorem therefore retains an explicit non-dummy
hypothesis and makes no numerical-H or AlgorithmRun conclusion.
-/

namespace Kk.ResolvedQBlockSeparation

/-- Across an omitted non-dummy base, every future retained auxiliary
original has zero ordinary old column, under block convexity modulo dummies. -/
theorem omitted_nondummy_later_retained_aux_old_column_zero
    (role : Nat → ResolvedQBaseRole)
    (E : Nat → Nat → Bool)
    (hQ : ResolvedQChronologicalAxioms role E)
    (hBlockInterval :
      ∀ p b j block : Nat, ∀ pastFlag futureFlag : Bool,
        p < b → b < j →
        role p = .auxiliary block pastFlag →
        role j = .auxiliary block futureFlag →
        role b = .dummy ∨
          ∃ middleFlag : Bool, role b = .auxiliary block middleFlag)
    (b j block : Nat)
    (hLater : b < j)
    (hOmitted : ResolvedQOmittedBase (role b))
    (hNonDummy : role b ≠ .dummy)
    (hRetained : role j = .auxiliary block true) :
    ∀ p : Nat, p < b → E p j = false := by
  intro p hBefore
  cases hRoleP : role p with
  | dummy =>
      exact hQ.dummy p j hRoleP
  | coded selected =>
      exact hQ.codedAux p j selected block true
        (lt_trans hBefore hLater) hRoleP hRetained
  | auxiliary pastBlock pastFlag =>
      by_cases hSameBlock : pastBlock = block
      · subst pastBlock
        rcases hBlockInterval p b j block pastFlag true
            hBefore hLater hRoleP hRetained with hDummy | ⟨middleFlag, hMiddle⟩
        · exact False.elim (hNonDummy hDummy)
        · have hFlag : middleFlag = true :=
            hQ.blockFlag b j block middleFlag true hMiddle hRetained
          have hMiddleRetained : role b = .auxiliary block true := by
            simpa only [hFlag] using hMiddle
          have hNotOmitted : ¬ ResolvedQOmittedBase (role b) := by
            rw [hMiddleRetained]
            simp [ResolvedQOmittedBase]
          exact False.elim (hNotOmitted hOmitted)
      · exact hQ.auxDifferent p j pastBlock block pastFlag true
          hSameBlock hRoleP hRetained

#print axioms omitted_nondummy_later_retained_aux_old_column_zero

end Kk.ResolvedQBlockSeparation
