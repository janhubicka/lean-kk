import Mathlib.Tactic

/-!
# Track D: exact finite original-Q retained base-neighbour classification

English-first proof and fourteen adversarial checks committed BEFORE Lean:
docs/audits/2026-11-18-track-d-resolved-q-base-roles-english.md

A finite role on each chronological original Q base records:
* isolated dummy;
* coded V vertex, with selected membership in a fixed independent A;
* member of an auxiliary clique block, with its common retained flag.

The conclusions are exact combinatorial implications of four literal
Q-construction edge axioms, *not* assertions that an AlgorithmRun stage
already equals the proposed retained diary carrier.
-/

namespace Kk

/-- A physical ORIGINAL base of the resolved Q graph.
All members of an auxiliary block share the same retained flag;
that coherence is still an explicit construction axiom. -/
inductive ResolvedQBaseRole where
  | dummy
  | coded (selected : Bool)
  | auxiliary (block : Nat) (retained : Bool)
  deriving DecidableEq, Repr

/-- Exactly the Q base roles that may occur in the PROPOSED
retained stage source, before proving equality with an actual run. -/
def ResolvedQRetainedBase (r : ResolvedQBaseRole) : Prop :=
  r = .dummy ∨ r = .coded true ∨
    ∃ block : Nat, r = .auxiliary block true

/-- A base which can have an OMITTED real numerical-H event:
dummy, any coded base at an omitted event, or an unretained
auxiliary block. The real top level of selected coding bases
is *retained*; this predicate alone does not specify a generation. -/
def ResolvedQOmittedBase (r : ResolvedQBaseRole) : Prop :=
  r = .dummy ∨
    (∃ selected : Bool, r = .coded selected) ∨
    ∃ block : Nat, r = .auxiliary block false

/-- Distinctive critical case: if an auxiliary base is omitted,
a later retained auxiliary base cannot be in the SAME block
(whole-block coherence), and distinct blocks are nonadjacent.

No assumption that two members of one auxiliary clique are
nonadjacent; such an assumption would be false. -/
theorem resolvedQ_omitted_aux_later_retained_aux_nonedge
    (role : Nat → ResolvedQBaseRole)
    (E : Nat → Nat → Bool)
    (hAuxDifferent : ∀ i j (p q : Nat) (a b : Bool),
      p ≠ q →
      role i = .auxiliary p a →
      role j = .auxiliary q b →
      E i j = false)
    (hBlockFlag : ∀ i j (block : Nat) (a b : Bool),
      role i = .auxiliary block a →
      role j = .auxiliary block b → a = b)
    (i j p q : Nat)
    (hi : role i = .auxiliary p false)
    (hj : role j = .auxiliary q true) :
    E i j = false := by
  by_cases hSame : p = q
  · subst q
    have hContradiction : false = true :=
      hBlockFlag i j p false true hi hj
    cases hContradiction
  · exact hAuxDifferent i j p q false true hSame hi hj

/-- Every positive later retained base neighbour of an OMITTED
dummy/coding/auxiliary base is a SELECTED coding vertex, never
an isolated dummy or any retained auxiliary original.

The target may genuinely be selected and adjacent to an omitted
nonselected coding base or an omitted auxiliary block. -/
theorem resolvedQ_omitted_base_positive_retained_is_selected_coding
    (role : Nat → ResolvedQBaseRole)
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (hDummy : ∀ i j, role i = .dummy → E i j = false)
    (hCodedAux : ∀ i j (s : Bool) (block : Nat) (keep : Bool),
      i < j → role i = .coded s →
      role j = .auxiliary block keep → E i j = false)
    (hAuxDifferent : ∀ i j (p q : Nat) (a b : Bool),
      p ≠ q →
      role i = .auxiliary p a →
      role j = .auxiliary q b → E i j = false)
    (hBlockFlag : ∀ i j (block : Nat) (a b : Bool),
      role i = .auxiliary block a →
      role j = .auxiliary block b → a = b)
    (i j : Nat) (hij : i < j)
    (hi : ResolvedQOmittedBase (role i))
    (hj : ResolvedQRetainedBase (role j))
    (hEdge : E i j = true) :
    role j = .coded true := by
  rcases hj with hDummyJ | hSelectedJ | ⟨q,hAuxJ⟩
  · have hNo : E i j = false :=
      (hSym i j).trans (hDummy j i hDummyJ)
    simp [hNo] at hEdge
  · exact hSelectedJ
  · rcases hi with hDummyI | hCodeI | ⟨p,hAuxI⟩
    · have hNo := hDummy i j hDummyI
      simp [hNo] at hEdge
    · obtain ⟨s,hCode⟩ := hCodeI
      have hNo := hCodedAux i j s q true hij hCode hAuxJ
      simp [hNo] at hEdge
    · have hNo :=
        resolvedQ_omitted_aux_later_retained_aux_nonedge
          role E hAuxDifferent hBlockFlag i j p q hAuxI hAuxJ
      simp [hNo] at hEdge

/-- If the tested base is itself one of the independent selected
coding vertices, it has NO positive later neighbour among the
proposed retained source bases. This is the exact ordinary-Q
reason that omitted LOWER H generations of selected codes have
no positive physical cut-star. No no-I2 is asserted. -/
theorem resolvedQ_selected_coded_has_no_later_retained_neighbour
    (role : Nat → ResolvedQBaseRole)
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (hDummy : ∀ i j, role i = .dummy → E i j = false)
    (hCodedAux : ∀ i j (s : Bool) (block : Nat) (keep : Bool),
      i < j → role i = .coded s →
      role j = .auxiliary block keep → E i j = false)
    (hIndependent : ∀ i j,
      role i = .coded true →
      role j = .coded true → E i j = false)
    (i j : Nat) (hij : i < j)
    (hi : role i = .coded true)
    (hj : ResolvedQRetainedBase (role j)) :
    E i j = false := by
  rcases hj with hDummyJ | hSelectedJ | ⟨block,hAuxJ⟩
  · exact (hSym i j).trans (hDummy j i hDummyJ)
  · exact hIndependent i j hi hSelectedJ
  · exact hCodedAux i j true block true hij hi hAuxJ

#print axioms Kk.resolvedQ_omitted_aux_later_retained_aux_nonedge
#print axioms Kk.resolvedQ_omitted_base_positive_retained_is_selected_coding
#print axioms Kk.resolvedQ_selected_coded_has_no_later_retained_neighbour

end Kk
