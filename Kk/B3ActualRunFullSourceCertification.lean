import Kk.B3FullSourceCertification
import Kk.NumericHFinalPoolCrossing
import Mathlib.Tactic

/-!
# Track B: the true finite AlgorithmRun has an EXHAUSTIVE FULL source

English-first proof and sixteen adversarial checks:
  docs/track_b_actual_run_exhaustive_source_english_audit.md

We CONSTRUCT a HensonCutOccurrence whose Full names are exactly
the genuine closureSelectedOriginal names, in the actual
maintained final original pool V= hStageOriginals ... (Run.I 0).

The pinned successor-tree original pool theorem derives, rather
than assumes, exhaustive representation of every pre-cut Kpt
closure node in Z=closure ... (Run.I (cut+1)) X.

The actual chosen FULL old/upper L+ source graph and the
cut-star upper-L spectrum are then certified intrinsically
via the physical Kpt crossing relation. This is ONE run,
not a common source orbit across different diary occurrences.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A literal finite Henson source occurrence constructed from a
genuine Algorithm 5.4 run at a cut without a competing (I2) meet.

The original-name universe is the ACTUAL maintained FINAL pool.
The true source is the pre-cut meet/parameter closure.
Full is defined to be the EXACT closure-selected predicate,
not an arbitrary represented subpool. -/
noncomputable def actualHensonRunCutOccurrence
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N : Nat)
    (U : Finset (Fin N))
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (X : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell)) X top)
    (cut : Nat) (hCut : cut < N)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      a ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (cut+1)) X ∧
      ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        b ∈ SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily ell hell))
          (Run.I (cut+1)) X ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :
    HensonCutOccurrence ell cut hell := by
  classical
  let family := hensonForbiddenFamily ell hell
  let A := finiteNumericH (normalizedGraphModel E) k N
  let V : Finset (Fin N) :=
    hStageOriginals (normalizedGraphModel E) k N U (Run.I 0)
  let original : Fin V.card → Fin N := hOriginalName V
  let Z : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (Run.I (cut+1)) X
  exact {
    k := k
    hK := hK
    N := N
    M := V.card
    E := E
    hLoops := hLoops
    hSym := hSym
    hClique := hClique
    hCut := hCut
    original := original
    hAvoid := hAvoid
    Z := Z
    Full := closureSelectedOriginal family A hAvoid original Z cut
    hRepresented := by intro v hV; exact hV
    hNoI2 := hNoI2
  }

/-- The source is literally FULL: each maintained original name is
selected iff it represents some genuine actual pre-cut Kpt
closure node strictly crossing the cut. This discharges BOTH
directions, unlike the older one-sided hRepresented field. -/
theorem actualHensonRunCutOccurrence_fullExact
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N : Nat)
    (U : Finset (Fin N))
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (X : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell)) X top)
    (cut : Nat) (hCut : cut < N)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      a ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (cut+1)) X ∧
      ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        b ∈ SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily ell hell))
          (Run.I (cut+1)) X ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :
    let P := actualHensonRunCutOccurrence
      ell hell k hK E hLoops hSym hClique
      N U hAvoid X top Run cut hCut hNoI2
    ∀ v : Fin P.M,
      P.Full v ↔ closureSelectedOriginal
        (hensonForbiddenFamily ell hell)
        P.ambient P.hAvoid P.original P.Z cut v := by
  intro P v
  rfl

/-- EVERY source node of the TRUE pre-cut closure is a prefix of
one ACTUAL original in the maintained final-stage name universe.
This is not an assumed hPool: it is deduced from the verified
numeric-H AlgorithmRun closure source invariant. -/
theorem actualHensonRunCutOccurrence_poolExhaustive
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N : Nat)
    (U : Finset (Fin N))
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (X : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (hX : X ⊆ ambientPrefixPool
      (hensonForbiddenFamily ell hell)
      (finiteNumericH (normalizedGraphModel E) k N)
      hAvoid (U : Set (Fin N)))
    (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell)) X top)
    (cut : Nat) (hCut : cut < N) (hBelow : cut < top)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      a ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (cut+1)) X ∧
      ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        b ∈ SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily ell hell))
          (Run.I (cut+1)) X ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :
    let P := actualHensonRunCutOccurrence
      ell hell k hK E hLoops hSym hClique
      N U hAvoid X top Run cut hCut hNoI2
    ∀ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      z ∈ P.Z →
        ∃ v : Fin P.M,
          z ≤ P.ambient.kptOriginal
            (hensonForbiddenFamily ell hell) P.hAvoid (P.original v) := by
  classical
  intro P z hz
  let family := hensonForbiddenFamily ell hell
  let K : AgeTestModel 1 0 1 := normalizedGraphModel E
  let V : Finset (Fin N) :=
    hStageOriginals K k N U (Run.I 0)
  have hCarrier : ∀ i : Nat, i ∈ K.carrier := by
    intro i
    trivial
  have hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K :=
    (hensonForbiddenFamily_avoids_iff ell hell E).2
      ⟨hLoops,hSym,hClique⟩
  have hXCanonical : X ⊆ ambientPrefixPool
      family (finiteNumericH K k N)
      (finiteNumericH_avoids_family
        family K hCarrier k N hAvoidK) (U : Set (Fin N)) := by
    exact hX
  have hZ : z ∈ SMTree.Envelope.closure
      (admissibleKptSTree family) (Run.I (cut+1)) X := hz
  obtain ⟨v,hv,hzv⟩ :=
    numericH_algorithmRun_closure_original_in_final_pool
      family K hCarrier hAvoidK
      k N U X hXCanonical top cut hBelow Run z hZ
  let j : Fin V.card := V.equivFin ⟨v,hv⟩
  have hOriginal : P.original j = v := by
    change hOriginalName V j = v
    simp [hOriginalName,j] <;> rfl
  refine ⟨j,?_⟩
  simpa only [P,actualHensonRunCutOccurrence,
    HensonCutOccurrence.ambient,hOriginal] using hzv

/-- True AlgorithmRun source-certification in ONE theorem:
its COMPLETE chosen old/upper L+ source graph is the canonical
physical closure crossing, and its unanchored cut-star upper-L
spectrum is exactly the intrinsic source-name-independent
positive-cut projection of that physical relation.

The source exhaustiveness assumptions have been DISCHARGED from
the actual numerical-H maintained-pool invariant. -/
theorem actualHensonRunCutOccurrence_fullGraph_and_starSpectrum
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N : Nat)
    (U : Finset (Fin N))
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (X : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (hX : X ⊆ ambientPrefixPool
      (hensonForbiddenFamily ell hell)
      (finiteNumericH (normalizedGraphModel E) k N)
      hAvoid (U : Set (Fin N)))
    (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell)) X top)
    (cut : Nat) (hCut : cut < N) (hBelow : cut < top)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      a ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (cut+1)) X ∧
      ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        b ∈ SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily ell hell))
          (Run.I (cut+1)) X ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :
    let P := actualHensonRunCutOccurrence
      ell hell k hK E hLoops hSym hClique
      N U hAvoid X top Run cut hCut hNoI2
    fullPrescribedCrossingGraph P.fullProfile =
      FullPhysicalClosureCrossing
        (hensonForbiddenFamily ell hell) P.Z cut ∧
    (∀ R : RelationalPrefixType (cut+1) 1 0 1,
      P.starProfile.PrescribedUpperLType R ↔
      PhysicalCutStarUpperL
        (hensonForbiddenFamily ell hell) P.Z cut R) := by
  classical
  intro P
  have hExact :=
    actualHensonRunCutOccurrence_fullExact
      ell hell k hK E hLoops hSym hClique
      N U hAvoid X top Run cut hCut hNoI2
  have hPool :=
    actualHensonRunCutOccurrence_poolExhaustive
      ell hell k hK E hLoops hSym hClique
      N U hAvoid X hX top Run cut hCut hBelow hNoI2
  constructor
  · exact HensonCutOccurrence.fullProfile_graph_eq_physical_of_exhaustive
      P hExact hPool
  · intro R
    exact HensonCutOccurrence.starProfile_upperL_iff_physical_of_exhaustive
      P hExact hPool R

#print axioms actualHensonRunCutOccurrence_fullExact
#print axioms actualHensonRunCutOccurrence_poolExhaustive
#print axioms actualHensonRunCutOccurrence_fullGraph_and_starSpectrum

end Kk
