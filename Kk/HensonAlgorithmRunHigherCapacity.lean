import Kk.HensonAlgorithmRunLowerI3
import SuccessorTree.V10.I3ActualHigherSignature
import Mathlib.Tactic

/-!
# Sharp higher-generation signature bound for genuine Henson AlgorithmRuns

Observation 6.52/ Lemma 6.53 of the successor construction count
I3 events at numerical H generation g using signatures based ONLY
on original names from STRICTLY higher generations. The pinned
successor library proves that signature theorem for any family
and selected-stage pool.

Here we derive the genuine Algorithm 5.4 consequence for the
normalized K_ell-free graph language. The SAME finite final-stage
pool V represents the parameter closure at every tested level.
We select its higher-generation subpool once, and use its
cardinality as the signature capacity. No new source/target B3
identity or externally supplied stage-original enumeration is
assumed.

This is the precise quantitative input for a bounded-envelope
induction. It does not show that equal macro-diaries determine
the same marked selected-source pullback.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The exact set of original names in an arbitrary finite pool whose
numeric H generation lies strictly above g. Noncomputability is only
the classical decision of membership in a finite set. -/
noncomputable def higherGenerationStageNames
    {M N : Nat} (original : Fin M → Fin N)
    (k g : Nat) : Finset (Fin M) := by
  classical
  exact Finset.univ.filter (fun v =>
    ∃ idx m : Nat, g < m ∧ m ≤ k ∧
      (original v).val = hPosition k idx m)

/-- For a true numerical-H AlgorithmRun, the number of positive
nonstructural I3 levels in any fixed generation g<k is at most
the I3 signature capacity of the ORIGINALS at strictly HIGHER
generations in the maintained final-stage pool.

The higher subpool is explicit and exact, rather than bounded by
the whole ambient pool. All corrected B3 failures, complete
parameter closure and signature injectivity are derived from
the generic checked successor infrastructure. -/
theorem henson_algorithmRun_lower_I3_levels_card_le_higher_capacity
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N : Nat)
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (hAvoidH :
      ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
        bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (hX : X ⊆ ambientPrefixPool (hensonForbiddenFamily ell hell)
       (finiteNumericH (normalizedGraphModel E) k N)
       hAvoidH (U : Set (Fin N)))
    (top : Nat)
    (R : SuccessorTree.SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell)) X top)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = top)
    (g : Nat) (hg : g < k)
    (levels : Finset Nat)
    (hLevels : ∀ cut, cut ∈ levels →
      0 < cut ∧ cut < top ∧ cut < N ∧ cut ∈ R.I 0 ∧
      ∃ idx : Nat, cut = hPosition k idx g)
    (hNoI1 : ∀ cut, cut ∈ levels →
      ¬ ∃ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        z ∈ SuccessorTree.SMTree.Envelope.closure
            (admissibleKptSTree (hensonForbiddenFamily ell hell))
            (R.I (cut+1)) X ∧ LevelTree.lev z = cut)
    (hNoI2 : ∀ cut, cut ∈ levels →
      ¬ ∃ a : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        a ∈ SuccessorTree.SMTree.Envelope.closure
            (admissibleKptSTree (hensonForbiddenFamily ell hell))
            (R.I (cut+1)) X ∧
        ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
          b ∈ SuccessorTree.SMTree.Envelope.closure
              (admissibleKptSTree (hensonForbiddenFamily ell hell))
              (R.I (cut+1)) X ∧
          SuccessorTree.SMTree.Envelope.SameComponent a b ∧
          LevelTree.lev (LevelTree.meet a b) = cut) :
    let V := hStageOriginals (normalizedGraphModel E) k N U (R.I 0)
    let original : Fin V.card → Fin N :=
      fun j => (V.equivFin.symm j).1
    let higher : Finset (Fin V.card) :=
      higherGenerationStageNames original k g
    levels.card ≤
      ageSignatureCapacity
        (fun j : Fin (hensonForbiddenFamily ell hell).length =>
          ((hensonForbiddenFamily ell hell).get j).patternCard)
        higher.card := by
  classical
  let family : List (NormalizedForbidden 1 0 1) :=
    hensonForbiddenFamily ell hell
  let K : AgeTestModel 1 0 1 := normalizedGraphModel E
  let A : EnumeratedPartialStructure 1 0 1 := finiteNumericH K k N
  have hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K :=
    (hensonForbiddenFamily_avoids_iff ell hell E).2
      ⟨hLoops,hSym,hClique⟩
  have hFamilyBound : ∀ bad, bad ∈ family →
      bad.patternCard ≤ k+1 := by
    intro bad hb
    exact (hensonForbiddenFamily_patternCard_le ell hell bad hb).trans hK
  let V : Finset (Fin N) := hStageOriginals K k N U (R.I 0)
  let original : Fin V.card → Fin N :=
    fun j => (V.equivFin.symm j).1
  have hSurj : ∀ v : Fin N, v ∈ V →
      ∃ j : Fin V.card, original j = v := by
    intro v hv
    refine ⟨V.equivFin ⟨v,hv⟩,?_⟩
    simp [original]
  let Z : Nat → Set (AdmissibleKptNode family) :=
    fun cut => SuccessorTree.SMTree.Envelope.closure
      (admissibleKptSTree family) (R.I (cut+1)) X
  let Selected : Nat → Fin V.card → Prop :=
    fun cut v => closureSelectedOriginal family A hAvoidH original (Z cut) cut v
  have hGeneration : ∀ cut, cut ∈ levels →
      cut < N ∧ ∃ idx : Nat, cut = hPosition k idx g := by
    intro cut hMem
    obtain ⟨_,_,hCut,_,hLoc⟩ := hLevels cut hMem
    exact ⟨hCut,hLoc⟩
  have hFailures : ∀ cut, cut ∈ levels →
      ¬ (selectedStagePoolPrescribedData
        (finiteNumericH K k N) cut original (Selected cut)).CorrectedB3 family := by
    intro cut hMem
    obtain ⟨hPos,hBelow,hCut,hSelected,_⟩ := hLevels cut hMem
    have hPool : ∀ z, z ∈ Z cut →
        ∃ v : Fin V.card, z ≤ A.kptOriginal family
          hAvoidH (original v) := by
      intro z hz
      obtain ⟨v,hv,hzv⟩ :=
        numericH_algorithmRun_closure_original_in_final_pool
          family K (by intro i; trivial) hAvoidK k N
          U X hX top cut hBelow R z hz
      obtain ⟨j,hj⟩ := hSurj v hv
      refine ⟨j,?_⟩
      simpa [A, ←hj] using hzv
    have hInteresting :
        SuccessorTree.SMTree.Envelope.IsInterestingAt
          (normalizedKptSMTree family) (Z cut) cut := by
      have hFinal := R.finalLevel_interesting_of_run hTopSeed hSelected
      have hNext := R.I_succ_eq_higher_final_of_run cut hBelow
      simpa only [Z,hNext] using hFinal
    exact algorithmI3_failsCorrectedB3
      family A hAvoidH original (Z cut) hPool cut hPos
      (hNoI1 cut hMem) (hNoI2 cut hMem) hInteresting
  let higherNames : Finset (Fin V.card) :=
    higherGenerationStageNames original k g
  let higher : Fin higherNames.card → Fin V.card :=
    fun j => (higherNames.equivFin.symm j).1
  have hCover : ∀ v : Fin V.card,
      (∃ idx m : Nat, g < m ∧ m ≤ k ∧
        (original v).val = hPosition k idx m) →
      ∃ j : Fin higherNames.card, higher j = v := by
    intro v hv
    have hMember : v ∈ higherNames := by
      simpa only [higherNames, higherGenerationStageNames,
        Finset.mem_filter, Finset.mem_univ, true_and] using hv
    refine ⟨higherNames.equivFin ⟨v,hMember⟩,?_⟩
    simp [higher]
  exact numericH_selectedB3_generation_levels_card_le_higher_budget
    family K (by intro i; trivial) hAvoidK k N g hg
    original Selected levels hGeneration hFamilyBound hFailures
    higher hCover higherNames.card le_rfl

end Kk
