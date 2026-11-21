import Kk.TrackDOddStageNoFreeEnd
import Kk.TrackEOriginalPrefixSocleCover
import Kk.TrackEOneBareRootEvenRealNoNovelty
import Kk.TrackEOldBoringBareRootNoSeed
import Kk.TrackDPhysicalHSymmetry
import Mathlib.Tactic

/-!
# Track E E83: safe odd source no-novelty with full OLD Kpt socle witnesses

English proof and 24 hostile checks committed FIRST:
docs/track_e_odd_safe_zero_source_no_novelty_english_audit_20261121.md

The ACTUAL numerical-H+ ordinary-L source row at odd c=2a+1
is identically zero. An OLD-BORING actual run excludes OLD
initial seed terminals, while the absence of ANY true original
stage E-free endpoint at c also excludes the one new BARE
original seed terminal (newV is in the root original pool U).

Track D's verified odd full I1 theorem eliminates ALL generated
meet and E-parameter terminals under this same E-free endpoint
condition. E74/E72 match EVERY complete old/upper dependent L+/E
crossing through complete OLD Kpt ancestor witnesses.

This is conditional physical no-novelty at one odd source cut:
stage free-end exclusion and active-original old Kpt prefix
witnesses are NOT proved for the resolved diary. A genuine
odd E-parameter terminal may be interesting; it cannot be
silently skipped. No target AlgorithmRun is an input.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- EVERY physical ordinary-L original at an actual ODD source
cut has zero cut bit, including all actual eligible originals
of the maintained full stage U ∪ positiveSelected(J).

This uses the genuine numerical-H+ binary generator; the
auxiliary directed E relation is NOT symmetrized or discarded. -/
theorem finiteNumericH_odd_full_original_stage_zero
    (E : Nat → Nat → Bool) (k N a : Nat)
    (U : Finset (Fin N)) (J : Set Nat) :
    ∀ v : Fin N,
      v ∈ hStageOriginals (normalizedGraphModel E) k N U J →
      (2*a+1)+1 ≤
        (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val →
      (finiteNumericH (normalizedGraphModel E) k N).L.binary
        (2*a+1) v.val (0 : Fin 1) = false := by
  intro v _hStage _hFree
  change hNumericBinary (normalizedGraphModel E).binary k
    (2*a+1) v.val (0 : Fin 1) = false
  exact hNumericBinary_odd_left_false
    (normalizedGraphModel E).binary k a v.val (0 : Fin 1)

/-- In ONE true old-boring AlgorithmRun, adding ONE literal
physical bare original O_new to initial old seeds X cannot
introduce an INITIAL seed terminal at ODD cut 2a+1 if no
ACTUAL stage original has its canonical auxiliary E-free end
at this cut. The initial X may contain dependent Kpt seeds.

The new original belongs to U, hence to the true stage pool.
Odd parity alone is insufficient: the no-free-end premise
is essential, even for the new bare original. -/
theorem finiteNumericH_old_boring_one_bare_root_odd_no_initial_seed
    (family : List (NormalizedForbidden 1 0 1))
    (E : Nat → Nat → Bool) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (newV : Fin N) (hNewInU : newV ∈ U)
    (hBare : Y = X ∪
      ({(finiteNumericH (normalizedGraphModel E) k N).kptOriginal family hAvoid newV} :
        Set (AdmissibleKptNode family)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (a : Nat)
    (hBoring : ¬ SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family)
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I ((2*a+1)+1)) X) (2*a+1))
    (hNoStageEnd : ∀ v : Fin N,
      v ∈ ambientStagePool
        (finiteNumericH (normalizedGraphModel E) k N)
        (U : Set (Fin N)) (R.I ((2*a+1)+1)) →
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val
        ≠ 2*a+1) :
    ¬ ∃ z : AdmissibleKptNode family,
      z ∈ Y ∧ LevelTree.lev z = 2*a+1 := by
  have hNoOld :
      ¬ ∃ x : AdmissibleKptNode family,
        x ∈ X ∧ LevelTree.lev x = 2*a+1 :=
    kpt_old_actual_boring_no_initial_seed_at_cut
      family X top (2*a+1) R hBoring
  have hNewStage :
      newV ∈ ambientStagePool
        (finiteNumericH (normalizedGraphModel E) k N)
        (U : Set (Fin N)) (R.I ((2*a+1)+1)) := by
    exact Or.inl (Finset.mem_coe.mpr hNewInU)
  have hNoNew :
      LevelTree.lev
        ((finiteNumericH (normalizedGraphModel E) k N).kptOriginal
          family hAvoid newV) ≠ 2*a+1 := by
    change (finiteNumericH (normalizedGraphModel E) k N).freeLevel
      newV.val ≠ 2*a+1
    exact hNoStageEnd newV hNewStage
  rintro ⟨z,hYz,hLev⟩
  rw [hBare] at hYz
  rcases hYz with hOld | hNew
  · exact hNoOld ⟨z,hOld,hLev⟩
  · have hzEq :
        z = (finiteNumericH (normalizedGraphModel E) k N).kptOriginal
          family hAvoid newV := by
      simpa only [Set.mem_singleton_iff] using hNew
    rw [hzEq] at hLev
    exact hNoNew hLev

/-- Actual complete physical NEW->OLD quietness at a genuinely
OLD-BORING ODD numerical-H+ source cut 2a+1.

Hypotheses:
  (F) NO ACTUAL stage original in U∪selected(R.I(c+1)) ends its
      canonical AUXILIARY E-free cut at c;
  (P) complete OLD Kpt source-socle coverage for every NEW-LIVE
      crossing, supplied by genuine active-original old prefixes.

The ordinary L ZERO-column hypothesis is AUTOMATIC at odd cuts,
and the new initial seed exclusion follows from old-boringness
plus (F) even if X contains dependent initial Kpt nodes.
The verified Track D theorem eliminates all GENERATED I1
terminals; E72 gives complete dependent old/upper L+/E crossing
inclusion even with I2 forks.

This theorem does NOT assert that any particular resolved-Q
odd source cut satisfies (F) or (P), or that all odd cuts are
boring. It constructs NO target AlgorithmRun by itself. -/
theorem finiteNumericH_old_boring_one_bare_root_odd_noNovelty
    (family : List (NormalizedForbidden 1 0 1))
    (E : Nat → Nat → Bool)
    (hGraphSym : ∀ i j, E i j = E j i)
    (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family
      (finiteNumericH (normalizedGraphModel E) k N)
      hAvoid (U : Set (Fin N)))
    (newV : Fin N) (hNewInU : newV ∈ U)
    (hBare : Y = X ∪
      ({(finiteNumericH (normalizedGraphModel E) k N).kptOriginal family hAvoid newV} :
        Set (AdmissibleKptNode family)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (a : Nat)
    (hBoring : ¬ SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family)
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I ((2*a+1)+1)) X) (2*a+1))
    (hNoStageEnd : ∀ v : Fin N,
      v ∈ ambientStagePool
        (finiteNumericH (normalizedGraphModel E) k N)
        (U : Set (Fin N)) (R.I ((2*a+1)+1)) →
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val
        ≠ 2*a+1)
    (hOldPrefix : KptCandidateOriginalOldPrefixCovered
      family (normalizedGraphModel E) k N
      hAvoid U X Y top R (2*a+1)) :
    NewRootNoNoveltyAtCut family
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I ((2*a+1)+1)) X)
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I ((2*a+1)+1)) Y)
      (2*a+1) := by
  let K : AgeTestModel 1 0 1 := normalizedGraphModel E
  let A : EnumeratedPartialStructure 1 0 1 := finiteNumericH K k N
  let cut : Nat := 2*a+1
  have hXY : X ⊆ Y := by
    rw [hBare]
    intro z hz
    exact Or.inl hz
  have hY : Y ⊆ ambientPrefixPool family A hAvoid
      (U : Set (Fin N)) := by
    rw [hBare]
    exact finiteNumericH_one_bare_root_stays_in_original_prefix_pool
      family K k N hAvoid U X hX newV hNewInU
  have hSymA : ∀ i j : Nat,
      A.L.binary i j (0 : Fin 1) =
        A.L.binary j i (0 : Fin 1) :=
    finiteNumericH_graph_ordinary_L_symmetric E hGraphSym k N
  have hNoSeed :
      ¬ ∃ z : AdmissibleKptNode family,
        z ∈ Y ∧ LevelTree.lev z = cut :=
    finiteNumericH_old_boring_one_bare_root_odd_no_initial_seed
      family E k N hAvoid U X Y newV hNewInU hBare
      top R a hBoring hNoStageEnd
  have hNoI1 : ¬ KptI1AtCut family
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1)) Y) cut := by
    change ¬ ∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1)) Y ∧ LevelTree.lev z = cut
    exact finiteNumericH_odd_no_full_I1_of_no_seed_or_stage_free
      family K k N hAvoid hSymA (R.I (cut+1)) Y
      (U : Set (Fin N)) hY a hNoSeed hNoStageEnd
  have hZeroStage : ∀ v : Fin N,
      v ∈ hStageOriginals K k N U (R.I (cut+1)) →
      cut+1 ≤ A.freeLevel v.val →
      A.L.binary cut v.val (0 : Fin 1) = false :=
    finiteNumericH_odd_full_original_stage_zero
      E k N a U (R.I (cut+1))
  have hOldSocle :=
    finiteNumericH_candidate_old_socle_of_active_original_prefixes
      family K k N hAvoid U X Y hY top R cut hOldPrefix
  exact finiteNumericH_candidate_zero_stage_noNovelty_of_socle_and_noI1
    family K k N hAvoid hSymA U X Y hXY hY top R
    cut hZeroStage hOldSocle hNoI1

end Kk
