import Kk.TrackEEvenRealZeroSocleNoNovelty
import Kk.TrackEOriginalPrefixSocleCover
import Kk.TrackEOldBoringBareRootNoSeed
import Mathlib.Tactic

/-!
# Track E E77: one physical bare-root source extension at an OLD-BORING real cut

English-first proof and 23 hostile checks:
docs/track_e_one_bare_root_even_real_certificate_english_audit_20261120.md

The only new initial seed is ONE actual complete finite numerical-H+
original O_new; the old X may contain legitimate dependent Kpt seeds.
The genuine OLD run R supplies the true selected tail R.I(cut+1).

At a positive even-real OLD-BORING cut, E76 makes the initial new-seed
terminal condition AUTOMATIC. E74 reduces full old Kpt source-socle
coverage to source-exact prefix matching for the physically ACTIVE
stage original names, without enumerating auxiliary meet/parameter
Kpt nodes. Track D plus E72/E73 then removes all generated terminals
and matches every complete old/upper dependent L+/E crossing pair
provided the entire genuine stage original cut column is zero.

This is a conditional one-cut theorem: original-prefix matching
and the true full-stage zero cut column remain geometric hypotheses.
No synchronized whole run, source orbit, diary-uniform carrier or
upper big Ramsey degree is asserted.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- One original-coordinate COMPLETE OLD Kpt prefix certificate.
Each actual stage original that represents at least one NEW live
candidate crossing has one actual old-live source witness for the
literal entire Kpt cut ancestor, including auxiliary E and
negative ordinary L data.

This definition is deliberately NOT just equality of graph ages,
and it does not require the original itself to be a live Kpt
closure node. -/
def KptCandidateOriginalOldPrefixCovered
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (cut : Nat) : Prop :=
  ∀ v : Fin N,
    v ∈ hStageOriginals K k N U (R.I (cut+1)) →
    (∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y ∧
      cut < LevelTree.lev z ∧
      z ≤ (finiteNumericH K k N).kptOriginal family hAvoid v) →
    ∃ w : AdmissibleKptNode family,
      w ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X ∧
      ∃ (hVCross : cut < LevelTree.lev
        ((finiteNumericH K k N).kptOriginal family hAvoid v))
        (hWCross : cut < LevelTree.lev w),
        LevelTree.ancestor
          ((finiteNumericH K k N).kptOriginal family hAvoid v)
          cut (Nat.le_of_lt hVCross) =
        LevelTree.ancestor w cut (Nat.le_of_lt hWCross)

/-- A TRUE bare-root enlargement is represented in the SAME
finite numerical-H+ original-prefix pool provided the newly
adjoined physical original name belongs to that pool.
No larger arbitrary prefix seed set, new AlgorithmRun or
auxiliary source list is required. -/
theorem finiteNumericH_one_bare_root_stays_in_original_prefix_pool
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid (U : Set (Fin N)))
    (newV : Fin N) (hNewInU : newV ∈ U) :
    X ∪ ({(finiteNumericH K k N).kptOriginal family hAvoid newV} :
        Set (AdmissibleKptNode family)) ⊆
      ambientPrefixPool family (finiteNumericH K k N)
        hAvoid (U : Set (Fin N)) := by
  intro z hz
  rcases hz with hOld | hNew
  · exact hX hOld
  · have hEq :
        z = (finiteNumericH K k N).kptOriginal family hAvoid newV := by
      simpa only [Set.mem_singleton_iff] using hNew
    subst z
    exact ⟨(finiteNumericH K k N).kptOriginal family hAvoid newV,
      ⟨newV, hNewInU, rfl⟩, le_rfl⟩

/-- Complete PHYSICAL no-novelty for ONE actual bare new-root
extension at a genuinely old-boring positive EVEN REAL H+ cut.

The initial new-seed I1 exclusion is DERIVED from the old run
and physical original parity (E76), not an assumption. The
full generated meet/parameter I1 exclusion follows from Track
D's exact even-real theorem; all paired dependent upper L+/E
crossings follow via E74's ACTUAL original old-prefix tests
and E72's zero-column next-type uniqueness.

The two genuine unresolved application checks are exactly:
  (Z) all eligible physical stage-original ordinary-L cut bits zero,
  (P) one old COMPLETE Kpt-prefix witness for each ACTIVE original.
No new AlgorithmRun on Y or finite Kpt auxiliary-node index
is assumed. The theorem is cut-LOCAL, not whole-run transport. -/
theorem finiteNumericH_old_boring_one_bare_root_even_real_noNovelty
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
      ({(finiteNumericH (normalizedGraphModel E) k N).kptOriginal
        family hAvoid newV} : Set (AdmissibleKptNode family)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (cut idx g : Nat)
    (hReal : cut = hPosition k idx g)
    (hPos : 0 < cut)
    (_hCut : cut < top)
    (hBoring : ¬ SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family)
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1)) X) cut)
    (hZeroStage : ∀ v : Fin N,
      v ∈ hStageOriginals (normalizedGraphModel E) k N U
        (R.I (cut+1)) →
      cut+1 ≤ (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val →
      (finiteNumericH (normalizedGraphModel E) k N).L.binary
        cut v.val (0 : Fin 1) = false)
    (hOldPrefix : KptCandidateOriginalOldPrefixCovered
      family (normalizedGraphModel E) k N hAvoid U X Y top R cut) :
    NewRootNoNoveltyAtCut family
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1)) X)
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1)) Y)
      cut := by
  subst cut
  have hXY : X ⊆ Y := by
    rw [hBare]
    intro z hz
    exact Or.inl hz
  have hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH (normalizedGraphModel E) k N)
      hAvoid (U : Set (Fin N)) := by
    rw [hBare]
    exact finiteNumericH_one_bare_root_stays_in_original_prefix_pool
      family (normalizedGraphModel E) k N hAvoid
      U X hX newV hNewInU
  have hNoNewSeed :
      ¬ ∃ z : AdmissibleKptNode family,
        z ∈ Y ∧
        LevelTree.lev z = hPosition k idx g := by
    rw [hBare]
    exact finiteNumericH_oldBoring_bare_root_no_positive_real_seed
      family (normalizedGraphModel E) k N
      hAvoid X top R newV idx g hPos hBoring
  have hOldSocle :=
    finiteNumericH_candidate_old_socle_of_active_original_prefixes
      family (normalizedGraphModel E) k N
      hAvoid U X Y hY top R
      (hPosition k idx g) hOldPrefix
  exact finiteNumericH_graph_even_real_candidate_noNovelty_of_zero_socle
    family E hGraphSym k N hAvoid
    U X Y hXY hY top R idx g
    hPos hNoNewSeed hZeroStage hOldSocle

/-- In the actual algorithmic OFF-PLAN case, literal
nonselection c∉R.I(c) (for c<top) gives genuine old-boringness
by the REAL AlgorithmRun interesting_step equation. Thus the
one-bare-original positive even-real physical no-novelty
certificate reduces to its zero full stage column and active
physical original old-prefix witnesses, with no extra I1
or new-run hypothesis. -/
theorem finiteNumericH_old_unselected_one_bare_root_even_real_noNovelty
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
      ({(finiteNumericH (normalizedGraphModel E) k N).kptOriginal
        family hAvoid newV} : Set (AdmissibleKptNode family)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (cut idx g : Nat)
    (hReal : cut = hPosition k idx g)
    (hPos : 0 < cut)
    (hCut : cut < top)
    (hNotSelected : cut ∉ R.I cut)
    (hZeroStage : ∀ v : Fin N,
      v ∈ hStageOriginals (normalizedGraphModel E) k N U
        (R.I (cut+1)) →
      cut+1 ≤ (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val →
      (finiteNumericH (normalizedGraphModel E) k N).L.binary
        cut v.val (0 : Fin 1) = false)
    (hOldPrefix : KptCandidateOriginalOldPrefixCovered
      family (normalizedGraphModel E) k N hAvoid U X Y top R cut) :
    NewRootNoNoveltyAtCut family
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1)) X)
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1)) Y)
      cut := by
  have hBoring : ¬ SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family)
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X) cut := by
    intro hInteresting
    have hStep := (R.interesting_step cut hCut hInteresting).1
    apply hNotSelected
    rw [hStep]
    simp
  exact finiteNumericH_old_boring_one_bare_root_even_real_noNovelty
    family E hGraphSym k N hAvoid
    U X Y hX newV hNewInU hBare top R
    cut idx g hReal hPos hCut hBoring hZeroStage hOldPrefix

end Kk
