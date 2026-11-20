import Kk.TrackGExactBoringRunTransport
import Mathlib.Tactic

/-!
# Track G: the exact (not merely sufficient) finite support of old-factor obstructions

English proof and nineteen adversarial checks committed FIRST:
docs/track_g_exact_factor_badcuts_english_audit_20261120.md

An actual old Kpt AlgorithmRun and a single independently EXACT finite
index of the enlarged candidate full pre-cut Kpt closure suffice for
an intrinsic finite set of OLD-BORING cuts preventing transport of
the entire selected I and total monoid-valued F functions.

Unlike the earlier E54 canonical *no-novelty* Bad set, this is exact:
zero factor-Bad iff an actual synchronized Y-run EXISTS. It permits
extra full dependent L+/E crossings as long as they obey the UNIQUE
old total step factor. All true terminal and same-component I2 meet
events are checked independently.

The finite indices are physical Kpt nodes (not selected graph ages).
A classically filtered Finset does NOT mean an executable decision
procedure for monoid maps; no bound independent of the physical
finite stage, coherent labelled inverse source or sharp BRD is proved.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

/-- A one-cut COMPLETE finite target Kpt index is compatible with
the original chosen total monoid F-step exactly when it has
no I1 terminal, no actual same-component I2 meet, and every
genuine total MMap factor of the old total F endpoints respects
every new live Kpt crossing ancestor.

At an old-boring cut the old run supplies such a factor, and
total left cancellation makes it UNIQUE. In particular the
universal quantifier over D is not vacuous or a new choice. -/
def KptIndexedOldFactorCompatibleAt
    {db du dd Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (newNode : Fin Q → AdmissibleKptNode family)
    (newLive : Nat → Fin Q → Bool)
    (cut : Nat) : Prop :=
  (∀ j : Fin Q, newLive cut j = true →
    LevelTree.lev (newNode j) ≠ cut) ∧
  (∀ j k : Fin Q,
    newLive cut j = true → newLive cut k = true →
    ¬ (SMTree.Envelope.SameComponent (newNode j) (newNode k) ∧
      LevelTree.lev (LevelTree.meet (newNode j) (newNode k)) = cut)) ∧
  (∀ D : MMap (normalizedKptSMTree family),
    RX.F cut =
      MMap.comp (normalizedKptSMTree family) (RX.F (cut+1)) D →
    ∀ j : Fin Q, newLive cut j = true →
      ∀ (hCross : cut < LevelTree.lev (newNode j)),
        D (LevelTree.ancestor (newNode j) cut (Nat.le_of_lt hCross)) =
          LevelTree.ancestor (newNode j) (cut+1)
            (Nat.succ_le_iff.mpr hCross))

/-- Exactly those OLD-BORING cut coordinates at which the
complete candidate Kpt finite index fails the sharp old
total-factor compatibility criterion.

Its cardinality is finite because top is finite, not because
a uniform diary-level complexity bound has been proved. -/
noncomputable def kptExactOldFactorBadCuts
    {db du dd Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (newNode : Fin Q → AdmissibleKptNode family)
    (newLive : Nat → Fin Q → Bool) : Finset Nat := by
  classical
  exact (Finset.range top).filter (fun cut =>
    ¬ SMTree.Envelope.IsInterestingAt (normalizedKptSMTree family)
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (RX.I (cut+1)) X) cut ∧
    ¬ KptIndexedOldFactorCompatibleAt
      family X top RX newNode newLive cut)

/-- Exact intrinsic membership description of finite old-factor
Bad support; selected interesting cuts are never counted. -/
theorem mem_kptExactOldFactorBadCuts
    {db du dd Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (newNode : Fin Q → AdmissibleKptNode family)
    (newLive : Nat → Fin Q → Bool)
    (cut : Nat) :
    cut ∈ kptExactOldFactorBadCuts
      family X top RX newNode newLive ↔
    cut < top ∧
      ¬ SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family)
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) X) cut ∧
      ¬ KptIndexedOldFactorCompatibleAt
        family X top RX newNode newLive cut := by
  classical
  simp only [kptExactOldFactorBadCuts,
    Finset.mem_filter, Finset.mem_range]

/-- SHARP iff: for X ⊆ Y, one actual RX on X and an independently
EXACT full Kpt source index on Y along RX.I tails, the finite
old-factor Bad set is empty if and ONLY if one real AlgorithmRun
on Y exists with exactly the SAME selected I function AND
the SAME TOTAL monoid-valued F function.

One target full source index suffices: no old finite index,
no source-name bijection, no E1 and no equal crossing spectra.
The Finset may be noncomputable; this is a precise mathematical
support certificate, not an executable algorithm. -/
theorem kpt_exact_factor_BadCuts_empty_iff_wholeRun_transport
    {db du dd Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (newNode : Fin Q → AdmissibleKptNode family)
    (newLive : Nat → Fin Q → Bool)
    (hExactY : ∀ cut : Nat, cut < top →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (RX.I (cut+1)) Y ↔
        ∃ j : Fin Q, newNode j = z ∧ newLive cut j = true) :
    kptExactOldFactorBadCuts family X top RX
      newNode newLive = ∅ ↔
    ∃ RY : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family) Y top,
      RY.I = RX.I ∧ RY.F = RX.F := by
  classical
  constructor
  · intro hEmpty
    apply (actualRun_transport_iff_old_boring_original_factor_extends
      (normalizedKptSMTree family) X Y hXY top RX).mpr
    intro cut hCut hOldBoring
    have hCompatible : KptIndexedOldFactorCompatibleAt
        family X top RX newNode newLive cut := by
      by_contra hNot
      have hBad :
          cut ∈ kptExactOldFactorBadCuts
            family X top RX newNode newLive :=
        (mem_kptExactOldFactorBadCuts
          family X top RX newNode newLive cut).mpr
          ⟨hCut,hOldBoring,hNot⟩
      rw [hEmpty] at hBad
      simp at hBad
    obtain ⟨hNoTerminal,hNoMeet,hFactor⟩ := hCompatible
    refine ⟨?_,?_,?_⟩
    · rintro ⟨z,hz,hLev⟩
      obtain ⟨j,hName,hLive⟩ :=
        (hExactY cut hCut z).mp hz
      exact (hNoTerminal j hLive) (by
        simpa only [hName] using hLev)
    · rintro ⟨a,ha,b,hb,hSame,hMeet⟩
      obtain ⟨j,hJa,hJLive⟩ :=
        (hExactY cut hCut a).mp ha
      obtain ⟨k,hKb,hKLive⟩ :=
        (hExactY cut hCut b).mp hb
      apply (hNoMeet j k hJLive hKLive)
      constructor
      · simpa only [hJa,hKb] using hSame
      · simpa only [hJa,hKb] using hMeet
    · intro D _hSkip _hOldCross hFactorD z hz hCrossZ
      obtain ⟨j,hName,hLive⟩ :=
        (hExactY cut hCut z).mp hz
      have hCrossJ : cut < LevelTree.lev (newNode j) := by
        simpa only [hName] using hCrossZ
      have hAt := hFactor D hFactorD j hLive hCrossJ
      simpa only [hName] using hAt
  · intro hTransport
    apply Finset.ext
    intro cut
    constructor
    · intro hBad
      exfalso
      obtain ⟨hCut,hOldBoring,hNotCompat⟩ :=
        (mem_kptExactOldFactorBadCuts
          family X top RX newNode newLive cut).mp hBad
      apply hNotCompat
      have hPhysical :=
        (actualRun_transport_iff_old_boring_original_factor_extends
          (normalizedKptSMTree family) X Y hXY top RX).mp
          hTransport cut hCut hOldBoring
      obtain ⟨hNoI1,hNoI2,hOldFactorExtension⟩ := hPhysical
      refine ⟨?_,?_,?_⟩
      · intro j hLive hLev
        have hj :
            newNode j ∈ SMTree.Envelope.closure
              (admissibleKptSTree family) (RX.I (cut+1)) Y :=
          (hExactY cut hCut (newNode j)).mpr
            ⟨j,rfl,hLive⟩
        exact hNoI1 ⟨newNode j,hj,hLev⟩
      · intro j k hjLive hkLive hMeetData
        have hj :
            newNode j ∈ SMTree.Envelope.closure
              (admissibleKptSTree family) (RX.I (cut+1)) Y :=
          (hExactY cut hCut (newNode j)).mpr
            ⟨j,rfl,hjLive⟩
        have hk :
            newNode k ∈ SMTree.Envelope.closure
              (admissibleKptSTree family) (RX.I (cut+1)) Y :=
          (hExactY cut hCut (newNode k)).mpr
            ⟨k,rfl,hkLive⟩
        exact hNoI2
          ⟨newNode j,hj,newNode k,hk,
            hMeetData.1,hMeetData.2⟩
      · intro D hFactorD j hLive hCross
        obtain ⟨E,hSkipE,hCrossE,_hOldI,hFactorE⟩ :=
          RX.noninteresting_step cut hCut hOldBoring
        have hDE : D = E :=
          kpt_MMap_comp_left_cancel
            (normalizedKptSMTree family) (RX.F (cut+1)) D E
            (hFactorD.symm.trans hFactorE)
        have hj :
            newNode j ∈ SMTree.Envelope.closure
              (admissibleKptSTree family) (RX.I (cut+1)) Y :=
          (hExactY cut hCut (newNode j)).mpr
            ⟨j,rfl,hLive⟩
        have hE :=
          hOldFactorExtension E hSkipE hCrossE hFactorE
            (newNode j) hj hCross
        simpa only [hDE] using hE
    · intro hEmpty
      simpa using hEmpty

end Kk
