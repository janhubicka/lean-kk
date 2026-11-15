import Kk.PhysicalOffPlanFiniteIndex
import Mathlib.Tactic

/-!
# Track E E54: intrinsic finite support of physical off-plan exceptions

A finite, independently chosen *exact* index of a Kpt pre-cut source
is a representation of physical no-novelty, not additional geometry.
The quietness test is equivalent in both directions to the intrinsic
complete-terminal/full-dependent-L+ condition. Hence the minimal
set of off-plan bad cuts is independent of how the two true source
closures were finitely enumerated.

This does NOT construct a diary-uniform bound, normalization across
different Kpt trees, or the labelled inverse-source orbit.

English-first proof and 16 hostile checks:
docs/track_e_canonical_offplan_exception_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A one-cut finite physical quietness test. The terminal index
may change; each old/upper crossing PAIR must match on the same
old index, even at I2 forks. -/
def KptIndexedQuietAtCut
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool)
    (cut : Nat) : Prop :=
  (∀ j : Fin Q, newLive cut j = true →
    LevelTree.lev (newNode j) = cut →
    ∃ i : Fin P, oldLive cut i = true ∧
      LevelTree.lev (oldNode i) = cut) ∧
  IndexedPhysicalCrossing family newNode newLive cut ⊆
    IndexedPhysicalCrossing family oldNode oldLive cut

/-- EXACT finite source indices give an equivalence, not merely
one sufficient implication, between the finite live-node test
and intrinsic physical no-novelty at a cut. -/
theorem kptIndexedQuietAtCut_iff_physical
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldSource newSource : Set (AdmissibleKptNode family))
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool)
    (cut : Nat)
    (hExactOld : ∀ z : AdmissibleKptNode family,
      z ∈ oldSource ↔ ∃ i : Fin P,
        oldNode i = z ∧ oldLive cut i = true)
    (hExactNew : ∀ z : AdmissibleKptNode family,
      z ∈ newSource ↔ ∃ j : Fin Q,
        newNode j = z ∧ newLive cut j = true) :
    KptIndexedQuietAtCut family
        oldNode newNode oldLive newLive cut ↔
      NewRootNoNoveltyAtCut family oldSource newSource cut := by
  constructor
  · rintro ⟨hTerm,hPairs⟩
    constructor
    · rintro ⟨z,hNewZ,hLevel⟩
      obtain ⟨j,hNode,hLive⟩ := (hExactNew z).mp hNewZ
      obtain ⟨i,hOldLive,hOldLevel⟩ :=
        hTerm j hLive (by simpa only [hNode] using hLevel)
      exact ⟨oldNode i,
        (hExactOld (oldNode i)).mpr ⟨i,rfl,hOldLive⟩,
        hOldLevel⟩
    · intro p hp
      have hNewIndexed :
          p ∈ IndexedPhysicalCrossing
            family newNode newLive cut := by
        rw [indexed_physical_crossing_eq_full_closure_relation
          family newNode newLive newSource cut hExactNew]
        exact hp
      have hOldIndexed :
          p ∈ IndexedPhysicalCrossing
            family oldNode oldLive cut := hPairs hNewIndexed
      rw [indexed_physical_crossing_eq_full_closure_relation
        family oldNode oldLive oldSource cut hExactOld] at hOldIndexed
      exact hOldIndexed
  · intro hPhysical
    constructor
    · intro j hNewLive hNewLevel
      have hInNew : newNode j ∈ newSource :=
        (hExactNew (newNode j)).mpr ⟨j,rfl,hNewLive⟩
      obtain ⟨z,hInOld,hOldLevel⟩ :=
        hPhysical.1 ⟨newNode j,hInNew,hNewLevel⟩
      obtain ⟨i,hName,hOldLive⟩ := (hExactOld z).mp hInOld
      exact ⟨i,hOldLive,
        by simpa only [hName] using hOldLevel⟩
    · intro p hp
      have hNewPhysical :
          p ∈ FullPhysicalClosureCrossing
            family newSource cut := by
        rw [← indexed_physical_crossing_eq_full_closure_relation
          family newNode newLive newSource cut hExactNew]
        exact hp
      have hOldPhysical :
          p ∈ FullPhysicalClosureCrossing
            family oldSource cut := hPhysical.2 hNewPhysical
      rw [← indexed_physical_crossing_eq_full_closure_relation
        family oldNode oldLive oldSource cut hExactOld] at hOldPhysical
      exact hOldPhysical

/-- E53's original quantified finite off-plan condition equals
the concise pointwise QUIET predicate on precisely the old-boring
cuts outside the proposed Allowed mask. -/
theorem kptTwoIndexOffPlanNoNovelty_iff_quiet
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldSelected : Nat → Set Nat)
    (oldTop : Nat) (Allowed : Set Nat)
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool) :
    KptTwoIndexOffPlanNoNovelty family oldSelected oldTop
        Allowed oldNode newNode oldLive newLive ↔
      ∀ cut : Nat, cut < oldTop →
        cut ∉ oldSelected cut → cut ∉ Allowed →
        KptIndexedQuietAtCut family
          oldNode newNode oldLive newLive cut := by
  constructor
  · intro hFinite cut hCut hOldSkip hOffPlan
    constructor
    · exact hFinite.1 cut hCut hOldSkip hOffPlan
    · intro p hp
      obtain ⟨j,hLive,hOld,hUpper⟩ := hp
      exact hFinite.2 cut hCut hOldSkip hOffPlan
        j hLive p.1 p.2 hOld hUpper
  · intro hQuiet
    constructor
    · intro cut hCut hOldSkip hOffPlan j hLive hLev
      exact (hQuiet cut hCut hOldSkip hOffPlan).1 j hLive hLev
    · intro cut hCut hOldSkip hOffPlan j hLive T U hOld hUpper
      change (T,U) ∈ IndexedPhysicalCrossing
        family oldNode oldLive cut
      exact (hQuiet cut hCut hOldSkip hOffPlan).2
        (⟨j,hLive,hOld,hUpper⟩ :
          (T,U) ∈ IndexedPhysicalCrossing
            family newNode newLive cut)

/-- The least finite set of old-boring source-coordinate cuts at
which the full two-index physical no-novelty test fails. It does
not depend on an externally chosen diary Allowed set. -/
noncomputable def kptCanonicalOffPlanBadCuts
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldSelected : Nat → Set Nat)
    (oldTop : Nat)
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool) : Finset Nat := by
  classical
  exact (Finset.range oldTop).filter
    (fun cut => cut ∉ oldSelected cut ∧
      ¬ KptIndexedQuietAtCut
        family oldNode newNode oldLive newLive cut)

/-- Membership has NO existential choice of a finite enumeration;
it is exactly the old-boring failure of full physical quietness. -/
theorem mem_kptCanonicalOffPlanBadCuts
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldSelected : Nat → Set Nat)
    (oldTop : Nat)
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool)
    (cut : Nat) :
    cut ∈ kptCanonicalOffPlanBadCuts family oldSelected
        oldTop oldNode newNode oldLive newLive ↔
      cut < oldTop ∧ cut ∉ oldSelected cut ∧
        ¬ KptIndexedQuietAtCut family
          oldNode newNode oldLive newLive cut := by
  classical
  simp only [kptCanonicalOffPlanBadCuts,
    Finset.mem_filter, Finset.mem_range]
  tauto

/-- The physical off-plan tests hold outside Allowed if and only if
the canonical finite bad-cut set is INCLUDED in Allowed. Thus the
canonical set is the LEAST such Allowed set. -/
theorem kptTwoIndexOffPlanNoNovelty_iff_badCuts_subset
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldSelected : Nat → Set Nat)
    (oldTop : Nat) (Allowed : Set Nat)
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool) :
    KptTwoIndexOffPlanNoNovelty family oldSelected
        oldTop Allowed oldNode newNode oldLive newLive ↔
      ∀ cut : Nat,
        cut ∈ kptCanonicalOffPlanBadCuts family oldSelected
          oldTop oldNode newNode oldLive newLive →
        cut ∈ Allowed := by
  classical
  rw [kptTwoIndexOffPlanNoNovelty_iff_quiet]
  constructor
  · intro hQuiet cut hBad
    obtain ⟨hCut,hOldSkip,hNotQuiet⟩ :=
      (mem_kptCanonicalOffPlanBadCuts
        family oldSelected oldTop oldNode newNode
        oldLive newLive cut).mp hBad
    by_contra hNotAllowed
    exact hNotQuiet (hQuiet cut hCut hOldSkip hNotAllowed)
  · intro hCovered cut hCut hOldSkip hNotAllowed
    by_contra hNotQuiet
    have hBad : cut ∈ kptCanonicalOffPlanBadCuts
        family oldSelected oldTop oldNode newNode
        oldLive newLive :=
      (mem_kptCanonicalOffPlanBadCuts
        family oldSelected oldTop oldNode newNode
        oldLive newLive cut).mpr
          ⟨hCut,hOldSkip,hNotQuiet⟩
    exact hNotAllowed (hCovered cut hBad)

/-- Once the two indices EXACTLY represent actual pre-cut sources,
membership in the finite bad-cut set is intrinsic: it is failure
of the physical no-novelty predicate at an old-boring cut. -/
theorem mem_kptCanonicalOffPlanBadCuts_iff_physical
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldSelected : Nat → Set Nat) (oldTop : Nat)
    (oldSource newSource : Nat → Set (AdmissibleKptNode family))
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool)
    (hExactOld : ∀ cut : Nat, cut < oldTop →
      ∀ z : AdmissibleKptNode family,
        z ∈ oldSource cut ↔
        ∃ i : Fin P, oldNode i = z ∧ oldLive cut i = true)
    (hExactNew : ∀ cut : Nat, cut < oldTop →
      ∀ z : AdmissibleKptNode family,
        z ∈ newSource cut ↔
        ∃ j : Fin Q, newNode j = z ∧ newLive cut j = true)
    (cut : Nat) :
    cut ∈ kptCanonicalOffPlanBadCuts family oldSelected
        oldTop oldNode newNode oldLive newLive ↔
      cut < oldTop ∧ cut ∉ oldSelected cut ∧
        ¬ NewRootNoNoveltyAtCut family
          (oldSource cut) (newSource cut) cut := by
  constructor
  · intro hBad
    obtain ⟨hCut,hOldSkip,hNotQuiet⟩ :=
      (mem_kptCanonicalOffPlanBadCuts
        family oldSelected oldTop oldNode newNode
        oldLive newLive cut).mp hBad
    refine ⟨hCut,hOldSkip,?_⟩
    intro hPhysical
    exact hNotQuiet
      ((kptIndexedQuietAtCut_iff_physical
        family (oldSource cut) (newSource cut)
        oldNode newNode oldLive newLive cut
        (hExactOld cut hCut) (hExactNew cut hCut)).mpr hPhysical)
  · rintro ⟨hCut,hOldSkip,hNotPhysical⟩
    apply (mem_kptCanonicalOffPlanBadCuts
      family oldSelected oldTop oldNode newNode
      oldLive newLive cut).mpr
    refine ⟨hCut,hOldSkip,?_⟩
    intro hQuiet
    exact hNotPhysical
      ((kptIndexedQuietAtCut_iff_physical
        family (oldSource cut) (newSource cut)
        oldNode newNode oldLive newLive cut
        (hExactOld cut hCut) (hExactNew cut hCut)).mp hQuiet)

/-- Two completely different exhaustive finite enumerations of the
SAME physical source families compute IDENTICAL bad-cut supports.
No common finite index, bijection or node-name identification is
required. This does NOT compare different diary occurrences. -/
theorem kptCanonicalOffPlanBadCuts_index_independent
    {db du dd P Q P' Q' : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldSelected : Nat → Set Nat) (oldTop : Nat)
    (oldSource newSource : Nat → Set (AdmissibleKptNode family))
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool)
    (oldNode' : Fin P' → AdmissibleKptNode family)
    (newNode' : Fin Q' → AdmissibleKptNode family)
    (oldLive' : Nat → Fin P' → Bool)
    (newLive' : Nat → Fin Q' → Bool)
    (hExactOld : ∀ cut : Nat, cut < oldTop →
      ∀ z : AdmissibleKptNode family,
        z ∈ oldSource cut ↔
        ∃ i : Fin P, oldNode i = z ∧ oldLive cut i = true)
    (hExactNew : ∀ cut : Nat, cut < oldTop →
      ∀ z : AdmissibleKptNode family,
        z ∈ newSource cut ↔
        ∃ j : Fin Q, newNode j = z ∧ newLive cut j = true)
    (hExactOld' : ∀ cut : Nat, cut < oldTop →
      ∀ z : AdmissibleKptNode family,
        z ∈ oldSource cut ↔
        ∃ i : Fin P', oldNode' i = z ∧ oldLive' cut i = true)
    (hExactNew' : ∀ cut : Nat, cut < oldTop →
      ∀ z : AdmissibleKptNode family,
        z ∈ newSource cut ↔
        ∃ j : Fin Q', newNode' j = z ∧ newLive' cut j = true) :
    kptCanonicalOffPlanBadCuts family oldSelected
      oldTop oldNode newNode oldLive newLive =
    kptCanonicalOffPlanBadCuts family oldSelected
      oldTop oldNode' newNode' oldLive' newLive' := by
  ext cut
  rw [mem_kptCanonicalOffPlanBadCuts_iff_physical
      family oldSelected oldTop oldSource newSource
      oldNode newNode oldLive newLive
      hExactOld hExactNew cut,
    mem_kptCanonicalOffPlanBadCuts_iff_physical
      family oldSelected oldTop oldSource newSource
      oldNode' newNode' oldLive' newLive'
      hExactOld' hExactNew' cut]

/-- Apply E53 with the *least* physical exception set as Allowed:
there is no externally imposed unverified off-plan coverage premise.
The support remains realization-dependent and is NOT a diary-uniform
upper bound on BRD or on full labelled inverse-source types. -/
theorem crossheight_old_range_sandwich_of_canonical_badCuts
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (oldTop newTop : Nat) (hTopLe : oldTop ≤ newTop)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = oldTop)
    (RunOld : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (RunNew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y newTop)
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool)
    (hExactOld : ∀ cut : Nat, cut < oldTop →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (RunOld.I (cut+1)) X ↔
        ∃ i : Fin P, oldNode i = z ∧ oldLive cut i = true)
    (hExactNew : ∀ cut : Nat, cut < oldTop →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (RunNew.I (cut+1)) Y ↔
        ∃ j : Fin Q, newNode j = z ∧ newLive cut j = true) :
    ∀ i : Nat, i ≤ oldTop →
      (RunOld.I i ⊆ RunNew.I i) ∧
      ({q : Nat | q ∈ RunNew.I i ∧ q ≤ oldTop} ⊆
        RunOld.I i ∪
          {q : Nat |
            q ∈ kptCanonicalOffPlanBadCuts family RunOld.I oldTop
              oldNode newNode oldLive newLive ∧ i ≤ q}) := by
  let Bad : Set Nat := {q | q ∈
    kptCanonicalOffPlanBadCuts family RunOld.I oldTop
      oldNode newNode oldLive newLive}
  have hCoverage : KptTwoIndexOffPlanNoNovelty family RunOld.I
      oldTop Bad oldNode newNode oldLive newLive :=
    (kptTwoIndexOffPlanNoNovelty_iff_badCuts_subset
      family RunOld.I oldTop Bad oldNode newNode
      oldLive newLive).mpr (by intro cut hBad; exact hBad)
  have hSandwich :=
    crossheight_old_range_sandwich_of_two_finite_offplan_indices
      family X Y hXY oldTop newTop hTopLe hTopSeed
      RunOld RunNew Bad oldNode newNode oldLive newLive
      hExactOld hExactNew hCoverage
  simpa only [Bad, Set.mem_setOf_eq] using hSandwich

end Kk
