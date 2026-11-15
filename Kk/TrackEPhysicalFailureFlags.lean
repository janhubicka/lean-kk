import Kk.TrackECanonicalBadCutSupport
import Mathlib.Tactic

/-!
# Track E E55: two complete physical failure flags determine bad-cut support

Under exact finite Kpt source indexing, E54's canonical old-boring
bad-cut support is exactly a Finset of source coordinates at which
terminal-I1 *existence inclusion* or full same-node old/upper dependent
L+ crossing *relation inclusion* fails.

Across TWO different physical source pairs, equality of just these
two Boolean flags at each genuinely aligned source cut plus equality
of old-boringness implies equality of bad-cut Finsets.

This does NOT identify source nodes, selected-event labels,
dependent-parameter assignments, outgoing Kpt MMaps or diary orbits.

English-first proof and hostile audit:
  docs/track_e_physical_failure_flags_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- TRUE if the new physical source contains a level-cut terminal
but the old source has NO level-cut terminal. Identity and number
of terminal source nodes are deliberately forgotten. -/
def KptPhysicalTerminalFailure
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldSource newSource : Set (AdmissibleKptNode family))
    (cut : Nat) : Prop :=
  KptI1AtCut family newSource cut ∧
    ¬ KptI1AtCut family oldSource cut

/-- TRUE if some new *complete same-node* physical old/upper L+
crossing pair has no old realization. Includes all negative
ordinary-L and auxiliary E atoms and all competing I2 pairs. -/
def KptPhysicalCrossingFailure
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldSource newSource : Set (AdmissibleKptNode family))
    (cut : Nat) : Prop :=
  ¬ (FullPhysicalClosureCrossing family newSource cut ⊆
      FullPhysicalClosureCrossing family oldSource cut)

/-- Exactly TWO physical failure flags, not a source-node bijection,
a graph-age shadow or a labelled source record. -/
def KptPhysicalCutFailure
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldSource newSource : Set (AdmissibleKptNode family))
    (cut : Nat) : Prop :=
  KptPhysicalTerminalFailure family oldSource newSource cut ∨
    KptPhysicalCrossingFailure family oldSource newSource cut

/-- The checked one-sided physical no-novelty predicate fails
precisely when at least one of the two physical flags is true. -/
theorem kptPhysicalCutFailure_iff_not_noNovelty
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldSource newSource : Set (AdmissibleKptNode family))
    (cut : Nat) :
    KptPhysicalCutFailure family oldSource newSource cut ↔
      ¬ NewRootNoNoveltyAtCut family oldSource newSource cut := by
  classical
  simp only [KptPhysicalCutFailure,
    KptPhysicalTerminalFailure,
    KptPhysicalCrossingFailure, NewRootNoNoveltyAtCut]
  tauto

/-- The canonical FINITE physical off-plan failure support can
be defined without selecting any finite names for source nodes.
It is realization-dependent and source-coordinate dependent. -/
noncomputable def kptPhysicalBadCuts
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldSelected : Nat → Set Nat)
    (oldTop : Nat)
    (oldSource newSource : Nat → Set (AdmissibleKptNode family)) :
    Finset Nat := by
  classical
  exact (Finset.range oldTop).filter
    (fun cut =>
      cut ∉ oldSelected cut ∧
        KptPhysicalCutFailure family
          (oldSource cut) (newSource cut) cut)

/-- Explicit source-coordinate membership normal form. -/
theorem mem_kptPhysicalBadCuts
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldSelected : Nat → Set Nat)
    (oldTop : Nat)
    (oldSource newSource : Nat → Set (AdmissibleKptNode family))
    (cut : Nat) :
    cut ∈ kptPhysicalBadCuts family oldSelected oldTop
        oldSource newSource ↔
      cut < oldTop ∧ cut ∉ oldSelected cut ∧
        KptPhysicalCutFailure family
          (oldSource cut) (newSource cut) cut := by
  classical
  simp only [kptPhysicalBadCuts, Finset.mem_filter, Finset.mem_range]

/-- Under exact full Kpt source indexing at each cut, E54's
index-defined canonical bad Finset equals the genuinely
physical no-index bad Finset. This equality keeps ALL L+ atoms. -/
theorem kptCanonicalOffPlanBadCuts_eq_physicalBadCuts
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldSelected : Nat → Set Nat)
    (oldTop : Nat)
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
        ∃ j : Fin Q, newNode j = z ∧ newLive cut j = true) :
    kptCanonicalOffPlanBadCuts family oldSelected oldTop
        oldNode newNode oldLive newLive =
      kptPhysicalBadCuts family oldSelected oldTop
        oldSource newSource := by
  classical
  ext cut
  rw [mem_kptCanonicalOffPlanBadCuts_iff_physical
      family oldSelected oldTop oldSource newSource
      oldNode newNode oldLive newLive
      hExactOld hExactNew cut,
    mem_kptPhysicalBadCuts,
    kptPhysicalCutFailure_iff_not_noNovelty]

/-- The minimal cross-pair criterion: for two pairs of full physical
source families in one shared Kpt tree, equal old-boring flags,
terminal-failure flags and full dependent-crossing-failure flags
at every *aligned* old-range source cut force equal physical
bad-cut Finsets.

This is strictly weaker than full source-record equality and
does not give coherent labelled occurrences or an upper BRD. -/
theorem kptPhysicalBadCuts_eq_of_two_failure_flags
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldSelected₁ oldSelected₂ : Nat → Set Nat)
    (oldTop : Nat)
    (oldSource₁ newSource₁ : Nat → Set (AdmissibleKptNode family))
    (oldSource₂ newSource₂ : Nat → Set (AdmissibleKptNode family))
    (hOldBoring : ∀ cut : Nat, cut < oldTop →
      (cut ∈ oldSelected₁ cut ↔ cut ∈ oldSelected₂ cut))
    (hTerminal : ∀ cut : Nat, cut < oldTop →
      (KptPhysicalTerminalFailure family
          (oldSource₁ cut) (newSource₁ cut) cut ↔
       KptPhysicalTerminalFailure family
          (oldSource₂ cut) (newSource₂ cut) cut))
    (hCrossing : ∀ cut : Nat, cut < oldTop →
      (KptPhysicalCrossingFailure family
          (oldSource₁ cut) (newSource₁ cut) cut ↔
       KptPhysicalCrossingFailure family
          (oldSource₂ cut) (newSource₂ cut) cut)) :
    kptPhysicalBadCuts family oldSelected₁ oldTop
        oldSource₁ newSource₁ =
      kptPhysicalBadCuts family oldSelected₂ oldTop
        oldSource₂ newSource₂ := by
  classical
  ext cut
  rw [mem_kptPhysicalBadCuts, mem_kptPhysicalBadCuts]
  by_cases hc : cut < oldTop
  · have hBoring :
        (cut ∉ oldSelected₁ cut ↔
         cut ∉ oldSelected₂ cut) :=
      not_congr (hOldBoring cut hc)
    have hFailure :
        KptPhysicalCutFailure family
            (oldSource₁ cut) (newSource₁ cut) cut ↔
        KptPhysicalCutFailure family
            (oldSource₂ cut) (newSource₂ cut) cut := by
      exact or_congr (hTerminal cut hc) (hCrossing cut hc)
    simp only [hc, true_and]
    exact and_congr hBoring hFailure
  · simp only [hc, false_and]

end Kk
