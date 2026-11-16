import Kk.TrackEPhysicalFailureFlags
import Mathlib.Tactic

/-!
# Track G: physical bad-cut support under explicit source-coordinate transport

Track E E55 proves same-cut physical failure-flag transfer. This module
handles two DIFFERENT old scan horizons and a proposed cut-coordinate
map f, without silently identifying numerical source levels.

Under old-boring and both complete physical failure-flag comparisons
on the image, and off-image full physical quietness, the intrinsic
bad-cut support is EXACTLY the image of the reference bad-cut support.
Its cardinality is therefore bounded by the finite reference oldTop,
independent of the target oldTop.

These are CONDITIONAL flag-transport and quietness premises. They are
not derived from equality of macrodiaries and do not transport
labelled Kpt nodes, dependent upper L+ assignments or monoid actions.

English-first proof and hostile audit:
docs/track_g_physical_badcuts_reindex_english_audit_20261116.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A precise certificate for transporting the TWO physical failure
flags from reference source coordinates into another realization.
The off-image condition rules out genuinely unplanned bad cuts.

Even when this holds, f is not proved to be an order-compatible
source-tree map: that is an independent geometric obligation. -/
structure KptPhysicalBadCutReindexCertificate
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldSelected1 oldSelected2 : Nat → Set Nat)
    (top1 top2 : Nat)
    (oldSource1 newSource1 : Nat → Set (AdmissibleKptNode family))
    (oldSource2 newSource2 : Nat → Set (AdmissibleKptNode family))
    (f : Nat → Nat) : Prop where
  inRange : ∀ c : Nat, c < top1 → f c < top2
  oldBoring : ∀ c : Nat, c < top1 →
    (c ∈ oldSelected1 c ↔ f c ∈ oldSelected2 (f c))
  terminal : ∀ c : Nat, c < top1 →
    (KptPhysicalTerminalFailure family
        (oldSource1 c) (newSource1 c) c ↔
      KptPhysicalTerminalFailure family
        (oldSource2 (f c)) (newSource2 (f c)) (f c))
  crossing : ∀ c : Nat, c < top1 →
    (KptPhysicalCrossingFailure family
        (oldSource1 c) (newSource1 c) c ↔
      KptPhysicalCrossingFailure family
        (oldSource2 (f c)) (newSource2 (f c)) (f c))
  offImageQuiet : ∀ d : Nat, d < top2 →
    ¬ (∃ c : Nat, c < top1 ∧ f c = d) →
    d ∉ oldSelected2 d →
    ¬ KptPhysicalCutFailure family
        (oldSource2 d) (newSource2 d) d

/-- The physical exceptional-cut FINSET transports by image when
the reference and target complete failure flags are synchronized
along f and there are no off-image target exceptions.

Neither injectivity nor monotonicity of f is needed for this
FINITE-SET statement. A true diary source-coordinate map requires
additional chronology/labelled parameter conditions. -/
theorem kptPhysicalBadCuts_eq_image_of_reindex_certificate
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldSelected1 oldSelected2 : Nat → Set Nat)
    (top1 top2 : Nat)
    (oldSource1 newSource1 : Nat → Set (AdmissibleKptNode family))
    (oldSource2 newSource2 : Nat → Set (AdmissibleKptNode family))
    (f : Nat → Nat)
    (h : KptPhysicalBadCutReindexCertificate family
      oldSelected1 oldSelected2 top1 top2
      oldSource1 newSource1 oldSource2 newSource2 f) :
    kptPhysicalBadCuts family oldSelected2 top2
      oldSource2 newSource2 =
      (kptPhysicalBadCuts family oldSelected1 top1
        oldSource1 newSource1).image f := by
  classical
  ext d
  rw [Finset.mem_image]
  constructor
  · intro hBad2
    obtain ⟨hd, hSkip2, hFail2⟩ :=
      (mem_kptPhysicalBadCuts family oldSelected2 top2
        oldSource2 newSource2 d).mp hBad2
    by_cases hPre : ∃ c : Nat, c < top1 ∧ f c = d
    · obtain ⟨c, hc, hEq⟩ := hPre
      subst d
      refine ⟨c, ?_, rfl⟩
      have hSkip1 : c ∉ oldSelected1 c := by
        intro hSelected1
        exact hSkip2 ((h.oldBoring c hc).mp hSelected1)
      have hFail1 : KptPhysicalCutFailure family
          (oldSource1 c) (newSource1 c) c := by
        rcases hFail2 with hTerminal2 | hCrossing2
        · exact Or.inl ((h.terminal c hc).mpr hTerminal2)
        · exact Or.inr ((h.crossing c hc).mpr hCrossing2)
      exact (mem_kptPhysicalBadCuts family oldSelected1 top1
        oldSource1 newSource1 c).mpr ⟨hc, hSkip1, hFail1⟩
    · exact False.elim ((h.offImageQuiet d hd hPre hSkip2) hFail2)
  · rintro ⟨c, hBad1, hEq⟩
    obtain ⟨hc, hSkip1, hFail1⟩ :=
      (mem_kptPhysicalBadCuts family oldSelected1 top1
        oldSource1 newSource1 c).mp hBad1
    subst d
    have hSkip2 : f c ∉ oldSelected2 (f c) := by
      intro hSelected2
      exact hSkip1 ((h.oldBoring c hc).mpr hSelected2)
    have hFail2 : KptPhysicalCutFailure family
        (oldSource2 (f c)) (newSource2 (f c)) (f c) := by
      rcases hFail1 with hTerminal1 | hCrossing1
      · exact Or.inl ((h.terminal c hc).mp hTerminal1)
      · exact Or.inr ((h.crossing c hc).mp hCrossing1)
    exact (mem_kptPhysicalBadCuts family oldSelected2 top2
      oldSource2 newSource2 (f c)).mpr
        ⟨h.inRange c hc, hSkip2, hFail2⟩

/-- A fixed reference finite oldTop gives a UNIFORM CARDINALITY bound
on physical bad cuts in every target carrying such a certificate.

This does NOT bound the full labelled envelope or prove a monoid orbit;
uniformity in the actual diary requires a reference depending only
on that diary and geometric certificates for every occurrence. -/
theorem kptPhysicalBadCuts_card_le_reference_top_of_reindex
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldSelected1 oldSelected2 : Nat → Set Nat)
    (top1 top2 : Nat)
    (oldSource1 newSource1 : Nat → Set (AdmissibleKptNode family))
    (oldSource2 newSource2 : Nat → Set (AdmissibleKptNode family))
    (f : Nat → Nat)
    (h : KptPhysicalBadCutReindexCertificate family
      oldSelected1 oldSelected2 top1 top2
      oldSource1 newSource1 oldSource2 newSource2 f) :
    (kptPhysicalBadCuts family oldSelected2 top2
      oldSource2 newSource2).card ≤ top1 := by
  classical
  rw [kptPhysicalBadCuts_eq_image_of_reindex_certificate
    family oldSelected1 oldSelected2 top1 top2
      oldSource1 newSource1 oldSource2 newSource2 f h]
  have hSubset :
      kptPhysicalBadCuts family oldSelected1 top1
        oldSource1 newSource1 ⊆ Finset.range top1 := by
    intro c hc
    exact Finset.mem_range.mpr
      ((mem_kptPhysicalBadCuts family oldSelected1 top1
        oldSource1 newSource1 c).mp hc).1
  calc
    ((kptPhysicalBadCuts family oldSelected1 top1
      oldSource1 newSource1).image f).card
        ≤ (kptPhysicalBadCuts family oldSelected1 top1
            oldSource1 newSource1).card :=
          Finset.card_image_le
    _ ≤ (Finset.range top1).card := Finset.card_le_card hSubset
    _ = top1 := Finset.card_range top1

/-- Stagewise coordinate-transport certificate permitting a FINITE
set of genuinely new auxiliary microcuts outside the old image.
These geometric premises are NOT derived from a refined diary. -/
structure KptPhysicalBadCutReindexExtraCertificate
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldSelected1 oldSelected2 : Nat → Set Nat)
    (top1 top2 : Nat)
    (oldSource1 newSource1 : Nat → Set (AdmissibleKptNode family))
    (oldSource2 newSource2 : Nat → Set (AdmissibleKptNode family))
    (f : Nat → Nat) (Extra : Finset Nat) : Prop where
  inRange : ∀ c : Nat, c < top1 → f c < top2
  oldBoring : ∀ c : Nat, c < top1 →
    (c ∈ oldSelected1 c ↔ f c ∈ oldSelected2 (f c))
  terminal : ∀ c : Nat, c < top1 →
    (KptPhysicalTerminalFailure family
        (oldSource1 c) (newSource1 c) c ↔
      KptPhysicalTerminalFailure family
        (oldSource2 (f c)) (newSource2 (f c)) (f c))
  crossing : ∀ c : Nat, c < top1 →
    (KptPhysicalCrossingFailure family
        (oldSource1 c) (newSource1 c) c ↔
      KptPhysicalCrossingFailure family
        (oldSource2 (f c)) (newSource2 (f c)) (f c))
  offImageAllowed : ∀ d : Nat, d < top2 →
    ¬ (∃ c : Nat, c < top1 ∧ f c = d) →
    d ∉ oldSelected2 d →
    KptPhysicalCutFailure family (oldSource2 d) (newSource2 d) d →
    d ∈ Extra

/-- Every target physical bad cut is either transported from a
reference bad cut or among the explicitly permitted NEW auxiliary
microcuts. Neither the coordinate map nor the extra-event cover
is obtained from the macrodiary here. -/
theorem kptPhysicalBadCuts_subset_image_union_extra
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldSelected1 oldSelected2 : Nat → Set Nat)
    (top1 top2 : Nat)
    (oldSource1 newSource1 : Nat → Set (AdmissibleKptNode family))
    (oldSource2 newSource2 : Nat → Set (AdmissibleKptNode family))
    (f : Nat → Nat) (Extra : Finset Nat)
    (h : KptPhysicalBadCutReindexExtraCertificate family
      oldSelected1 oldSelected2 top1 top2
      oldSource1 newSource1 oldSource2 newSource2 f Extra) :
    kptPhysicalBadCuts family oldSelected2 top2
      oldSource2 newSource2 ⊆
      (kptPhysicalBadCuts family oldSelected1 top1
        oldSource1 newSource1).image f ∪ Extra := by
  classical
  intro d hBad2
  obtain ⟨hd, hSkip2, hFail2⟩ :=
    (mem_kptPhysicalBadCuts family oldSelected2 top2
      oldSource2 newSource2 d).mp hBad2
  by_cases hPre : ∃ c : Nat, c < top1 ∧ f c = d
  · obtain ⟨c, hc, hEq⟩ := hPre
    subst d
    have hSkip1 : c ∉ oldSelected1 c := by
      intro hSel1
      exact hSkip2 ((h.oldBoring c hc).mp hSel1)
    have hFail1 : KptPhysicalCutFailure family
        (oldSource1 c) (newSource1 c) c := by
      rcases hFail2 with hTerminal2 | hCrossing2
      · exact Or.inl ((h.terminal c hc).mpr hTerminal2)
      · exact Or.inr ((h.crossing c hc).mpr hCrossing2)
    have hBad1 : c ∈ kptPhysicalBadCuts family oldSelected1 top1
        oldSource1 newSource1 :=
      (mem_kptPhysicalBadCuts family oldSelected1 top1
        oldSource1 newSource1 c).mpr ⟨hc,hSkip1,hFail1⟩
    exact Finset.mem_union.mpr
      (Or.inl (Finset.mem_image.mpr ⟨c,hBad1,rfl⟩))
  · exact Finset.mem_union.mpr
      (Or.inr (h.offImageAllowed d hd hPre hSkip2 hFail2))

/-- If at most |Extra| genuinely new bad cuts are permitted at this
physical stage, their total number is bounded by reference oldTop
plus |Extra|. This is a FINITE-SET inequality, not a uniform BRD
bound without a fixed diary-derived reference and geometric inputs. -/
theorem kptPhysicalBadCuts_card_le_reference_top_add_extra
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldSelected1 oldSelected2 : Nat → Set Nat)
    (top1 top2 : Nat)
    (oldSource1 newSource1 : Nat → Set (AdmissibleKptNode family))
    (oldSource2 newSource2 : Nat → Set (AdmissibleKptNode family))
    (f : Nat → Nat) (Extra : Finset Nat)
    (h : KptPhysicalBadCutReindexExtraCertificate family
      oldSelected1 oldSelected2 top1 top2
      oldSource1 newSource1 oldSource2 newSource2 f Extra) :
    (kptPhysicalBadCuts family oldSelected2 top2
      oldSource2 newSource2).card ≤ top1 + Extra.card := by
  classical
  let B1 : Finset Nat :=
    kptPhysicalBadCuts family oldSelected1 top1
      oldSource1 newSource1
  let B2 : Finset Nat :=
    kptPhysicalBadCuts family oldSelected2 top2
      oldSource2 newSource2
  have hSub : B2 ⊆ B1.image f ∪ Extra :=
    kptPhysicalBadCuts_subset_image_union_extra
      family oldSelected1 oldSelected2 top1 top2
      oldSource1 newSource1 oldSource2 newSource2 f Extra h
  have hB1Range : B1 ⊆ Finset.range top1 := by
    intro c hc
    exact Finset.mem_range.mpr
      ((mem_kptPhysicalBadCuts family oldSelected1 top1
        oldSource1 newSource1 c).mp hc).1
  have hB1Card : B1.card ≤ top1 := by
    calc
      B1.card ≤ (Finset.range top1).card :=
        Finset.card_le_card hB1Range
      _ = top1 := Finset.card_range top1
  calc
    B2.card ≤ (B1.image f ∪ Extra).card :=
      Finset.card_le_card hSub
    _ ≤ (B1.image f).card + Extra.card :=
      Finset.card_union_le
    _ ≤ B1.card + Extra.card :=
      Nat.add_le_add_right Finset.card_image_le _
    _ ≤ top1 + Extra.card :=
      Nat.add_le_add_right hB1Card _

end Kk
