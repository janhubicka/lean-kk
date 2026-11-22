import Kk.TrackFPrecodeEndpointAgeSandwich
import Kk.TrackFPhysicalSurvivorDeletion
import Kk.TrackFTypePrefixCanonicalAgeSandwich
import Kk.TrackFZeroCodePreprofileRigidity
import Mathlib.Tactic

/-!
# Track F: complete genuine zero-code profile via REAL survivors, no dummy

Audited English proof and 18 hostile checks committed FIRST:
docs/track_f_genuine_survivor_code_age_english_audit_20261122.md

Genuine chronological target OLD/PRE type families are indexed by
Fin(d+1); the ACTUALLY surviving target family is indexed by Fin(d)
under the exact TARGET order-preserving deletion f=succAboveEmb j.

If the old and later genuine survivor canonical NUMERIC ages agree,
then the COMPLETE pre-code survivor profile agrees via the checked
true three-front chronological sandwich on Fin(d), not by assuming
anything about the intermediate pre-code profile.

The checked canonical survivor reindexing, plus exact finite
support lifting from every support that avoids j, transfers that
equality to ALL full pre-code supports avoiding j. The genuine
pre-code age, chronological P<=F, coded singleton rank zero and
full legal zero-code erasure law then give P=F on ALL supports,
including mixed triples, by the checked domain-correct rigidity.

No dummy later coded branch is constructed or assumed. No global
history, target lex-order identification from source order, or BRD.
-/

namespace Kk

/-- Every admissible nonempty old-sort support avoiding the coded
sort j is the EXACT image of an admissible nonempty support on the
order-preservingly reindexed survivors Fin d.

This is the missing finite support inverse for the physical age
deletion theorem. It uses Mathlib's actual succAbove complement
surjectivity; no invented empty support or collapsed sort. -/
theorem trackFCodeSupport_exists_survivor_preimage
    (d ell : Nat) (j : Fin (d + 1))
    (T : IntegerGraphSupport (d + 1) ell)
    (hjT : j ∉ T.1) :
    ∃ U : IntegerGraphSupport d ell,
      trackFMapSupport (Fin.succAboveEmb j) U = T := by
  classical
  let f : Fin d ↪ Fin (d + 1) := Fin.succAboveEmb j
  let S : Finset (Fin d) := trackFSelectedPreimage f T
  have hTSub : T.1 ⊆ Finset.univ.image f := by
    intro k hk
    have hkj : k ≠ j := by
      intro h
      exact hjT (h ▸ hk)
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq (x := k) (y := j) hkj
    exact Finset.mem_image.mpr
      ⟨i, Finset.mem_univ i, by simpa only [f, Fin.succAboveEmb_apply] using hi⟩
  have hImage : S.image f = T.1 := by
    calc
      S.image f = T.1 ∩ Finset.univ.image f :=
        trackFSelectedPreimage_image f T
      _ = T.1 := Finset.inter_eq_left.mpr hTSub
  have hNonempty : S.Nonempty := by
    obtain ⟨k, hk⟩ := T.2.1
    have hkImage : k ∈ S.image f := by rw [hImage]; exact hk
    obtain ⟨i, hi, _⟩ := Finset.mem_image.mp hkImage
    exact ⟨i, hi⟩
  have hCard : S.card ≤ ell - 1 := by
    calc
      S.card = (S.image f).card :=
        (Finset.card_image_of_injective S f.injective).symm
      _ = T.1.card := congrArg Finset.card hImage
      _ ≤ ell - 1 := T.2.2
  let U : IntegerGraphSupport d ell := ⟨S, ⟨hNonempty, hCard⟩⟩
  refine ⟨U, ?_⟩
  apply Subtype.ext
  exact hImage

/-- Full ACTUAL zero-code numeric preprofile rigidity with no
artificial later continuation of the terminated coded branch.

OLD and PRE are genuine target K4 front types on d+1 sorts;
LATER contains only the d genuine SURVIVING target types.
The survivor map is the actual order-preserving deletion
f=Fin.succAboveEmb j, not a guessed source-to-target label map.

If these genuine chronological fronts satisfy:
* old<=pre on EVERY old sort, pre(f i)<=later_i on survivors;
* the NUMERIC old and later survivor canonical ages coincide;
* old/pre coded singleton true ranks are zero;
* the old full canonical age obeys the legitimate zero-code
  erasure law on every genuine mixed support,
then the COMPLETE PRE canonical age equals the COMPLETE OLD age
on ALL admissible supports, including every j-containing triple.

The full intermediate pre-code equality is DERIVED; neither it
nor survivor-precode equality is a hypothesis. The endpoint
NUMERIC equality is a separate output of #482 plus target survivor
order matching. No future coded dummy, diary or BRD lower bound. -/
theorem k4ActualPrecode_full_age_eq_of_genuine_survivor_endpoints
    (d m c H : Nat) (E : Nat → Nat → Bool)
    (j : Fin (d + 1))
    (hmC : m ≤ c) (hcH : c ≤ H)
    (old pre : Fin (d + 1) → HensonOneType 4 E)
    (later : Fin d → HensonOneType 4 E)
    (hOldLevel : ∀ i, (old i).level = m)
    (hPreLevel : ∀ i, (pre i).level = c)
    (hLaterLevel : ∀ i, (later i).level = H)
    (hOldPre : ∀ i, old i ≤ pre i)
    (hPreLater : ∀ i, pre (Fin.succAboveEmb j i) ≤ later i)
    (hEndpoint :
      trackFPhysicalFrontCanonicalAge d 4 m E
        (fun i => old (Fin.succAboveEmb j i)) =
      trackFPhysicalFrontCanonicalAge d 4 H E later)
    (hOldRank : HensonOneType.rank (old j) = 0)
    (hPreRank : HensonOneType.rank (pre j) = 0)
    (hLegal : ∀ T : IntegerGraphSupport (d + 1) 4,
      j ∈ T.1 → ∀ S : IntegerGraphSupport (d + 1) 4,
        S.1 = T.1.erase j →
        trackFPhysicalFrontCanonicalAge (d + 1) 4 m E old T =
        trackFPhysicalFrontCanonicalAge (d + 1) 4 m E old S) :
    trackFPhysicalFrontCanonicalAge (d + 1) 4 c E pre =
      trackFPhysicalFrontCanonicalAge (d + 1) 4 m E old := by
  classical
  let f : Fin d ↪ Fin (d + 1) := Fin.succAboveEmb j
  have hSmallPre :
      trackFPhysicalFrontCanonicalAge d 4 c E
          (fun i => pre (f i)) =
      trackFPhysicalFrontCanonicalAge d 4 m E
          (fun i => old (f i)) :=
    trackFActualFront_canonical_sandwich_eq
      d 4 m c H E hmC hcH
      (fun i => old (f i))
      (fun i => pre (f i))
      later
      (fun i => hOldLevel (f i))
      (fun i => hPreLevel (f i))
      hLaterLevel
      (fun i => hOldPre (f i))
      hPreLater
      hEndpoint
  have hTruePre :
      IsIntegerGraphAge (d + 1) 4
        (trackFPhysicalFrontCanonicalAge (d + 1) 4 c E pre) :=
    trackFActualFront_canonical_is_integer_graph_age
      (d + 1) 4 c (by decide) E pre hPreLevel
  have hPreLe :
      AgeLe
        (trackFPhysicalFrontCanonicalAge (d + 1) 4 c E pre)
        (trackFPhysicalFrontCanonicalAge (d + 1) 4 m E old) :=
    trackFActualFront_canonical_antitone_of_extension
      (d + 1) 4 m c E hmC old pre
      hOldLevel hPreLevel hOldPre
  have hSurvivorEquality :
      ∀ T : IntegerGraphSupport (d + 1) 4, j ∉ T.1 →
        trackFPhysicalFrontCanonicalAge (d + 1) 4 c E pre T =
        trackFPhysicalFrontCanonicalAge (d + 1) 4 m E old T := by
    intro T hjT
    obtain ⟨U, hU⟩ :=
      trackFCodeSupport_exists_survivor_preimage d 4 j T hjT
    have hPreReindex :
        trackFPhysicalFrontCanonicalAge d 4 c E
          (fun i => pre (f i)) U =
        trackFPhysicalFrontCanonicalAge (d + 1) 4 c E pre
          (trackFMapSupport f U) :=
      trackFActualFront_canonical_reindex f (by decide) c E pre U
    have hOldReindex :
        trackFPhysicalFrontCanonicalAge d 4 m E
          (fun i => old (f i)) U =
        trackFPhysicalFrontCanonicalAge (d + 1) 4 m E old
          (trackFMapSupport f U) :=
      trackFActualFront_canonical_reindex f (by decide) m E old U
    have hSmallU :
        trackFPhysicalFrontCanonicalAge d 4 c E
          (fun i => pre (f i)) U =
        trackFPhysicalFrontCanonicalAge d 4 m E
          (fun i => old (f i)) U :=
      congrArg (fun A : IntegerGraphSupport d 4 → Nat => A U)
        hSmallPre
    calc
      trackFPhysicalFrontCanonicalAge (d + 1) 4 c E pre T =
          trackFPhysicalFrontCanonicalAge (d + 1) 4 c E pre
            (trackFMapSupport f U) := by rw [hU]
      _ = trackFPhysicalFrontCanonicalAge d 4 c E
            (fun i => pre (f i)) U := hPreReindex.symm
      _ = trackFPhysicalFrontCanonicalAge d 4 m E
            (fun i => old (f i)) U := hSmallU
      _ = trackFPhysicalFrontCanonicalAge (d + 1) 4 m E old
            (trackFMapSupport f U) := hOldReindex
      _ = trackFPhysicalFrontCanonicalAge (d + 1) 4 m E old T := by
            rw [hU]
  have hPOne :
      ∀ T : IntegerGraphSupport (d + 1) 4,
        T.1 = {j} →
        trackFPhysicalFrontCanonicalAge (d + 1) 4 c E pre T = 1 := by
    intro T hT
    have hTSing : T =
        trackFSingletonSupport (d + 1) 4 j (by decide) :=
      Subtype.ext hT
    subst T
    exact trackFPhysicalFront_singleton_one_of_rank_zero
      (d + 1) 4 c (by decide) E pre hPreLevel j hPreRank
  have hFOne :
      ∀ T : IntegerGraphSupport (d + 1) 4,
        T.1 = {j} →
        trackFPhysicalFrontCanonicalAge (d + 1) 4 m E old T = 1 := by
    intro T hT
    have hTSing : T =
        trackFSingletonSupport (d + 1) 4 j (by decide) :=
      Subtype.ext hT
    subst T
    exact trackFPhysicalFront_singleton_one_of_rank_zero
      (d + 1) 4 m (by decide) E old hOldLevel j hOldRank
  exact integerGraphAge_zeroCode_preprofile_rigidity
    (d + 1) 4 j
    (trackFPhysicalFrontCanonicalAge (d + 1) 4 m E old)
    (trackFPhysicalFrontCanonicalAge (d + 1) 4 c E pre)
    hTruePre hPreLe hSurvivorEquality hPOne hFOne hLegal

/-- A source-mediated endpoint interface: the genuine old target
survivor canonical age and later true target survivor canonical age
are both equal to ONE genuine source survivor checkpoint age.

This makes the exact intended application of the verified numerical
source/target synchronization theorem (#482) explicit. No target
lex-order map is silently inferred: the old target survivors are
exactly selected by the order-preserving f=succAboveEmb j. -/
theorem k4ActualPrecode_full_age_eq_of_source_checkpoint
    (d m c H ms : Nat)
    (Esrc E : Nat → Nat → Bool)
    (j : Fin (d + 1))
    (hmC : m ≤ c) (hcH : c ≤ H)
    (old pre : Fin (d + 1) → HensonOneType 4 E)
    (later : Fin d → HensonOneType 4 E)
    (source : Fin d → HensonOneType 4 Esrc)
    (hOldLevel : ∀ i, (old i).level = m)
    (hPreLevel : ∀ i, (pre i).level = c)
    (hLaterLevel : ∀ i, (later i).level = H)
    (hOldPre : ∀ i, old i ≤ pre i)
    (hPreLater : ∀ i, pre (Fin.succAboveEmb j i) ≤ later i)
    (hSourceOld :
      trackFPhysicalFrontCanonicalAge d 4 ms Esrc source =
      trackFPhysicalFrontCanonicalAge d 4 m E
        (fun i => old (Fin.succAboveEmb j i)))
    (hSourceLater :
      trackFPhysicalFrontCanonicalAge d 4 ms Esrc source =
      trackFPhysicalFrontCanonicalAge d 4 H E later)
    (hOldRank : HensonOneType.rank (old j) = 0)
    (hPreRank : HensonOneType.rank (pre j) = 0)
    (hLegal : ∀ T : IntegerGraphSupport (d + 1) 4,
      j ∈ T.1 → ∀ S : IntegerGraphSupport (d + 1) 4,
        S.1 = T.1.erase j →
        trackFPhysicalFrontCanonicalAge (d + 1) 4 m E old T =
        trackFPhysicalFrontCanonicalAge (d + 1) 4 m E old S) :
    trackFPhysicalFrontCanonicalAge (d + 1) 4 c E pre =
      trackFPhysicalFrontCanonicalAge (d + 1) 4 m E old := by
  apply k4ActualPrecode_full_age_eq_of_genuine_survivor_endpoints
    d m c H E j hmC hcH old pre later
    hOldLevel hPreLevel hLaterLevel hOldPre hPreLater
  · exact hSourceOld.symm.trans hSourceLater
  · exact hOldRank
  · exact hPreRank
  · exact hLegal

end Kk
