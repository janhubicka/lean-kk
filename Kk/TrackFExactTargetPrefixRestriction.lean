import Kk.TrackFActualCodingFibre
import Kk.TrackFRealHensonTypeTree
import Mathlib.Tactic

/-!
# Track F: exact chronological target type prefix truncation

English-first adversarial proof:
docs/track_f_target_exact_level_english_audit.md

The old manuscript requested source-target type continuation at an
EXACT later target level, whereas previous Lean theorems returned
a target type only at some level >= the requested bound.

Any genuine finite Henson one-type w can be RESTRICTED to a prefix
L<=w.level by keeping precisely the old positive and negative
adjacency bits below L. Its actual K_(ell-1)-free certificate
persists by finite directed clique capacity monotonicity.

If v0<=w and v0.level<=L, then v0<=restrict w L<=w;
equality of ranks at the two endpoints forces equality at L.
For exact actual sourceCodingFibre predicates, a longer target
prefix yields a SUBSET of the shorter target prefix's fibre.
This is the key set and rank sandwich for exact-level transport.

No new Henson, diary, BRD, or enumeration axiom is introduced.
-/

namespace Kk.HensonOneType

variable {ell : Nat} {E : Nat → Nat → Bool}

/-- Restrict a genuine finite Henson type w to its true
chronological prefix [0,L), including all negative old bits.
The old K_(ell-1)-free neighbour certificate is inherited via
monotonicity of maximum directed clique capacity. -/
def restrictPrefix (w : HensonOneType ell E)
    (L : Nat) (hL : L ≤ w.level) : HensonOneType ell E where
  level := L
  neighbours := w.neighbours.filter (fun x => x < L)
  below := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  safe := by
    have hSub :
        w.neighbours.filter (fun x => x < L) ⊆ w.neighbours :=
      Finset.filter_subset _ _
    have hCap :=
      finiteDirectedCliqueCapacity_mono E
        (w.neighbours.filter (fun x => x < L))
        w.neighbours hSub
    have hSafeCap : finiteDirectedCliqueCapacity E
        w.neighbours < ell - 1 :=
      (finitePoolCliqueCheck_false_iff_capacity_lt
        E (ell - 1) w.neighbours).1 w.safe
    exact (finitePoolCliqueCheck_false_iff_capacity_lt
      E (ell - 1) (w.neighbours.filter (fun x => x < L))).2
      (lt_of_le_of_lt hCap hSafeCap)

/-- Every prefix-restricted type extends into its original
type, with COMPLETE positive and negative bits unchanged
below the restriction level. -/
theorem restrictPrefix_le
    (w : HensonOneType ell E)
    (L : Nat) (hL : L ≤ w.level) :
    restrictPrefix w L hL ≤ w := by
  refine ⟨hL, ?_⟩
  intro x hx
  change x < L at hx
  change (x ∈ w.neighbours.filter (fun y => y < L) ↔
    x ∈ w.neighbours)
  simp [Finset.mem_filter, hx]

/-- If an old type v0 is extended by w and the desired
intermediate target level L is at least v0.level,
then v0 also extends into the TRUE restriction of w at L. -/
theorem le_restrictPrefix_of_le
    (v0 w : HensonOneType ell E)
    (hVW : v0 ≤ w)
    (L : Nat) (hOld : v0.level ≤ L)
    (hNew : L ≤ w.level) :
    v0 ≤ restrictPrefix w L hNew := by
  refine ⟨hOld, ?_⟩
  intro x hx
  have hxL : x < L := lt_of_lt_of_le hx hOld
  have hBits : x ∈ v0.neighbours ↔ x ∈ w.neighbours :=
    hVW.2 x hx
  change x ∈ v0.neighbours ↔
    x ∈ w.neighbours.filter (fun y => y < L)
  simp only [Finset.mem_filter, hxL, and_true]
  exact hBits

/-- Rank is ANTITONE along chronological type extension.
If the first and last types have the SAME singleton rank,
the genuine intermediate target type of any later level
also has exactly this rank (rank sandwich). -/
theorem rank_restrictPrefix_eq_of_endpoint_eq
    (v0 w : HensonOneType ell E)
    (hVW : v0 ≤ w)
    (hRank : rank v0 = rank w)
    (L : Nat)
    (hOld : v0.level ≤ L) (hNew : L ≤ w.level) :
    rank (restrictPrefix w L hNew) = rank w := by
  have hVL : v0 ≤ restrictPrefix w L hNew :=
    le_restrictPrefix_of_le v0 w hVW L hOld hNew
  have hLW : restrictPrefix w L hNew ≤ w :=
    restrictPrefix_le w L hNew
  have hLeft : rank w ≤ rank (restrictPrefix w L hNew) :=
    rank_antitone hLW
  have hRight : rank (restrictPrefix w L hNew) ≤ rank v0 :=
    rank_antitone hVL
  omega

/-- The fibre of an EXTENDED target type is contained in the
fibre of the SHORTER target prefix: all source coding originals
matching a longer complete two-directed target column match
its true shorter prefix as well. No source/target enumeration
order or induced-embedding hypothesis is required here. -/
theorem sourceCodingFibre_antitone_target
    (Esrc Etgt : Nat → Nat → Bool)
    (e : Nat → Nat)
    (v0 w : HensonOneType ell Etgt)
    (hVW : v0 ≤ w) :
    sourceCodingFibre (E := Esrc) Etgt e w ⊆
      sourceCodingFibre (E := Esrc) Etgt e v0 := by
  intro x hx
  refine ⟨hx.1, le_trans hVW.1 hx.2.1, ?_⟩
  intro p hp
  have hpW : p < w.level := lt_of_lt_of_le hp hVW.1
  have hCols := hx.2.2 p hpW
  have hDec :
      decide (p ∈ w.neighbours) =
        decide (p ∈ v0.neighbours) := by
    by_cases hOld : p ∈ v0.neighbours
    · have hNew : p ∈ w.neighbours := (hVW.2 p hp).mp hOld
      simp [hOld,hNew]
    · have hNew : p ∉ w.neighbours := by
        intro hpNew
        exact hOld ((hVW.2 p hp).mpr hpNew)
      simp [hOld,hNew]
  exact ⟨hCols.1.trans hDec,hCols.2.trans hDec⟩

end Kk.HensonOneType
