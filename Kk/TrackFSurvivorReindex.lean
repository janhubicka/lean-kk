import Kk.TrackFMonotoneRawLocality
import Mathlib.Tactic

/-!
# Track F: deletion/reindexing of actual finite concrete word columns

An embedding of e surviving ordered sorts into d old sorts transports
nonempty admissible supports and an ordered list of word columns.
The literal c_n common-positive-letter function is preserved exactly
under this injection, and hence so is the *raw* word bound phi.

The stronger claim that the true integer-witness canonicalizer commutes
with finite dimension reduction requires explicit feasible vector
restriction/zero extension and raw monotonicity. The proof steps will
be provided in this module separately from the raw word identity.
No source B3, full diary correspondence or new unavoidability claimed.
-/

namespace Kk

/-- Image of a nonempty admissible support under a *genuine injection*
of surviving coordinates. No labelled sort is merged with another. -/
def trackFMapSupport {e d ell : Nat}
    (f : Fin e ↪ Fin d)
    (U : IntegerGraphSupport e ell) :
    IntegerGraphSupport d ell :=
  ⟨U.1.image f,
    ⟨U.2.1.image f,
      (Finset.card_image_le).trans U.2.2⟩⟩

/-- Every entry of a chronological column after retaining exactly the
ordered coordinates selected by f. -/
def trackFRestrictColumns {e d : Nat}
    (f : Fin e ↪ Fin d)
    (cols : List (Fin d → Nat)) : List (Fin e → Nat) :=
  cols.map (fun col i => col (f i))

/-- The literal common letter of any nonempty support survives
injective reindexing, including the cases where no positive common
symbol exists. The proof uses the exact c_n positive-letter API. -/
theorem trackFColumnCommon_reindex {e d ell : Nat}
    (f : Fin e ↪ Fin d)
    (col : Fin d → Nat) (U : IntegerGraphSupport e ell) :
    trackFColumnCommon (fun i => col (f i)) U =
      trackFColumnCommon col (trackFMapSupport f U) := by
  classical
  have hPositive : ∀ n : Nat, 0 < n →
      (trackFColumnCommon (fun i => col (f i)) U = n ↔
       trackFColumnCommon col (trackFMapSupport f U) = n) := by
    intro n hn
    rw [trackFColumnCommon_pos_iff _ _ n hn,
        trackFColumnCommon_pos_iff _ _ n hn]
    constructor
    · intro h j hj
      obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hj
      subst j
      exact h i hi
    · intro h i hi
      exact h (f i) (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
  let a := trackFColumnCommon (fun i => col (f i)) U
  let b := trackFColumnCommon col (trackFMapSupport f U)
  change a = b
  by_cases ha : 0 < a
  · exact ((hPositive a ha).mp rfl).symm
  · have ha0 : a = 0 := Nat.eq_zero_of_not_pos ha
    by_cases hb : 0 < b
    · exact (hPositive b hb).mpr rfl
    · have hb0 : b = 0 := Nat.eq_zero_of_not_pos hb
      exact ha0.trans hb0.symm

/-- For every chronological history, deleting/reindexing the
selected active words gives precisely the raw bound obtained by
restricting the old phi to supports contained in the image of f.
No assumption that phi itself is a canonical graph age. -/
theorem trackFWordRaw_restrict_columns {e d ell : Nat}
    (f : Fin e ↪ Fin d)
    (cols : List (Fin d → Nat))
    (U : IntegerGraphSupport e ell) :
    trackFWordRaw e ell (trackFRestrictColumns f cols) U =
      trackFWordRaw d ell cols (trackFMapSupport f U) := by
  classical
  have hFold : ∀ (cs : List (Fin d → Nat)) (start : Nat),
      ((cs.map (fun col i => col (f i))).foldl
        (fun cap col =>
          min cap (ell - 1 - trackFColumnCommon col U)) start) =
      (cs.foldl
        (fun cap col =>
          min cap (ell - 1 -
            trackFColumnCommon col (trackFMapSupport f U))) start) := by
    intro cs
    induction cs with
    | nil =>
        intro start
        rfl
    | cons col tail ih =>
        intro start
        simp only [List.map_cons, List.foldl_cons]
        rw [trackFColumnCommon_reindex f col U]
        exact ih _
  exact hFold cols (ell - 1)

/-- Pull a raw finite graph-age record back along an injective
selection of active sorts. All admissible nonempty supports are
imaged into actual admissible nonempty supports. -/
def trackFPullbackRaw {e d ell : Nat}
    (f : Fin e ↪ Fin d)
    (B : IntegerGraphSupport d ell → Nat) :
    IntegerGraphSupport e ell → Nat :=
  fun U => B (trackFMapSupport f U)

/-- The actual word record commutes with raw pullback, rather than
merely having the same canonical bound in favorable finite cases. -/
theorem trackFWordRaw_pullback {e d ell : Nat}
    (f : Fin e ↪ Fin d)
    (cols : List (Fin d → Nat)) :
    trackFWordRaw e ell (trackFRestrictColumns f cols) =
      trackFPullbackRaw f (trackFWordRaw d ell cols) := by
  funext U
  exact trackFWordRaw_restrict_columns f cols U

end Kk
