import Kk.CanonicalCoverBlock
import Mathlib.Tactic

/-!
# Integer-witness canonicalization for K_ell-free graph ages

The manuscript's graph-age data are integer bounds on nonempty
supports T of size at most ell-1. Consistency means that for each T,
a multiplicity vector realizes F(T) while respecting every bound.
Such a witness can be supported on T and thus normalized to total
size at most ell-1.

This file constructs G_B as a finite supremum of exactly these
normalized vectors and checks admissibility, boundedness, and
maximality. The raw clique-cover lemma is then specialized to
these actual integer-witness ages. No physical numerical-H gadget
or common labelled orbit is constructed here.
-/

namespace Kk

universe u v

/-- A finite integer witness respects every raw bound. -/
def WitnessRespects {ι : Type u} {ω : Type v}
    (value : ω → ι → Nat) (B : ι → Nat) (w : ω) : Prop :=
  ∀ i, value w i ≤ B i

/-- The canonical integer-witness bound G_B is a finite maximum. -/
noncomputable def finiteWitnessCanonical
    {ι : Type u} {ω : Type v} [Fintype ω]
    (value : ω → ι → Nat) (B : ι → Nat) (i : ι) : Nat := by
  classical
  exact (Finset.univ.filter (WitnessRespects value B)).sup
    (fun w => value w i)

/-- Each feasible vector contributes to the canonical maximum. -/
theorem witnessValue_le_canonical
    {ι : Type u} {ω : Type v} [Fintype ω]
    (value : ω → ι → Nat) (B : ι → Nat)
    (w : ω) (hw : WitnessRespects value B w) (i : ι) :
    value w i ≤ finiteWitnessCanonical value B i := by
  classical
  unfold finiteWitnessCanonical
  have hmem : w ∈ Finset.univ.filter (WitnessRespects value B) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩
  exact Finset.le_sup hmem

/-- Canonicalization is pointwise below the raw bound. -/
theorem finiteWitnessCanonical_le_raw
    {ι : Type u} {ω : Type v} [Fintype ω]
    (value : ω → ι → Nat) (B : ι → Nat) :
    AgeLe (finiteWitnessCanonical value B) B := by
  classical
  intro i
  unfold finiteWitnessCanonical
  apply Finset.sup_le
  intro w hw
  exact (Finset.mem_filter.mp hw).2 i

/-- Consistency is exactly the integer-witness condition at each support. -/
def IsFiniteWitnessAge {ι : Type u} {ω : Type v}
    (value : ω → ι → Nat) (cap : Nat) (F : ι → Nat) : Prop :=
  (∀ i, 1 ≤ F i ∧ F i ≤ cap) ∧
  (∀ i, ∃ w, WitnessRespects value F w ∧ value w i = F i)

/-- Every admissible age below B is below its canonicalization. -/
theorem finiteWitnessCanonical_greatest
    {ι : Type u} {ω : Type v} [Fintype ω]
    (value : ω → ι → Nat) (cap : Nat)
    (B H : ι → Nat)
    (hAge : IsFiniteWitnessAge value cap H)
    (hHB : AgeLe H B) :
    AgeLe H (finiteWitnessCanonical value B) := by
  intro i
  obtain ⟨w, hw, hval⟩ := hAge.2 i
  rw [← hval]
  apply witnessValue_le_canonical value B w
  intro j
  exact le_trans (hw j) (hHB j)

/-- A uniform bound on witness values bounds the canonical maximum. -/
theorem finiteWitnessCanonical_le_cap
    {ι : Type u} {ω : Type v} [Fintype ω]
    (value : ω → ι → Nat) (cap : Nat)
    (hCap : ∀ w i, value w i ≤ cap)
    (B : ι → Nat) :
    ∀ i, finiteWitnessCanonical value B i ≤ cap := by
  classical
  intro i
  unfold finiteWitnessCanonical
  apply Finset.sup_le
  intro w _
  exact hCap w i

/-- Above a genuine admissible age, the finite maximum is realized
and is itself an admissible integer-witness age. -/
theorem finiteWitnessCanonical_is_age
    {ι : Type u} {ω : Type v} [Fintype ω]
    (value : ω → ι → Nat) (cap : Nat)
    (hCap : ∀ w i, value w i ≤ cap)
    (B H : ι → Nat)
    (hAge : IsFiniteWitnessAge value cap H)
    (hHB : AgeLe H B) :
    IsFiniteWitnessAge value cap (finiteWitnessCanonical value B) := by
  classical
  constructor
  · intro i
    constructor
    · exact le_trans (hAge.1 i).1
        (finiteWitnessCanonical_greatest value cap B H hAge hHB i)
    · exact finiteWitnessCanonical_le_cap value cap hCap B i
  · intro i
    obtain ⟨w₀, hw₀, _⟩ := hAge.2 i
    let W : Finset ω := Finset.univ.filter (WitnessRespects value B)
    have hw₀B : WitnessRespects value B w₀ := by
      intro j
      exact le_trans (hw₀ j) (hHB j)
    have hw₀mem : w₀ ∈ W :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ w₀, hw₀B⟩
    have hnonempty : W.Nonempty := ⟨w₀, hw₀mem⟩
    obtain ⟨w, hwmem, hmax⟩ :=
      Finset.exists_mem_eq_sup W hnonempty (fun w => value w i)
    have hB : WitnessRespects value B w :=
      (Finset.mem_filter.mp hwmem).2
    refine ⟨w, ?_, ?_⟩
    · intro j
      exact witnessValue_le_canonical value B w hB j
    · simpa only [finiteWitnessCanonical, W] using hmax.symm

/-- Nonempty supports involving at most ell-1 of d labelled sorts. -/
abbrev IntegerGraphSupport (d ell : Nat) :=
  {T : Finset (Fin d) // T.Nonempty ∧ T.card ≤ ell - 1}

/-- Clique multiplicity vectors, normalized to total size <= ell-1. -/
abbrev IntegerCliqueWeights (d ell : Nat) :=
  {w : Fin d → Fin ell //
    (Finset.univ.sum (fun j : Fin d => (w j).val)) ≤ ell - 1}

/-- The integer multiplicity of a vector on a named support. -/
def integerCliqueOnSupport {d ell : Nat}
    (w : IntegerCliqueWeights d ell)
    (T : IntegerGraphSupport d ell) : Nat :=
  T.1.sum (fun j => (w.1 j).val)

/-- A normalized witness has size <= ell-1 on every support. -/
theorem integerCliqueOnSupport_le {d ell : Nat}
    (w : IntegerCliqueWeights d ell)
    (T : IntegerGraphSupport d ell) :
    integerCliqueOnSupport w T ≤ ell - 1 := by
  have hpart :
      T.1.sum (fun j => (w.1 j).val) ≤
        Finset.univ.sum (fun j : Fin d => (w.1 j).val) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ T.1)
    intro j _ _
    exact Nat.zero_le _
  exact hpart.trans w.2

/-- The normalized integer-witness consistency condition. -/
def IsIntegerGraphAge (d ell : Nat)
    (F : IntegerGraphSupport d ell → Nat) : Prop :=
  IsFiniteWitnessAge (integerCliqueOnSupport (d := d) (ell := ell))
    (ell - 1) F

/-- The concrete G_B operation on finite integer-witness graph ages. -/
noncomputable def integerGraphAgeCanonical (d ell : Nat)
    (B : IntegerGraphSupport d ell → Nat) :
    IntegerGraphSupport d ell → Nat :=
  finiteWitnessCanonical
    (integerCliqueOnSupport (d := d) (ell := ell)) B

theorem integerGraphAgeCanonical_le_raw (d ell : Nat)
    (B : IntegerGraphSupport d ell → Nat) :
    AgeLe (integerGraphAgeCanonical d ell B) B :=
  finiteWitnessCanonical_le_raw _ B

theorem integerGraphAgeCanonical_greatest (d ell : Nat)
    (B H : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell H)
    (hHB : AgeLe H B) :
    AgeLe H (integerGraphAgeCanonical d ell B) :=
  finiteWitnessCanonical_greatest _ (ell - 1) B H hAge hHB

theorem integerGraphAgeCanonical_is_age (d ell : Nat)
    (B H : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell H)
    (hHB : AgeLe H B) :
    IsIntegerGraphAge d ell (integerGraphAgeCanonical d ell B) :=
  finiteWitnessCanonical_is_age _ (ell - 1)
    (fun w T => integerCliqueOnSupport_le w T) B H hAge hHB

/-- Exact finite integer-witness graph-age cover-block theorem.
Only the genuine cover and its changed coordinate are hypotheses;
numerical-H realization is NOT asserted. -/
theorem integerGraphAge_canonical_cover_block
    (d ell r : Nat)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (T : IntegerGraphSupport d ell)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (hEll : ell = lower T + r + 1)
    (hAt : upper T = lower T + 1)
    (a : Nat) (ha : a ≤ r) :
    integerGraphAgeCanonical d ell
      (rawCliqueBlockBound ell a upper T) =
      if a < r then upper else lower := by
  apply canonical_cover_block_all_stages ell r
    (IsIntegerGraphAge d ell)
    (integerGraphAgeCanonical d ell)
    lower upper T hCover hEll hAt
  · intro B hLB
    exact integerGraphAgeCanonical_is_age d ell B lower
      hCover.lower_age hLB
  · intro B
    exact integerGraphAgeCanonical_le_raw d ell B
  · intro B H hAge hHB
    exact integerGraphAgeCanonical_greatest d ell B H hAge hHB
  · exact ha

end Kk
