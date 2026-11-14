import Kk.IntegerWitnessCanonical
import Mathlib.Tactic

/-!
# Track F: exact two-sort canonical clique-capacity formula

For the actual normalized integer-clique-vector K_ell graph-age
canonicalizer on two sorts, provided the RAW pair capacity B({0,1})
is ≤ ell-1, its canonical pair value is exactly the minimum of
the pair raw capacity and the sum of the two raw singleton capacities.

No fake abstract age interfaces, new axioms, or diary-lower-bound
claims. The branch-spectrum E/passing-bit equivalence will be
proved separately, using the true word-bound and this numeric lemma.
-/

namespace Kk

/-- The first nonempty singleton support of the actual two-sort model. -/
def trackFPairFirst (ell : Nat) (hell : 3 ≤ ell) :
    IntegerGraphSupport 2 ell := by
  refine ⟨{(0 : Fin 2)}, ?_⟩
  constructor
  · simp
  · simp
    omega

/-- The second singleton support. -/
def trackFPairSecond (ell : Nat) (hell : 3 ≤ ell) :
    IntegerGraphSupport 2 ell := by
  refine ⟨{(1 : Fin 2)}, ?_⟩
  constructor
  · simp
  · simp
    omega

/-- The full two-sort support, admissible because ell≥3. -/
def trackFPairBoth (ell : Nat) (hell : 3 ≤ ell) :
    IntegerGraphSupport 2 ell := by
  refine ⟨Finset.univ, ?_⟩
  constructor
  · decide
  · simp
    omega

/-- There are exactly three nonempty finite supports of two sorts. -/
private theorem trackFPair_nonempty_cases
    (S : Finset (Fin 2)) (hS : S.Nonempty) :
    S = {(0 : Fin 2)} ∨ S = {(1 : Fin 2)} ∨
      S = Finset.univ := by
  have hCases : ∀ Q : Finset (Fin 2), Q.Nonempty →
      Q = {(0 : Fin 2)} ∨ Q = {(1 : Fin 2)} ∨
        Q = Finset.univ := by decide
  exact hCases S hS

/-- The first singleton mass of an actual normalized clique vector. -/
theorem trackFPair_mass_first
    (ell : Nat) (hell : 3 ≤ ell)
    (w : IntegerCliqueWeights 2 ell) :
    integerCliqueOnSupport w (trackFPairFirst ell hell) =
      (w.1 0).val := by
  simp [integerCliqueOnSupport,trackFPairFirst]

/-- The second singleton mass. -/
theorem trackFPair_mass_second
    (ell : Nat) (hell : 3 ≤ ell)
    (w : IntegerCliqueWeights 2 ell) :
    integerCliqueOnSupport w (trackFPairSecond ell hell) =
      (w.1 1).val := by
  simp [integerCliqueOnSupport,trackFPairSecond]

/-- The actual full-support mass is exactly the sum of both weights. -/
theorem trackFPair_mass_both
    (ell : Nat) (hell : 3 ≤ ell)
    (w : IntegerCliqueWeights 2 ell) :
    integerCliqueOnSupport w (trackFPairBoth ell hell) =
      (w.1 0).val + (w.1 1).val := by
  simp [integerCliqueOnSupport,trackFPairBoth,Fin.sum_univ_two]

/-- The *actual finite normalized integer-witness canonicalizer*
has the expected exact two-sort capacity formula.

Raw B need NOT itself be an age or monotone. We only require
B({0,1})≤ell-1; this is automatic for literal common-symbol
raw ages of concrete words, but cannot be omitted in general. -/
theorem trackFPair_canonical_capacity
    (ell : Nat) (hell : 3 ≤ ell)
    (B : IntegerGraphSupport 2 ell → Nat)
    (hPairCap : B (trackFPairBoth ell hell) ≤ ell - 1) :
    integerGraphAgeCanonical 2 ell B (trackFPairBoth ell hell) =
      min (B (trackFPairBoth ell hell))
          (B (trackFPairFirst ell hell) +
           B (trackFPairSecond ell hell)) := by
  classical
  let s0 := trackFPairFirst ell hell
  let s1 := trackFPairSecond ell hell
  let sp := trackFPairBoth ell hell
  let M := min (B sp) (B s0 + B s1)
  have hMPair : M ≤ B sp := Nat.min_le_left _ _
  have hMSum : M ≤ B s0 + B s1 := Nat.min_le_right _ _
  have hMCap : M ≤ ell - 1 := hMPair.trans hPairCap
  let a := min (B s0) M
  let b := M - a
  have ha0 : a ≤ B s0 := Nat.min_le_left _ _
  have haM : a ≤ M := Nat.min_le_right _ _
  have hb1 : b ≤ B s1 := by omega
  have hsum : a + b = M := by omega
  let wa : Fin ell := ⟨a, by omega⟩
  let wb : Fin ell := ⟨b, by omega⟩
  let v : Fin 2 → Fin ell := fun i => if i = 0 then wa else wb
  have hTotal : Finset.univ.sum (fun i : Fin 2 => (v i).val) = M := by
    simp [v,wa,wb,Fin.sum_univ_two]
    omega
  let w : IntegerCliqueWeights 2 ell := ⟨v, by
    rw [hTotal]
    exact hMCap⟩
  have hW0 : integerCliqueOnSupport w s0 = a := by
    simp [s0,trackFPair_mass_first,w,v,wa]
  have hW1 : integerCliqueOnSupport w s1 = b := by
    simp [s1,trackFPair_mass_second,w,v,wb]
  have hWPair : integerCliqueOnSupport w sp = M := by
    rw [trackFPair_mass_both]
    simpa [w,v,wa,wb] using hsum
  have hFeasible : WitnessRespects
      (integerCliqueOnSupport (d := 2) (ell := ell)) B w := by
    intro U
    rcases trackFPair_nonempty_cases U.1 U.2.1 with h|h|h
    · have hEq : U = s0 := Subtype.ext h
      rw [hEq,hW0]
      exact ha0
    · have hEq : U = s1 := Subtype.ext h
      rw [hEq,hW1]
      exact hb1
    · have hEq : U = sp := Subtype.ext h
      rw [hEq,hWPair]
      exact hMPair
  have hLower : M ≤ integerGraphAgeCanonical 2 ell B sp := by
    rw [←hWPair]
    exact witnessValue_le_canonical
      (integerCliqueOnSupport (d := 2) (ell := ell))
      B w hFeasible sp
  have hUpper : integerGraphAgeCanonical 2 ell B sp ≤ M := by
    change (Finset.univ.filter
      (WitnessRespects
        (integerCliqueOnSupport (d := 2) (ell := ell)) B)).sup
      (fun w => integerCliqueOnSupport w sp) ≤ M
    apply Finset.sup_le
    intro w hw
    have hFw : WitnessRespects
      (integerCliqueOnSupport (d := 2) (ell := ell)) B w :=
      (Finset.mem_filter.mp hw).2
    have h0 := hFw s0
    have h1 := hFw s1
    have hp := hFw sp
    rw [trackFPair_mass_first] at h0
    rw [trackFPair_mass_second] at h1
    rw [trackFPair_mass_both] at hp ⊢
    apply le_min hp
    omega
  exact Nat.le_antisymm hUpper hLower

end Kk
