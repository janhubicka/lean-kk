import Kk.NonedgeHistoryCount
import Kk.IntegerWitnessCanonical

/-!
# The nonedge machine uses the repository's actual integer graph ages

English proof and hostile checks precede this file in
`docs/nonedge_profile_bridge_20261122.md`.

For d=2 and ell=4 there are exactly three nonempty supports. The
finite-history capacity triple is equivalent to the existing normalized
integer-witness age function on these supports. All natural-number
weights are covered, with empty support zero, and the full age posets
and their Hasse covers agree. This is not an actual-history or BRD
realization theorem.
-/

namespace Kk.NonedgeProfileBridge

open NonedgeHistory

abbrev Support := IntegerGraphSupport 2 4
abbrev Weights := IntegerCliqueWeights 2 4

def leftSupport : Support := ⟨{0}, by decide⟩
def rightSupport : Support := ⟨{1}, by decide⟩
def jointSupport : Support := ⟨{0, 1}, by decide⟩

/-- Exactly the three nonempty supports of two labelled sorts. -/
theorem support_cases (T : Support) :
    T = leftSupport ∨ T = rightSupport ∨ T = jointSupport := by
  revert T
  decide

theorem all_support_cases (S : Finset (Fin 2)) :
    S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {0, 1} := by
  revert S
  decide

/-- The literal extension of a capacity triple to all supports. -/
def onAllSupports (p : Bounds) (S : Finset (Fin 2)) : Nat :=
  if 0 ∈ S then
    if 1 ∈ S then jointCapacity p else leftCapacity p
  else if 1 ∈ S then rightCapacity p else 0

@[simp] theorem onAllSupports_empty (p : Bounds) :
    onAllSupports p ∅ = 0 := by simp [onAllSupports]

@[simp] theorem onAllSupports_left (p : Bounds) :
    onAllSupports p {0} = leftCapacity p := by simp [onAllSupports]

@[simp] theorem onAllSupports_right (p : Bounds) :
    onAllSupports p {1} = rightCapacity p := by simp [onAllSupports]

@[simp] theorem onAllSupports_joint (p : Bounds) :
    onAllSupports p {0, 1} = jointCapacity p := by simp [onAllSupports]

/-- The same data on the repository's nonempty-support subtype. -/
def toAge (p : Bounds) (T : Support) : Nat := onAllSupports p T.1

@[simp] theorem toAge_left (p : Bounds) :
    toAge p leftSupport = leftCapacity p := by simp [toAge, leftSupport]

@[simp] theorem toAge_right (p : Bounds) :
    toAge p rightSupport = rightCapacity p := by simp [toAge, rightSupport]

@[simp] theorem toAge_joint (p : Bounds) :
    toAge p jointSupport = jointCapacity p := by simp [toAge, jointSupport]

/-- Arbitrary natural-number vectors, including repeated sort labels. -/
def pairVector (x y : Nat) : Fin 2 → Nat := ![x, y]

/-- The empty support adds exactly the harmless inequality 0 <= 0. -/
theorem all_support_feasibility (p : Bounds) (x y : Nat) :
    (∀ S : Finset (Fin 2),
      S.sum (pairVector x y) ≤ onAllSupports p S) ↔ Feasible p x y := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa [pairVector] using h {0}
    · simpa [pairVector] using h {1}
    · simpa [pairVector] using h {0, 1}
  · intro h S
    rcases all_support_cases S with rfl | rfl | rfl | rfl
    · simp
    · simpa [pairVector] using h.1
    · simpa [pairVector] using h.2.1
    · simpa [pairVector] using h.2.2

@[simp] theorem support_weight_left (w : Weights) :
    integerCliqueOnSupport w leftSupport = (w.1 0).val := by
  simp [integerCliqueOnSupport, leftSupport]

@[simp] theorem support_weight_right (w : Weights) :
    integerCliqueOnSupport w rightSupport = (w.1 1).val := by
  simp [integerCliqueOnSupport, rightSupport]

@[simp] theorem support_weight_joint (w : Weights) :
    integerCliqueOnSupport w jointSupport = (w.1 0).val + (w.1 1).val := by
  simp [integerCliqueOnSupport, jointSupport]

/-- Literal equivalence with the existing integer-witness feasibility. -/
theorem weights_feasible_iff (p : Bounds) (w : Weights) :
    WitnessRespects integerCliqueOnSupport (toAge p) w ↔
      Feasible p (w.1 0).val (w.1 1).val := by
  constructor
  · intro h
    exact ⟨by simpa using h leftSupport,
      by simpa using h rightSupport, by simpa using h jointSupport⟩
  · intro h T
    rcases support_cases T with rfl | rfl | rfl
    · simpa using h.1
    · simpa using h.2.1
    · simpa using h.2.2

/-- Feasibility itself implies normalization; no large feasible vector
is silently discarded by the repository's bounded witness subtype. -/
def weightsOfPair (x y : Nat) (h : x + y ≤ 3) : Weights :=
  ⟨![⟨x, by omega⟩, ⟨y, by omega⟩], by
    simpa [Fin.sum_univ_two] using h⟩

@[simp] theorem weightsOfPair_left (x y : Nat) (h : x + y ≤ 3) :
    ((weightsOfPair x y h).1 0).val = x := rfl

@[simp] theorem weightsOfPair_right (x y : Nat) (h : x + y ≤ 3) :
    ((weightsOfPair x y h).1 1).val = y := rfl

theorem feasible_iff_existing_weights (p : Bounds) (x y : Nat) :
    Feasible p x y ↔ ∃ w : Weights,
      (w.1 0).val = x ∧ (w.1 1).val = y ∧
      WitnessRespects integerCliqueOnSupport (toAge p) w := by
  constructor
  · intro h
    have hc : jointCapacity p ≤ 3 := by
      dsimp [jointCapacity, capacity]
      have := p.2.2.isLt
      omega
    let w := weightsOfPair x y (h.2.2.trans hc)
    refine ⟨w, rfl, rfl, ?_⟩
    exact (weights_feasible_iff p w).2 h
  · rintro ⟨w, hx, hy, hw⟩
    have := (weights_feasible_iff p w).1 hw
    simpa [hx, hy] using this

/-- Canonicality is the existing saturation predicate, on precisely the
same normalized vectors and supports. -/
theorem toAge_is_age_iff (p : Bounds) :
    IsIntegerGraphAge 2 4 (toAge p) ↔ IsProfile p := by
  constructor
  · intro h
    apply (isProfile_iff_exactCapacities p).2
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨w, hw, he⟩ := h.2 leftSupport
      exact ⟨(w.1 0).val, (w.1 1).val,
        (weights_feasible_iff p w).1 hw, by simpa using he⟩
    · obtain ⟨w, hw, he⟩ := h.2 rightSupport
      exact ⟨(w.1 0).val, (w.1 1).val,
        (weights_feasible_iff p w).1 hw, by simpa using he⟩
    · obtain ⟨w, hw, he⟩ := h.2 jointSupport
      exact ⟨(w.1 0).val, (w.1 1).val,
        (weights_feasible_iff p w).1 hw, by simpa using he⟩
  · intro hp
    have hSat := (isProfile_iff_exactCapacities p).1 hp
    constructor
    · intro T
      rcases support_cases T with rfl | rfl | rfl <;>
        simp only [toAge_left, toAge_right, toAge_joint]
      · dsimp [leftCapacity, capacity]
        have := p.1.isLt
        omega
      · dsimp [rightCapacity, capacity]
        have := p.2.1.isLt
        omega
      · dsimp [jointCapacity, capacity]
        have := p.2.2.isLt
        omega
    · intro T
      rcases support_cases T with rfl | rfl | rfl
      · obtain ⟨x, y, hxy, hx⟩ := hSat.1
        obtain ⟨w, hwx, hwy, hw⟩ := (feasible_iff_existing_weights p x y).1 hxy
        exact ⟨w, hw, by simpa using hwx.trans hx⟩
      · obtain ⟨x, y, hxy, hy⟩ := hSat.2.1
        obtain ⟨w, hwx, hwy, hw⟩ := (feasible_iff_existing_weights p x y).1 hxy
        exact ⟨w, hw, by simpa using hwy.trans hy⟩
      · obtain ⟨x, y, hxy, he⟩ := hSat.2.2
        obtain ⟨w, hwx, hwy, hw⟩ := (feasible_iff_existing_weights p x y).1 hxy
        refine ⟨w, hw, ?_⟩
        simpa [hwx, hwy] using he

/-- Recover each bounded positive capacity as the machine's `Fin 3`. -/
def rankOfCapacity (n : Nat) (h : 1 ≤ n ∧ n ≤ 3) : Rank :=
  ⟨n - 1, by omega⟩

@[simp] theorem capacity_rankOfCapacity (n : Nat) (h : 1 ≤ n ∧ n ≤ 3) :
    capacity (rankOfCapacity n h) = n := by
  simp only [capacity, rankOfCapacity]
  omega

def boundsOfAge (F : Support → Nat) (h : IsIntegerGraphAge 2 4 F) : Bounds :=
  (rankOfCapacity (F leftSupport) (h.1 leftSupport),
    rankOfCapacity (F rightSupport) (h.1 rightSupport),
    rankOfCapacity (F jointSupport) (h.1 jointSupport))

/-- Every generic canonical age is represented; no intermediate age is
excluded merely because it was not declared as a machine state. -/
theorem toAge_boundsOfAge (F : Support → Nat) (h : IsIntegerGraphAge 2 4 F) :
    toAge (boundsOfAge F h) = F := by
  funext T
  rcases support_cases T with rfl | rfl | rfl <;>
    simp [boundsOfAge, leftCapacity, rightCapacity, jointCapacity]

theorem toAge_injective : Function.Injective toAge := by
  intro p q h
  have h0 := congrFun h leftSupport
  have h1 := congrFun h rightSupport
  have h2 := congrFun h jointSupport
  simp only [toAge_left, toAge_right, toAge_joint,
    leftCapacity, rightCapacity, jointCapacity, capacity] at h0 h1 h2
  apply Prod.ext
  · apply Fin.ext
    omega
  · apply Prod.ext <;> apply Fin.ext <;> omega

theorem exists_unique_profile (F : Support → Nat) (h : IsIntegerGraphAge 2 4 F) :
    ∃! p : Bounds, IsProfile p ∧ toAge p = F := by
  let p := boundsOfAge F h
  have hpEq : toAge p = F := toAge_boundsOfAge F h
  refine ⟨p, ⟨?_, hpEq⟩, ?_⟩
  · apply (toAge_is_age_iff p).1
    rw [hpEq]
    exact h
  · intro q hq
    exact toAge_injective (hq.2.trans hpEq.symm)

/-- Coordinate order is literally the repository's pointwise age order. -/
theorem below_iff_ageLe (q p : Bounds) :
    Below q p ↔ AgeLe (toAge q) (toAge p) := by
  constructor
  · intro h T
    rcases support_cases T with rfl | rfl | rfl
    · simpa using h.1
    · simpa using h.2.1
    · simpa using h.2.2
  · intro h
    exact ⟨by simpa using h leftSupport,
      by simpa using h rightSupport, by simpa using h jointSupport⟩

/-- The FULL canonical-age Hasse cover, including arbitrary generic
intermediate age functions, agrees with the history machine's cover. -/
theorem covers_iff_ageCover (q p : Bounds) :
    Covers q p ↔ AgeCover (IsIntegerGraphAge 2 4) (toAge q) (toAge p) := by
  constructor
  · rintro ⟨hq, hp, hle, hne, hCover⟩
    refine ⟨(toAge_is_age_iff q).2 hq, (toAge_is_age_iff p).2 hp,
      (below_iff_ageLe q p).1 hle, ?_, ?_⟩
    · exact fun h => hne (toAge_injective h)
    · intro F hF hqF hFp
      obtain ⟨r, ⟨hr, hrF⟩, _⟩ := exists_unique_profile F hF
      have hqr : Below q r := (below_iff_ageLe q r).2 (by simpa [hrF] using hqF)
      have hrp : Below r p := (below_iff_ageLe r p).2 (by simpa [hrF] using hFp)
      rcases hCover r hr hqr hrp with hrq | hrp
      · exact Or.inl (by simpa [hrq] using hrF.symm)
      · exact Or.inr (by simpa [hrp] using hrF.symm)
  · intro h
    refine ⟨(toAge_is_age_iff q).1 h.lower_age,
      (toAge_is_age_iff p).1 h.upper_age,
      (below_iff_ageLe q p).2 h.le, ?_, ?_⟩
    · exact fun he => h.strict (congrArg toAge he)
    · intro r hr hqr hrp
      rcases h.no_intermediate (toAge r) ((toAge_is_age_iff r).2 hr)
        ((below_iff_ageLe q r).1 hqr) ((below_iff_ageLe r p).1 hrp) with h | h
      · exact Or.inl (toAge_injective h)
      · exact Or.inr (toAge_injective h)

/-- The existing canonicalizer fixes exactly these canonical profiles. -/
theorem canonical_fixed (p : Bounds) (hp : IsProfile p) :
    integerGraphAgeCanonical 2 4 (toAge p) = toAge p := by
  funext T
  apply Nat.le_antisymm
  · exact integerGraphAgeCanonical_le_raw 2 4 (toAge p) T
  · exact integerGraphAgeCanonical_greatest 2 4 (toAge p) (toAge p)
      ((toAge_is_age_iff p).2 hp) (fun _ => le_refl _) T

end Kk.NonedgeProfileBridge
