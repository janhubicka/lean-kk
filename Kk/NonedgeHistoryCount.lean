import Mathlib.Tactic

/-!
# Exact count of the proposed non-edge history machine

The finite states here are derived from integer clique-multiplicity
constraints on one or two active sorts, with the K4-free capacity bound
three. Histories have exactly one split and two zero-coding events.

We prove termination, a soundness/completeness theorem for the finite
enumerator, and the kernel-checked count 24 (with subtotals 16, 6, 2).
No Ramsey upper bound, unavoidability assertion, or correspondence with
successor-tree source orbits is asserted in this file. Those are separate
mathematical interfaces; counting this machine does not discharge them.

The English proof and adversarial audit preceded this implementation in
`docs/nonedge_history_count_20261122.md`.
-/

namespace Kk.NonedgeHistory

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- A live unary clique capacity, represented by its value minus one. -/
abbrev Rank := Fin 3

def capacity (r : Rank) : Nat := r.val + 1

/-- Bounds on the left, right, and joint nonempty supports. No table of
proposed diaries is used to define this ambient space. -/
abbrev Bounds := Rank × Rank × Rank

def leftCapacity (p : Bounds) : Nat := capacity p.1
def rightCapacity (p : Bounds) : Nat := capacity p.2.1
def jointCapacity (p : Bounds) : Nat := capacity p.2.2

/-- A clique may contain several vertices of either sort. -/
def Feasible (p : Bounds) (x y : Nat) : Prop :=
  x ≤ leftCapacity p ∧ y ≤ rightCapacity p ∧ x + y ≤ jointCapacity p

/-- Every stated support capacity has a saturating integer witness. -/
def HasExactCapacities (p : Bounds) : Prop :=
  (∃ x y, Feasible p x y ∧ x = leftCapacity p) ∧
  (∃ x y, Feasible p x y ∧ y = rightCapacity p) ∧
  (∃ x y, Feasible p x y ∧ x + y = jointCapacity p)

/-- These inequalities characterize canonical profiles; this is proved
equivalent to saturation, rather than posited as a list of valid states. -/
def IsProfile (p : Bounds) : Prop :=
  leftCapacity p ≤ jointCapacity p ∧
  rightCapacity p ≤ jointCapacity p ∧
  jointCapacity p ≤ leftCapacity p + rightCapacity p

instance (p : Bounds) : Decidable (IsProfile p) := by
  unfold IsProfile
  infer_instance

theorem isProfile_iff_exactCapacities (p : Bounds) :
    IsProfile p ↔ HasExactCapacities p := by
  constructor
  · rintro ⟨ha, hb, hab⟩
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨leftCapacity p, 0, ?_, rfl⟩
      unfold Feasible
      omega
    · refine ⟨0, rightCapacity p, ?_, rfl⟩
      unfold Feasible
      omega
    · refine ⟨leftCapacity p, jointCapacity p - leftCapacity p, ?_, ?_⟩
      · unfold Feasible
        omega
      · omega
  · rintro ⟨⟨x, y, hxy, hx⟩, ⟨u, v, huv, hv⟩,
      ⟨z, w, hzw, hsum⟩⟩
    unfold Feasible at hxy huv hzw
    unfold IsProfile
    omega

/-- The complete abstract integer two-sort profile space, including
profiles unreachable from the particular initial split. This does not
assert that each profile is a distinct actual Henson type front. -/
def canonicalProfiles : Finset Bounds := Finset.univ.filter IsProfile

theorem canonicalProfiles_card : canonicalProfiles.card = 13 := by decide

def Below (q p : Bounds) : Prop :=
  leftCapacity q ≤ leftCapacity p ∧
  rightCapacity q ≤ rightCapacity p ∧
  jointCapacity q ≤ jointCapacity p

instance (q p : Bounds) : Decidable (Below q p) := by
  unfold Below
  infer_instance

/-- For canonical profiles, coordinate order agrees exactly with
inclusion of the feasible integer clique-multiplicity classes. -/
theorem below_iff_feasible_inclusion (q p : Bounds) (hq : IsProfile q) :
    Below q p ↔ ∀ x y, Feasible q x y → Feasible p x y := by
  constructor
  · intro h x y hxy
    unfold Below at h
    unfold Feasible at hxy ⊢
    omega
  · intro h
    obtain ⟨⟨x, y, hxy, hx⟩, ⟨u, v, huv, hv⟩,
      ⟨z, w, hzw, hsum⟩⟩ := (isProfile_iff_exactCapacities q).mp hq
    have hxy' := h x y hxy
    have huv' := h u v huv
    have hzw' := h z w hzw
    unfold Feasible at hxy' huv' hzw'
    unfold Below
    omega

/-- Hasse covers in the full canonical profile poset. In particular an
unreachable intermediate profile still rules out a spurious cover. -/
def Covers (q p : Bounds) : Prop :=
  IsProfile q ∧ IsProfile p ∧ Below q p ∧ q ≠ p ∧
    ∀ r : Bounds, IsProfile r → Below q r → Below r p → r = q ∨ r = p

instance (q p : Bounds) : Decidable (Covers q p) := by
  unfold Covers
  infer_instance

def coverEdges : Finset (Bounds × Bounds) :=
  Finset.univ.filter (fun edge => Covers edge.1 edge.2)

theorem coverEdges_card : coverEdges.card = 18 := by decide

/-- The right child sees the fresh marker. Its capacity is at most two;
the merged children obey the old unary total bound. -/
def splitProfile (r : Rank) : Bounds := (r, min r 1, r)

theorem splitProfile_capacities (r : Rank) :
    leftCapacity (splitProfile r) = capacity r ∧
    rightCapacity (splitProfile r) = min (capacity r) 2 ∧
    jointCapacity (splitProfile r) = capacity r := by
  revert r
  decide

theorem splitProfile_isProfile (r : Rank) : IsProfile (splitProfile r) := by
  revert r
  decide

/-- The canonical profiles that lie below some permitted split. This
excludes the three abstract profiles with right capacity three. -/
def profilesBelowSplits : Finset Bounds :=
  canonicalProfiles.filter (fun p => ∃ r : Rank, Below p (splitProfile r))

theorem profilesBelowSplits_card : profilesBelowSplits.card = 10 := by decide

/-- The split formula is exactly the integer feasibility constraint,
not merely a declared transition table. -/
theorem splitProfile_feasible (r : Rank) (x y : Nat) :
    Feasible (splitProfile r) x y ↔ x + y ≤ capacity r ∧ y ≤ 2 := by
  obtain ⟨ha, hb, hc⟩ := splitProfile_capacities r
  simp only [Feasible, ha, hb, hc, le_min_iff]
  omega

/-- Keeping the phases explicit prevents a second split or an early
terminal success, and retains the unary cover events in the history. -/
inductive State where
  | beforeSplit (r : Rank)
  | pair (p : Bounds)
  | afterCode (r : Rank)
  | done
  deriving DecidableEq, Fintype

/-- Left and right coding are distinct even if their successor states
coincide. Lowering events record their destination profile or rank. -/
inductive Event where
  | lowerOne (r : Rank)
  | lowerPair (p : Bounds)
  | split
  | codeLeft
  | codeRight
  | codeLast
  deriving DecidableEq, Fintype

/-- Literal legal transitions. Coding is independent: the coded sort has
capacity one and adjoining it does not reduce the surviving capacity. -/
def next : State → Event → Option State
  | .beforeSplit r, .lowerOne q =>
      if capacity q + 1 = capacity r then some (.beforeSplit q) else none
  | .beforeSplit r, .split => some (.pair (splitProfile r))
  | .pair p, .lowerPair q =>
      if Covers q p then some (.pair q) else none
  | .pair p, .codeLeft =>
      if IsProfile p ∧ leftCapacity p = 1 ∧ jointCapacity p = rightCapacity p
      then some (.afterCode p.2.1) else none
  | .pair p, .codeRight =>
      if IsProfile p ∧ rightCapacity p = 1 ∧ jointCapacity p = leftCapacity p
      then some (.afterCode p.1) else none
  | .afterCode r, .lowerOne q =>
      if capacity q + 1 = capacity r then some (.afterCode q) else none
  | .afterCode r, .codeLast =>
      if capacity r = 1 then some .done else none
  | _, _ => none

def ValidState : State → Prop
  | .pair p => IsProfile p
  | _ => True

instance (s : State) : Decidable (ValidState s) := by
  cases s <;> unfold ValidState <;> infer_instance

/-- All legal successors have canonical pair profiles. The larger
ambient type of triples introduces no invalid legal transition. -/
theorem next_valid {s t : State} {e : Event} (h : next s e = some t) :
    ValidState t := by
  have hall : ∀ s e,
      match next s e with
      | none => True
      | some t => ValidState t := by
    let (s : State) (e : Event) : Decidable
        (match next s e with
        | none => True
        | some t => ValidState t) := by
      split <;> infer_instance
    decide
  simpa only [h] using hall s e

/-- Every transition decreases this measure, including the split. -/
def measure : State → Nat
  | .beforeSplit r => 3 * capacity r + 1
  | .pair p => leftCapacity p + rightCapacity p + jointCapacity p
  | .afterCode r => capacity r
  | .done => 0

theorem next_decreases_all : ∀ s e,
    match next s e with
    | none => True
    | some t => measure t < measure s := by
  let (s : State) (e : Event) : Decidable
      (match next s e with
      | none => True
      | some t => measure t < measure s) := by
    split <;> infer_instance
  decide

theorem next_measure {s t : State} {e : Event}
    (h : next s e = some t) : measure t < measure s := by
  have hdec := next_decreases_all s e
  simpa only [h] using hdec

/-- An accepted history is any complete finite event list. There is no
fuel or numerical cutoff in this mathematical definition. -/
def Accepts : State → List Event → Prop
  | s, [] => s = .done
  | s, e :: es =>
      match next s e with
      | none => False
      | some t => Accepts t es

def remainingSplits : State → Nat
  | .beforeSplit _ => 1
  | _ => 0

def remainingCodes : State → Nat
  | .beforeSplit _ => 2
  | .pair _ => 2
  | .afterCode _ => 1
  | .done => 0

def splitCost : Event → Nat
  | .split => 1
  | _ => 0

def codeCost : Event → Nat
  | .codeLeft | .codeRight | .codeLast => 1
  | _ => 0

def splitCount : List Event → Nat
  | [] => 0
  | e :: es => splitCost e + splitCount es

def codeCount : List Event → Nat
  | [] => 0
  | e :: es => codeCost e + codeCount es

theorem next_inventory_all : ∀ s e,
    match next s e with
    | none => True
    | some t =>
        remainingSplits s = splitCost e + remainingSplits t ∧
        remainingCodes s = codeCost e + remainingCodes t := by
  let (s : State) (e : Event) : Decidable
      (match next s e with
      | none => True
      | some t =>
          remainingSplits s = splitCost e + remainingSplits t ∧
          remainingCodes s = codeCost e + remainingCodes t) := by
    split <;> infer_instance
  decide

/-- This invariant certifies the number and kind of events in every
complete history, independently of the numerical enumeration. -/
theorem accepts_inventory {s : State} {es : List Event}
    (h : Accepts s es) :
    splitCount es = remainingSplits s ∧ codeCount es = remainingCodes s := by
  induction es generalizing s with
  | nil =>
      have hs : s = .done := h
      subst s
      simp [splitCount, codeCount, remainingSplits, remainingCodes]
  | cons e es ih =>
      cases hn : next s e with
      | none => simp [Accepts, hn] at h
      | some t =>
          have ht : Accepts t es := by simpa only [Accepts, hn] using h
          obtain ⟨hsplit, hcode⟩ := ih ht
          have hstep := next_inventory_all s e
          simp only [hn] at hstep
          simp only [splitCount, codeCount]
          omega

/-- All accepted histories satisfy a proved length bound. -/
theorem accepts_length_le {s : State} {es : List Event}
    (h : Accepts s es) : es.length ≤ measure s := by
  induction es generalizing s with
  | nil => simp
  | cons e es ih =>
      cases hn : next s e with
      | none => simp [Accepts, hn] at h
      | some t =>
          have ht : Accepts t es := by simpa only [Accepts, hn] using h
          have htail := ih ht
          have hstep := next_measure hn
          simp only [List.length_cons]
          omega

/-- A finite enumerator, to be connected to the unbounded `Accepts`
predicate by a soundness and completeness theorem. -/
def histories : Nat → State → Finset (List Event)
  | 0, s => if s = .done then {[]} else ∅
  | fuel + 1, s =>
      (if s = .done then {[]} else ∅) ∪
      Finset.univ.biUnion (fun e =>
        match next s e with
        | none => ∅
        | some t => (histories fuel t).image (List.cons e))

theorem nil_mem_histories (fuel : Nat) (s : State) :
    [] ∈ histories fuel s ↔ s = .done := by
  cases fuel with
  | zero => by_cases h : s = .done <;> simp [histories, h]
  | succ fuel =>
      simp only [histories, Finset.mem_union, Finset.mem_biUnion,
        Finset.mem_univ, true_and]
      have hnone : ¬ ∃ e : Event,
          [] ∈ match next s e with
            | none => (∅ : Finset (List Event))
            | some t => (histories fuel t).image (List.cons e) := by
        rintro ⟨e, he⟩
        cases hn : next s e <;> simp [hn] at he
      simp only [hnone, or_false]
      by_cases h : s = .done <;> simp [h]

theorem cons_mem_histories (fuel : Nat) (s : State) (e : Event) (es : List Event) :
    e :: es ∈ histories (fuel + 1) s ↔
      ∃ t, next s e = some t ∧ es ∈ histories fuel t := by
  simp only [histories, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_univ, true_and]
  have hnot : ¬ e :: es ∈ (if s = .done then {[]} else (∅ : Finset (List Event))) := by
    split <;> simp
  simp only [hnot, false_or]
  constructor
  · rintro ⟨f, hf⟩
    cases hn : next s f with
    | none => simp [hn] at hf
    | some t =>
        simp only [hn, Finset.mem_image, List.cons.injEq] at hf
        obtain ⟨ys, hys, hfe, hyes⟩ := hf
        subst f
        subst ys
        exact ⟨t, hn, hys⟩
  · rintro ⟨t, ht, hes⟩
    refine ⟨e, ?_⟩
    rw [ht]
    exact Finset.mem_image.mpr ⟨es, hes, rfl⟩

/-- Enumeration is both sound and complete at every fuel. -/
theorem mem_histories_iff (fuel : Nat) (s : State) (es : List Event) :
    es ∈ histories fuel s ↔ Accepts s es ∧ es.length ≤ fuel := by
  induction fuel generalizing s es with
  | zero =>
      cases es with
      | nil => by_cases h : s = .done <;> simp [histories, Accepts, h]
      | cons e es => by_cases h : s = .done <;> simp [histories, h]
  | succ fuel ih =>
      cases es with
      | nil => simp [nil_mem_histories, Accepts]
      | cons e es =>
          rw [cons_mem_histories]
          cases hn : next s e with
          | none => simp [Accepts, hn]
          | some t =>
              simp only [hn, Option.some.injEq, exists_eq_left',
                Accepts, List.length_cons, Nat.succ_le_succ_iff]
              exact ih t es

/-- Using the proved measure removes the fuel bound from the enumerator. -/
theorem mem_histories_measure_iff (s : State) (es : List Event) :
    es ∈ histories (measure s) s ↔ Accepts s es := by
  rw [mem_histories_iff]
  exact ⟨And.left, fun h => ⟨h, accepts_length_le h⟩⟩

def initialState : State := .beforeSplit 2

theorem initial_accepts_one_split_two_codes {es : List Event}
    (h : Accepts initialState es) : splitCount es = 1 ∧ codeCount es = 2 :=
  accepts_inventory h

/-- This finite set is proved equal in membership to the unbounded
accepted-history predicate. The number 24 occurs only in the theorem. -/
def nonedgeHistories : Finset (List Event) := histories (measure initialState) initialState

theorem mem_nonedgeHistories_iff (es : List Event) :
    es ∈ nonedgeHistories ↔ Accepts initialState es :=
  mem_histories_measure_iff initialState es

theorem nonedge_histories_card : nonedgeHistories.card = 24 := by decide

/-- The unbounded mathematical history type, made finite using the
proved enumeration theorem. Its definition contains neither 24 nor fuel. -/
abbrev History := {es : List Event // Accepts initialState es}

instance historyFintype : Fintype History :=
  Fintype.ofFinset nonedgeHistories mem_nonedgeHistories_iff

theorem history_card : Fintype.card History = 24 := by
  exact (Fintype.card_ofFinset nonedgeHistories mem_nonedgeHistories_iff).trans
    nonedge_histories_card

/-- Continuations when the first split is at unary capacity three. -/
theorem split_capacity_three_card :
    (histories (measure (.pair (splitProfile 2))) (.pair (splitProfile 2))).card = 16 := by
  decide

/-- Continuations when the first split is at unary capacity two. -/
theorem split_capacity_two_card :
    (histories (measure (.pair (splitProfile 1))) (.pair (splitProfile 1))).card = 6 := by
  decide

/-- Distinct left-first and right-first codings at `(1,1,1)`. -/
theorem split_capacity_one_card :
    (histories (measure (.pair (splitProfile 0))) (.pair (splitProfile 0))).card = 2 := by
  decide

end Kk.NonedgeHistory
