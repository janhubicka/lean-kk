import Kk.UniversalFutureDisjointCliques
import Kk.ConcreteCanonicalMaximizers
import Mathlib.Tactic

/-!
# Exact full clique profile of one universal finite ordinary-L future

English-first mathematical proof and hostile audit:
  docs/universal_future_exact_profile_english_audit.md

For an arbitrary raw bound B, the single constructed finite future W_B
realises EXACTLY the B-feasible normalised labelled clique vectors,
under equality of ALL admissible support counts simultaneously.
Its finite support-clique capacity equals the actual integer age
canonicalizer G_B(T) at every support T.

This is a FINITE standalone ordinary-L graph. It does not realise any
specified extension over a fixed Henson past, or full numerical-H/Kpt
auxiliary E/parameter-closed corrected B3 source types or labelled orbits.
-/

namespace Kk

/-- A normalized labelled vector has a realized full support-count
profile if an ACTUAL directed clique of the one universal future
agrees with its multiplicity on every admissible support. -/
def IsRealizedUniversalWitnessProfile
    (d ell : Nat)
    (B : IntegerGraphSupport d ell → Nat)
    (w : IntegerCliqueWeights d ell) : Prop :=
  ∃ s : Finset (UniversalWitnessVertex d ell),
    s ⊆ universalWitnessFuture d ell B ∧
    IsUniversalWitnessClique s ∧
    ∀ T : IntegerGraphSupport d ell,
      (s.filter (fun v => v.2.1 ∈ T.1)).card =
        integerCliqueOnSupport w T

/-- The realized full labelled-clique support profiles in the ONE
chosen finite graph are exactly the feasible normalized vectors,
even when B is not a canonical age. All support counts must agree
at once; an arbitrary fixed W may not have this universality. -/
theorem universalWitnessFuture_exact_profile_iff
    (d ell : Nat) (hell : 0 < ell)
    (B : IntegerGraphSupport d ell → Nat)
    (w : IntegerCliqueWeights d ell) :
    w ∈ feasibleIntegerCliqueVectors d ell B ↔
      IsRealizedUniversalWitnessProfile d ell B w := by
  classical
  constructor
  · intro hw
    obtain ⟨hSub, hClique, hCounts, _⟩ :=
      universalWitnessFuture_realizes_every_feasible d ell hell B w hw
    exact ⟨universalWitnessComponent w, hSub, hClique, hCounts⟩
  · rintro ⟨s, hSub, hClique, hCounts⟩
    change w ∈ Finset.univ.filter
      (WitnessRespects
        (integerCliqueOnSupport (d := d) (ell := ell)) B)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro T
    rw [← hCounts T]
    exact universalWitnessFuture_clique_respects_raw
      d ell hell B s hSub hClique T

/-- Every clique's multiplicity on support T is at most the
CANONICAL bound G_B(T), not only the potentially weaker raw B(T).
The proof uses feasible-component classification and the entire
joint feasibility record of its component index. -/
theorem universalWitnessFuture_clique_support_le_canonical
    (d ell : Nat) (hell : 0 < ell)
    (B : IntegerGraphSupport d ell → Nat)
    (s : Finset (UniversalWitnessVertex d ell))
    (hSub : s ⊆ universalWitnessFuture d ell B)
    (hClique : IsUniversalWitnessClique s)
    (T : IntegerGraphSupport d ell) :
    (s.filter (fun v => v.2.1 ∈ T.1)).card ≤
      integerGraphAgeCanonical d ell B T := by
  classical
  obtain ⟨w, hw, hsComp⟩ :=
    universalWitnessFuture_clique_in_feasible_component
      d ell hell B s hSub hClique
  have hFilterSub :
      s.filter (fun v => v.2.1 ∈ T.1) ⊆
        (universalWitnessComponent w).filter
          (fun v => v.2.1 ∈ T.1) := by
    intro v hv
    exact Finset.mem_filter.mpr
      ⟨hsComp (Finset.mem_filter.mp hv).1,
        (Finset.mem_filter.mp hv).2⟩
  have hBound : (s.filter (fun v => v.2.1 ∈ T.1)).card ≤
      integerCliqueOnSupport w T := by
    exact (Finset.card_le_card hFilterSub).trans
      (le_of_eq (universalWitnessComponent_support_card w T))
  have hwB : WitnessRespects
      (integerCliqueOnSupport (d := d) (ell := ell)) B w := by
    change w ∈ Finset.univ.filter
      (WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell)) B)
      at hw
    exact (Finset.mem_filter.mp hw).2
  exact hBound.trans
    (witnessValue_le_canonical
      (integerCliqueOnSupport (d := d) (ell := ell)) B w hwB T)

/-- For each coordinate T, a genuine directed clique in the SAME
universal finite W_B ATTAINS its canonical G_B(T) value. The
maximizing clique may depend on T. -/
theorem universalWitnessFuture_clique_attains_canonical
    (d ell : Nat) (hell : 0 < ell)
    (B : IntegerGraphSupport d ell → Nat)
    (T : IntegerGraphSupport d ell) :
    ∃ s : Finset (UniversalWitnessVertex d ell),
      s ⊆ universalWitnessFuture d ell B ∧
      IsUniversalWitnessClique s ∧
      (s.filter (fun v => v.2.1 ∈ T.1)).card =
        integerGraphAgeCanonical d ell B T := by
  classical
  obtain ⟨w, hwB, hwMax⟩ :=
    integerGraphAgeCanonical_has_feasible_maximizer
      d ell hell B T
  have hw : w ∈ feasibleIntegerCliqueVectors d ell B := by
    change w ∈ Finset.univ.filter
      (WitnessRespects
        (integerCliqueOnSupport (d := d) (ell := ell)) B)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwB⟩
  obtain ⟨hSub, hClique, hCounts, _⟩ :=
    universalWitnessFuture_realizes_every_feasible d ell hell B w hw
  refine ⟨universalWitnessComponent w, hSub, hClique, ?_⟩
  exact (hCounts T).trans hwMax

/-- Maximum support size of a directed clique in the one explicitly
constructed universal finite L future. This uses an actual powerset
filter of the finite vertex pool, not an abstract age evaluator. -/
noncomputable def universalWitnessFutureSupportCapacity
    (d ell : Nat)
    (B : IntegerGraphSupport d ell → Nat)
    (T : IntegerGraphSupport d ell) : Nat := by
  classical
  exact ((universalWitnessFuture d ell B).powerset.filter
    IsUniversalWitnessClique).sup
      (fun s => (s.filter (fun v => v.2.1 ∈ T.1)).card)

/-- Exact combinatorial representation of canonical integer graph ages:
the canonical G_B(T) is the MAXIMUM T-labelled cardinality among
all directed cliques in one finite ordinary-L graph W_B. This is a
standalone finite age representation, NOT a relative Henson orbit. -/
theorem universalWitnessFuture_support_capacity_eq_canonical
    (d ell : Nat) (hell : 0 < ell)
    (B : IntegerGraphSupport d ell → Nat)
    (T : IntegerGraphSupport d ell) :
    universalWitnessFutureSupportCapacity d ell B T =
      integerGraphAgeCanonical d ell B T := by
  classical
  apply Nat.le_antisymm
  · unfold universalWitnessFutureSupportCapacity
    apply Finset.sup_le
    intro s hs
    obtain ⟨hsPow, hc⟩ := Finset.mem_filter.mp hs
    exact universalWitnessFuture_clique_support_le_canonical
      d ell hell B s (Finset.mem_powerset.mp hsPow) hc T
  · obtain ⟨s, hSub, hClique, hMax⟩ :=
      universalWitnessFuture_clique_attains_canonical
        d ell hell B T
    unfold universalWitnessFutureSupportCapacity
    have hMem : s ∈
        ((universalWitnessFuture d ell B).powerset.filter
          IsUniversalWitnessClique) :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hSub, hClique⟩
    have hSup := Finset.le_sup
      (f := fun s : Finset (UniversalWitnessVertex d ell) =>
        (s.filter (fun v => v.2.1 ∈ T.1)).card) hMem
    rw [hMax] at hSup
    exact hSup

#print axioms universalWitnessFuture_exact_profile_iff
#print axioms universalWitnessFuture_clique_support_le_canonical
#print axioms universalWitnessFuture_clique_attains_canonical
#print axioms universalWitnessFuture_support_capacity_eq_canonical

end Kk
