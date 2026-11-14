import Kk.TrackFBranchSpectrumCover
import Kk.TrackFPairCapacityTrue
import Mathlib.Tactic

/-!
# Track F: the literal concrete E predicate on two equal-length words

We do not define E by the desired numerical passing-bit condition.
Instead we implement all clauses of the manuscript's chronological
word predicate: distinct equal-length words, individual 1 symbols,
top symbol on at least one word, and a greatest positive symbol
seen individually on BOTH words that never occurs simultaneously.

For a genuine positive initial-segment spectrum on x and a top-length
initial segment on the coded branch j, E is exactly the condition
that the largest *simultaneously* shared positive symbol is < a_x.
The initial-segment premise cannot be dropped (K4 x=(1), j=(2)).
-/

namespace Kk

/-- A symbol n occurs simultaneously on both active branches of
the two-sort level at the SAME chronological coordinate. -/
def trackFPairSimultaneous
    (cols : List (Fin 2 → Nat)) (n : Nat) : Prop :=
  ∃ col ∈ cols, col 0 = n ∧ col 1 = n

/-- The manuscript's literal equal-length concrete edge predicate:
the first branch x=0 and the candidate coded branch j=1 have
different words, each has seen 1, one has seen ell-2, and the
*largest* positive symbol seen individually on both branches
has NOT occurred simultaneously at a common coordinate. -/
def trackFConcreteEdgePair
    (ell : Nat) (cols : List (Fin 2 → Nat)) : Prop :=
  (∃ col ∈ cols, col 0 ≠ col 1) ∧
    trackFSeenSymbol cols 0 1 ∧
    trackFSeenSymbol cols 1 1 ∧
    (trackFSeenSymbol cols 0 (ell - 2) ∨
     trackFSeenSymbol cols 1 (ell - 2)) ∧
    (∃ n : Nat,
       0 < n ∧
       trackFSeenSymbol cols 0 n ∧
       trackFSeenSymbol cols 1 n ∧
       (∀ m : Nat, n < m →
         ¬ (trackFSeenSymbol cols 0 m ∧
            trackFSeenSymbol cols 1 m)) ∧
       ¬ trackFPairSimultaneous cols n)

/-- Under the exact two initial-segment spectra of a genuine
candidate coding level, E says that x saw some positive symbol a,
but a was never written on both branches in the same column. -/
theorem trackFConcreteEdgePair_iff_no_top
    (ell a : Nat) (hell : 3 ≤ ell)
    (ha : a ≤ ell - 2)
    (cols : List (Fin 2 → Nat))
    (hX : trackFBranchInitial cols (0 : Fin 2) a)
    (hJ : trackFBranchInitial cols (1 : Fin 2) (ell - 2)) :
    trackFConcreteEdgePair ell cols ↔
      0 < a ∧ ¬ trackFPairSimultaneous cols a := by
  constructor
  · rintro ⟨_,hXOne,_,_,⟨n,hn,hNX,hNJ,hGreat,hNoN⟩⟩
    have haPos : 0 < a := by
      have hOneLeA := (hX 1 (by omega)).mp hXOne
      omega
    have hASeenX : trackFSeenSymbol cols 0 a :=
      (hX a haPos).mpr le_rfl
    have hASeenJ : trackFSeenSymbol cols 1 a :=
      (hJ a haPos).mpr ha
    have hnLeA : n ≤ a := (hX n hn).mp hNX
    have haLeN : a ≤ n := by
      by_contra h
      have hLess : n < a := by omega
      exact (hGreat a hLess) ⟨hASeenX,hASeenJ⟩
    have hEq : n = a := Nat.le_antisymm hnLeA haLeN
    exact ⟨haPos,by simpa only [←hEq] using hNoN⟩
  · rintro ⟨haPos,hNoA⟩
    have hSeenX1 : trackFSeenSymbol cols 0 1 :=
      (hX 1 (by omega)).mpr (by omega)
    have hSeenJ1 : trackFSeenSymbol cols 1 1 :=
      (hJ 1 (by omega)).mpr (by omega)
    have hSeenTopJ : trackFSeenSymbol cols 1 (ell - 2) :=
      (hJ (ell - 2) (by omega)).mpr le_rfl
    have hASeenX : trackFSeenSymbol cols 0 a :=
      (hX a haPos).mpr le_rfl
    have hASeenJ : trackFSeenSymbol cols 1 a :=
      (hJ a haPos).mpr ha
    have hDifferent : ∃ col ∈ cols, col 0 ≠ col 1 := by
      obtain ⟨col,hmem,hval⟩ := hASeenX
      refine ⟨col,hmem,?_⟩
      intro hEq
      apply hNoA
      exact ⟨col,hmem,hval,hEq.symm.trans hval⟩
    have hGreat : ∀ m : Nat, a < m →
        ¬ (trackFSeenSymbol cols 0 m ∧
           trackFSeenSymbol cols 1 m) := by
      intro m hLt hBoth
      have hMLeA := (hX m (by omega)).mp hBoth.1
      omega
    exact ⟨hDifferent,hSeenX1,hSeenJ1,Or.inr hSeenTopJ,
      ⟨a,haPos,hASeenX,hASeenJ,hGreat,hNoA⟩⟩

/-- Exact foldl-max bound: the maximum common positive letter is < a
iff 0<a and the contribution of EVERY chronological column is < a.
This treats repeated symbols, zero columns and empty histories. -/
private theorem trackFWordMax_fold_lt_iff
    {d ell : Nat} (U : IntegerGraphSupport d ell)
    (cols : List (Fin d → Nat)) (start a : Nat) :
    (cols.foldl
      (fun b col => max b (trackFColumnCommon col U)) start < a) ↔
      start < a ∧
      (∀ col ∈ cols, trackFColumnCommon col U < a) := by
  induction cols generalizing start with
  | nil =>
      simp
  | cons first tail ih =>
      simp only [List.foldl_cons]
      rw [ih]
      constructor
      · rintro ⟨hMax,hEach⟩
        have hStart : start < a := (max_lt_iff.mp hMax).1
        have hFirst : trackFColumnCommon first U < a :=
          (max_lt_iff.mp hMax).2
        refine ⟨hStart,?_⟩
        intro col hMem
        rcases List.mem_cons.mp hMem with hEq | hTail
        · subst col
          exact hFirst
        · exact hEach col hTail
      · rintro ⟨hStart,hEach⟩
        refine ⟨max_lt_iff.mpr ⟨hStart,hEach first (by simp)⟩,?_⟩
        intro col hMem
        exact hEach col (List.mem_cons_of_mem first hMem)

/-- The literal word maximum of all simultaneously common symbols
is <a precisely when every chronological column contributes <a. -/
theorem trackFWordMax_lt_iff
    {d ell : Nat} (cols : List (Fin d → Nat))
    (U : IntegerGraphSupport d ell) (a : Nat) :
    trackFWordMax d ell cols U < a ↔
      0 < a ∧
      (∀ col ∈ cols, trackFColumnCommon col U < a) := by
  exact trackFWordMax_fold_lt_iff U cols 0 a

/-- Under an initial-segment spectrum on x=0, the largest letter
simultaneously common to both words is <a exactly when the letter a
never appears on both at the SAME chronological coordinate. -/
theorem trackFWordMax_pair_lt_iff
    (ell a : Nat) (hell : 3 ≤ ell)
    (cols : List (Fin 2 → Nat))
    (hX : trackFBranchInitial cols (0 : Fin 2) a) :
    trackFWordMax 2 ell cols (trackFPairBoth ell hell) < a ↔
      0 < a ∧ ¬ trackFPairSimultaneous cols a := by
  rw [trackFWordMax_lt_iff]
  constructor
  · rintro ⟨ha,hEach⟩
    refine ⟨ha,?_⟩
    rintro ⟨col,hMem,h0,h1⟩
    have hCommon : trackFColumnCommon col
        (trackFPairBoth ell hell) = a := by
      apply (trackFColumnCommon_pos_iff col
        (trackFPairBoth ell hell) a ha).mpr
      intro i _
      fin_cases i
      · exact h0
      · exact h1
    have hLt := hEach col hMem
    omega
  · rintro ⟨ha,hNoA⟩
    refine ⟨ha,?_⟩
    intro col hMem
    let n := trackFColumnCommon col (trackFPairBoth ell hell)
    by_cases hn : 0 < n
    · have hEq0 : col 0 = n :=
        (trackFColumnCommon_pos_iff col
          (trackFPairBoth ell hell) n hn).mp rfl
            (0 : Fin 2) (by simp [trackFPairBoth])
      have hEq1 : col 1 = n :=
        (trackFColumnCommon_pos_iff col
          (trackFPairBoth ell hell) n hn).mp rfl
            (1 : Fin 2) (by simp [trackFPairBoth])
      have hSeenN : trackFSeenSymbol cols 0 n :=
        ⟨col,hMem,hEq0⟩
      have hnLeA : n ≤ a := (hX n hn).mp hSeenN
      have hnNeA : n ≠ a := by
        intro hEqual
        apply hNoA
        refine ⟨col,hMem,?_,?_⟩
        · simpa [hEqual] using hEq0
        · simpa [hEqual] using hEq1
      dsimp [n]
      omega
    · have hnZero : n = 0 := Nat.eq_zero_of_not_pos hn
      dsimp [n]
      omega

/-- If x=0 has positive initial spectrum {1,...,a}, every
simultaneously common positive symbol is at most a, even when
the other word is arbitrary. In particular the chronological
common-symbol maximum c satisfies c≤a. -/
theorem trackFWordMax_pair_le_height
    (ell a : Nat) (hell : 3 ≤ ell)
    (cols : List (Fin 2 → Nat))
    (hX : trackFBranchInitial cols (0 : Fin 2) a) :
    trackFWordMax 2 ell cols (trackFPairBoth ell hell) ≤ a := by
  have hColumn : ∀ col ∈ cols,
      trackFColumnCommon col (trackFPairBoth ell hell) ≤ a := by
    intro col hMem
    let n := trackFColumnCommon col (trackFPairBoth ell hell)
    by_cases hn : 0 < n
    · have hEq0 : col 0 = n :=
        (trackFColumnCommon_pos_iff col
          (trackFPairBoth ell hell) n hn).mp rfl
          (0 : Fin 2) (by simp [trackFPairBoth])
      have hSeen : trackFSeenSymbol cols 0 n :=
        ⟨col,hMem,hEq0⟩
      exact (hX n hn).mp hSeen
    · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      dsimp [n]
      omega
  have hMaxLT : trackFWordMax 2 ell cols
        (trackFPairBoth ell hell) < a + 1 :=
    (trackFWordMax_lt_iff cols
      (trackFPairBoth ell hell) (a + 1)).mpr
      ⟨by omega,by
        intro col hMem
        have h := hColumn col hMem
        omega⟩
  omega

/-- The full literal equal-length E predicate for the two selected
branches is exactly the strict inequality c<a between the largest
SIMULTANEOUS symbol c and the largest individually seen symbol a
on the noncoded branch x, given both required initial spectra. -/
theorem trackFConcreteEdgePair_iff_commonMax_lt
    (ell a : Nat) (hell : 3 ≤ ell)
    (ha : a ≤ ell - 2)
    (cols : List (Fin 2 → Nat))
    (hX : trackFBranchInitial cols (0 : Fin 2) a)
    (hJ : trackFBranchInitial cols (1 : Fin 2) (ell - 2)) :
    trackFConcreteEdgePair ell cols ↔
      trackFWordMax 2 ell cols (trackFPairBoth ell hell) < a := by
  exact (trackFConcreteEdgePair_iff_no_top ell a hell ha cols
    hX hJ).trans
    (trackFWordMax_pair_lt_iff ell a hell cols hX).symm

end Kk
