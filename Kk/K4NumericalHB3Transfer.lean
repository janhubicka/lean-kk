import Kk.K4NumericalHAtoms
import SuccessorTree.V10.I3AmbientSocleBridge
import Mathlib.Tactic

/-!
# Transport the full cut-22 K4 B3 obstruction to the actual numerical H

The literal H-atom lemmas identify the 23-old-vertex L socle and
complete upper L type of original 38 with the explicit finite
two-future-vertex continuation proved in K4Cut22Continuation.

Here we include every diagonal and unary atom, so no unsupported
identification of directed or auxiliary E records is used. The B3
age-test witnesses are L-only; E is needed only to extract the
actual Kpt type.

The final theorem establishes failure of the exact one-upper
CommonSocleAgeTest associated with type_H^{23}(38) at cut 22.
The next application can use the already merged
bad_single_upper_forces_actual_interesting theorem to show the
tested level belongs to the actual AlgorithmRun selected set,
provided original 38 is an initial closure seed.

No claim about common labelled diary sources is made.
-/

namespace Kk

open SuccessorTree.V10

/-- Every diagonal bit of the actual finite numerical H is false
because every base singleton is loopless. This covers fake vertices
as well as real original copies. -/
theorem k4H_all_diagonals_false (x : Nat) :
    (finiteNumericHL (normalizedGraphModel k4FourOriginalEdge)
      4 40).diagonal x (0 : Fin 1) = false := by
  classical
  change hNumericSingleton (normalizedGraphModel k4FourOriginalEdge).diagonal
      4 x (0 : Fin 1) = false
  unfold hNumericSingleton
  split_ifs with h
  · change k4FourOriginalEdge (Classical.choose h)
        (Classical.choose h) = false
    exact k4FourOriginalEdge_irreflexive _
  · rfl

/-- There is no positive binary loop at any numerical H original:
an allowed copied pair always comes from distinct original blocks
in increasing numerical order. -/
theorem k4H_top_binary_loop_false :
    (finiteNumericHL (normalizedGraphModel k4FourOriginalEdge)
      4 40).binary 38 38 (0 : Fin 1) = false := by
  change hNumericBinary (normalizedGraphModel k4FourOriginalEdge).binary
      4 38 38 (0 : Fin 1) = false
  by_cases ht : hNumericBinary
      (normalizedGraphModel k4FourOriginalEdge).binary
      4 38 38 (0 : Fin 1) = true
  · obtain ⟨i,j,q,m,hij,hq,_hm,_hgate,hdir⟩ :=
      (hNumericBinary_true_iff
        (normalizedGraphModel k4FourOriginalEdge).binary
        4 38 38 (0 : Fin 1)).1 ht
    have hStrict := hPosition_lt_of_block_lt 4 i j q m hq hij
    rcases hdir with ⟨h1,h2,_⟩ | ⟨h1,h2,_⟩ <;> omega
  · cases hb : hNumericBinary
        (normalizedGraphModel k4FourOriginalEdge).binary
        4 38 38 (0 : Fin 1) with
    | false => rfl
    | true => exact False.elim (ht hb)

/-- The whole initial L-reduct of the explicit finite B3
continuation matches the literal numerical H L model through
coordinate 22, including all negative directed atoms and
diagonal bits. -/
theorem k4H_full_old_L_socle :
    SameInitialL k4Cut22Continuation
      (finiteNumericHL (normalizedGraphModel k4FourOriginalEdge)
        4 40) 22 := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x hx
    change (x < 25 ↔ x < 40)
    omega
  · intro x y hx hy t
    fin_cases t
    calc
      k4Cut22Continuation.binary x y (0 : Fin 1) =
          decide ((x = 10 ∧ y = 22) ∨
            (x = 22 ∧ y = 10)) := by
        simp [k4Cut22Continuation, hx, hy]
      _ = (finiteNumericHL
          (normalizedGraphModel k4FourOriginalEdge) 4 40).binary
            x y (0 : Fin 1) :=
        (k4H_old_binary_eq x y hx hy).symm
  · intro x hx t
    exact Fin.elim0 t
  · intro x hx t
    fin_cases t
    change false = (finiteNumericHL
      (normalizedGraphModel k4FourOriginalEdge) 4 40).diagonal
      x (0 : Fin 1)
    exact (k4H_all_diagonals_false x).symm

/-- Full equality of the future L-type of the finite continuation
with the Kpt original's genuine L-type through cut 22+1.
Includes all old--old, old--type, type--old, type--type atoms. -/
theorem k4H_full_upper_L_type :
    k4Cut22Upper =
      RelationalPrefixType.ofAgeModel
        (finiteNumericHL (normalizedGraphModel k4FourOriginalEdge)
          4 40) 23 38 := by
  apply RelationalPrefixType.eq_of_atoms
  · intro a b t
    fin_cases t
    cases a with
    | none =>
      cases b with
      | none =>
        change k4Cut22Continuation.binary 23 23 (0 : Fin 1) =
          (finiteNumericHL (normalizedGraphModel k4FourOriginalEdge)
            4 40).binary 38 38 (0 : Fin 1)
        simpa [k4Cut22Continuation] using
          k4H_top_binary_loop_false.symm
      | some j =>
        have hj : j.val ≤ 22 := by omega
        change k4Cut22Continuation.binary 23 j.val (0 : Fin 1) =
          (finiteNumericHL (normalizedGraphModel k4FourOriginalEdge)
            4 40).binary 38 j.val (0 : Fin 1)
        calc
          k4Cut22Continuation.binary 23 j.val (0 : Fin 1) =
              decide (j.val % 2 = 0) := by
            simp [k4Cut22Continuation,hj]
          _ = (finiteNumericHL
              (normalizedGraphModel k4FourOriginalEdge)
              4 40).binary 38 j.val (0 : Fin 1) :=
            (k4H_upper_edge_reverse_eq j.val hj).symm
    | some i =>
      cases b with
      | none =>
        have hi : i.val ≤ 22 := by omega
        change k4Cut22Continuation.binary i.val 23 (0 : Fin 1) =
          (finiteNumericHL (normalizedGraphModel k4FourOriginalEdge)
            4 40).binary i.val 38 (0 : Fin 1)
        calc
          k4Cut22Continuation.binary i.val 23 (0 : Fin 1) =
              decide (i.val % 2 = 0) := by
            simp [k4Cut22Continuation,hi]
          _ = (finiteNumericHL
              (normalizedGraphModel k4FourOriginalEdge)
              4 40).binary i.val 38 (0 : Fin 1) :=
            (k4H_upper_edge_eq i.val hi).symm
      | some j =>
        have hi : i.val ≤ 22 := by omega
        have hj : j.val ≤ 22 := by omega
        change k4Cut22Continuation.binary i.val j.val (0 : Fin 1) =
          (finiteNumericHL (normalizedGraphModel k4FourOriginalEdge)
            4 40).binary i.val j.val (0 : Fin 1)
        exact (k4H_full_old_L_socle.2.1
          i.val j.val hi hj (0 : Fin 1))
  · intro a t
    exact Fin.elim0 t
  · intro a t
    fin_cases t
    cases a with
    | none =>
      change k4Cut22Continuation.diagonal 23 (0 : Fin 1) =
        (finiteNumericHL (normalizedGraphModel k4FourOriginalEdge)
          4 40).diagonal 38 (0 : Fin 1)
      exact (k4H_all_diagonals_false 38).symm
    | some i =>
      change k4Cut22Continuation.diagonal i.val (0 : Fin 1) =
        (finiteNumericHL (normalizedGraphModel k4FourOriginalEdge)
          4 40).diagonal i.val (0 : Fin 1)
      exact (k4H_all_diagonals_false i.val).symm

/-- Initial-socle equality is symmetric, including all directed
binary values, unary values and singleton diagonal values. -/
private theorem sameInitialL_reverse
    {db du dd : Nat} {A B : AgeTestModel db du dd} {cut : Nat}
    (h : SameInitialL A B cut) : SameInitialL B A cut := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x hx
    exact (h.1 x hx).symm
  · intro x y hx hy t
    exact (h.2.1 x y hx hy t).symm
  · intro x hx t
    exact (h.2.2.1 x hx t).symm
  · intro x hx t
    exact (h.2.2.2 x hx t).symm

/-- The corrected-B3 lower socle supplied by the actual complete
Kpt type at 38 equals the explicit finite continuation's
23-element lower L-socle. -/
theorem k4H_cut22_prescribed_socle :
    SameInitialL k4Cut22Continuation
      (prescribedOrdinarySocle
        ((finiteNumericH (normalizedGraphModel k4FourOriginalEdge)
          4 40).partialTypeAt 23 38)) 22 := by
  let A := finiteNumericH (normalizedGraphModel k4FourOriginalEdge) 4 40
  have hToAmbient : SameInitialL k4Cut22Continuation A.L 22 :=
    k4H_full_old_L_socle
  have hFromType :
      SameInitialL
        (prescribedOrdinarySocle (A.partialTypeAt 23 38))
        A.L 22 :=
    ambient_partialType_prescribedSocle A 22 38 (by decide)
  exact hToAmbient.trans (sameInitialL_reverse hFromType)

/-- The FINITE 25-vertex continuation is a genuine failed
corrected-B3 age test of one ACTUAL selected original 38 at
numerical H cut 22. The test remains entirely L-only,
as mandated by Lemma 6.51. -/
theorem k4H_actual_cut22_singleUpper_B3_failure :
    ¬ CommonSocleAgeTest
      (hensonForbiddenFamily 4 (by decide))
      (prescribedOrdinarySocle
        ((finiteNumericH (normalizedGraphModel k4FourOriginalEdge)
          4 40).partialTypeAt 23 38)) 22
      (fun R =>
        R = ((finiteNumericH (normalizedGraphModel k4FourOriginalEdge)
          4 40).partialTypeAt 23 38).lReduct) := by
  intro hB3
  have hUpperActual :
      UpperTypesPrescribed k4Cut22Continuation 22
        (fun R => R =
          ((finiteNumericH (normalizedGraphModel k4FourOriginalEdge)
            4 40).partialTypeAt 23 38).lReduct) := by
    intro x hx hAbove
    have hxType := k4Cut22_upper_types x hx hAbove
    change RelationalPrefixType.ofAgeModel
      k4Cut22Continuation 23 x = k4Cut22Upper at hxType
    change RelationalPrefixType.ofAgeModel
      k4Cut22Continuation 23 x =
        RelationalPrefixType.ofAgeModel
          (finiteNumericHL (normalizedGraphModel k4FourOriginalEdge)
            4 40) 23 38
    exact hxType.trans k4H_full_upper_L_type
  have hK4mem :
      (NormalizedForbidden.nontrivial 4
        (cliquePattern 4) (by decide) (cliquePattern_irreducible 4)) ∈
        hensonForbiddenFamily 4 (by decide) := by
    simp [hensonForbiddenFamily]
  have hAvoid := hB3
    k4Cut22Continuation k4Cut22_finite
    k4H_cut22_prescribed_socle hUpperActual
    k4Cut22_deleted_avoids
    (NormalizedForbidden.nontrivial 4
      (cliquePattern 4) (by decide) (cliquePattern_irreducible 4))
    hK4mem
  exact hAvoid k4Cut22_realizesK4

end Kk
