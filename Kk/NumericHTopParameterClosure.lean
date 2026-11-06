import Kk.NumericHTopAuxE
import Kk.B3GadgetClosureParameter
import SuccessorTree.V10.HFiniteAge
import Mathlib.Tactic

/-!
# Actual top-seed forcing of genuine generation-one Kpt parameters

The English proof and hostile 14-point audit were committed FIRST in
`docs/numeric_h_top_parameter_closure_english_audit.md`.

For a REAL finite numerical H+ top selected coordinate iota(j,k), any
earlier positive original i with 0<i<j has generation-one coordinate
c=iota(i,1) STRICTLY BELOW the top E free-level cutoff and with its
own ACTUAL numerical-H free level positive, provided 1<k.

The actual S3 Kpt parameter-closure theorem therefore forces the
genuine original Kpt node at c into the COMPLETE meet-and-parameter
closure WHEN c belongs to the chosen Algorithm 5.4 level set I and
the top selected Kpt original belongs to the actual seed set X.

The Henson specialization derives finite numerical-H avoidance from
the normalized base forbidden-family avoidance, rather than adding
an arbitrary finite-model hAvoid hypothesis.

This is NOT a proof that the canonical diary chooses c in I or
that an extra B3 microevent is harmless. A positive E incidence by
itself is never claimed sufficient for source membership. The
selected L+-column alone cannot determine full dependent B3 or
the common labelled inverse-source orbit.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Every positive ORIGINAL index 0<i<j at generation one has an
actual carrier address and POSITIVE E free level in the literal
finite H+ structure, assuming its later top selected address is
inside the carrier and 1<k. Generation-zero and i=0 are excluded. -/
theorem finiteNumericH_earlier_generation_one_positive_freeLevel
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N i j : Nat)
    (hk : 1 < k) (hi : 0 < i) (hij : i < j)
    (hTop : hPosition k j k < N) :
    hPosition k i 1 < N ∧
      0 < (finiteNumericH K k N).freeLevel
        (hPosition k i 1) := by
  have hOld : hPosition k i 1 < N :=
    (hPosition_lt_of_block_lt k i j 1 k (by omega) hij).trans hTop
  have hii : i - 1 + 1 = i := by omega
  have hOld' : hPosition k (i-1+1) 1 < N := by
    simpa only [hii] using hOld
  have hFree :=
    finiteNumericH_next_generation_one_freeLevel
      K k N (i-1) hk hOld'
  rw [hii] at hFree
  refine ⟨hOld, ?_⟩
  rw [hFree]
  omega

/-- The SAME earlier generation-one original is strictly BELOW the
real top selected Kpt node's full free-level cut. This uses the
actual top E-column, including its finite-carrier test, rather
than postulating a parameter incidence. -/
theorem finiteNumericH_generation_one_before_top_freeLevel
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N i j : Nat)
    (hk : 1 < k) (hi : 0 < i) (hij : i < j)
    (hTop : hPosition k j k < N) :
    hPosition k i 1 <
      (finiteNumericH K k N).freeLevel (hPosition k j k) := by
  have hTopPos : 0 < j := by omega
  have hH : 0 < k := by omega
  have hBit : exactHEBool k (hPosition k i 1)
      (hPosition k j k) = true :=
    numericH_top_auxE_all_earlier_real
      k i j 1 hH hTopPos hij (by omega)
  have hActual : (finiteNumericH K k N).E
      (hPosition k i 1) (hPosition k j k) = true := by
    change finiteNumericHE k N
      (hPosition k i 1) (hPosition k j k) = true
    exact (finiteNumericHE_true_iff k N _ _).2 ⟨hTop, hBit⟩
  exact ((finiteNumericH K k N).E_iff_freeLevel _ _).1 hActual

/-- Actual finite H+ Kpt-source forcing, *conditional* on precisely
the REAL Algorithm 5.4 selected-level and closure-seed data.

No closure membership is inferred from E-positive alone.
The result uses the genuine Kpt original, the actual numerical H
free levels and the existing kernel-checked S3 parameter theorem. -/
theorem finiteNumericH_top_seed_forces_genOne_parameter
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N i j : Nat)
    (hk : 1 < k) (hi : 0 < i) (hij : i < j)
    (hTop : hPosition k j k < N)
    (hFiniteAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (I : Set Nat)
    (X : Set (AdmissibleKptNode family))
    (hSeed :
      (finiteNumericH K k N).kptOriginal family hFiniteAvoid
        (⟨hPosition k j k, by
          change hPosition k j k < N
          exact hTop⟩ : Fin (finiteNumericH K k N).size) ∈ X)
    (hSelected : hPosition k i 1 ∈ I) :
    ∃ hiCarrier : hPosition k i 1 < (finiteNumericH K k N).size,
      (finiteNumericH K k N).kptOriginal family hFiniteAvoid
        (⟨hPosition k i 1, hiCarrier⟩ :
          Fin (finiteNumericH K k N).size) ∈
        SMTree.Envelope.closure
          (admissibleKptSTree family) I X := by
  have hPos :=
    (finiteNumericH_earlier_generation_one_positive_freeLevel
      K k N i j hk hi hij hTop).2
  have hBelow :=
    finiteNumericH_generation_one_before_top_freeLevel
      K k N i j hk hi hij hTop
  exact kpt_closure_contains_positive_parameter_of_seed
    family (finiteNumericH K k N) hFiniteAvoid I X
    (⟨hPosition k j k, by
      change hPosition k j k < N
      exact hTop⟩ : Fin (finiteNumericH K k N).size)
    hSeed (hPosition k i 1) hSelected hBelow hPos

/-- HENSON specialization: full finite numerical-H normalized-family
avoidance is obtained from the Henson original base's actual avoidance.
The only selected-source hypotheses left are the precise level c∈I
and the genuine seeded top Kpt original ∈X. -/
theorem henson_numericH_top_seed_forces_genOne_parameter
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (N i j : Nat) (hk : 1 < ell)
    (hi : 0 < i) (hij : i < j)
    (hTop : hPosition ell j ell < N)
    (I : Set Nat)
    (X : Set (AdmissibleKptNode
      (hensonForbiddenFamily ell hell)))
    (hSeed :
      (finiteNumericH (normalizedGraphModel E) ell N).kptOriginal
        (hensonForbiddenFamily ell hell)
        (finiteNumericH_avoids_family
          (hensonForbiddenFamily ell hell)
          (normalizedGraphModel E)
          (by intro x; trivial) ell N hAvoid)
        (⟨hPosition ell j ell, by
          change hPosition ell j ell < N
          exact hTop⟩ :
          Fin (finiteNumericH (normalizedGraphModel E) ell N).size) ∈ X)
    (hSelected : hPosition ell i 1 ∈ I) :
    ∃ hiCarrier :
        hPosition ell i 1 <
          (finiteNumericH (normalizedGraphModel E) ell N).size,
      (finiteNumericH (normalizedGraphModel E) ell N).kptOriginal
        (hensonForbiddenFamily ell hell)
        (finiteNumericH_avoids_family
          (hensonForbiddenFamily ell hell)
          (normalizedGraphModel E)
          (by intro x; trivial) ell N hAvoid)
        (⟨hPosition ell i 1, hiCarrier⟩ :
          Fin (finiteNumericH (normalizedGraphModel E) ell N).size) ∈
        SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily ell hell)) I X := by
  exact finiteNumericH_top_seed_forces_genOne_parameter
    (hensonForbiddenFamily ell hell)
    (normalizedGraphModel E)
    ell N i j hk hi hij hTop
    (finiteNumericH_avoids_family
      (hensonForbiddenFamily ell hell)
      (normalizedGraphModel E)
      (by intro x; trivial) ell N hAvoid)
    I X hSeed hSelected


/-- An ACTUAL AlgorithmRun selection of an earlier positive-generation
original c=iota(i,1) forces its complete Kpt parameter node into
the genuine closure at EVERY earlier scan cut p<c, provided the
later top Kpt original is a real seed.

The selected-level premise is now c ∈ R.I c of a genuine AlgorithmRun,
not an arbitrary externally postulated level-set I. The checked
R.I_eq_final_tail_of_run identity propagates its membership into
R.I (p+1), where the physical S3 parameter theorem applies.

This does NOT assert that every E-positive earlier original is
selected, or that the earlier cut p itself is interesting. In the
literal K4 gadget the latter needs an additional actual two-upper
corrected-B3 failure; that separate selection is already checked. -/
theorem finiteNumericH_run_selected_genOne_in_lower_closure
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N i j : Nat)
    (hk : 1 < k) (hi : 0 < i) (hij : i < j)
    (hTop : hPosition k j k < N)
    (hFiniteAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (X : Set (AdmissibleKptNode family))
    (hSeed :
      (finiteNumericH K k N).kptOriginal family hFiniteAvoid
        (⟨hPosition k j k, by
          change hPosition k j k < N
          exact hTop⟩ : Fin (finiteNumericH K k N).size) ∈ X)
    (runHeight : Nat) (hScan : hPosition k i 1 < runHeight)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X runHeight)
    (hSelected :
      hPosition k i 1 ∈ R.I (hPosition k i 1))
    (p : Nat) (hp : p < hPosition k i 1) :
    ∃ hiCarrier : hPosition k i 1 < (finiteNumericH K k N).size,
      (finiteNumericH K k N).kptOriginal family hFiniteAvoid
        (⟨hPosition k i 1, hiCarrier⟩ :
          Fin (finiteNumericH K k N).size) ∈
        SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (p+1)) X := by
  let c : Nat := hPosition k i 1
  have hFinal : c ∈ R.I 0 := by
    rw [R.I_eq_final_tail_of_run c (by simpa [c] using hScan)]
      at hSelected
    exact hSelected.1
  have hAtPrevious : c ∈ R.I (p+1) := by
    rw [R.I_eq_final_tail_of_run (p+1) (by omega)]
    exact ⟨hFinal, by omega⟩
  exact finiteNumericH_top_seed_forces_genOne_parameter
    family K k N i j hk hi hij hTop hFiniteAvoid
    (R.I (p+1)) X hSeed hAtPrevious

end Kk
