import Kk.TrackFMonotoneRawLocality
import Mathlib.Tactic

/-!
# Track F: genuine normalized singleton age equals monotone raw capacity

For an actual nonempty singleton support {i} in the finite integer
K_ell graph-age model, support-monotone raw B and the bounded concrete
capacity B({i}) ≤ ell-1 imply G_B({i})=B({i}).

A single normalized clique witness puts weight B({i}) at i and zero
elsewhere. Every full raw inequality is checked by monotonicity.
No geometric source or diary correspondence is assumed.
-/

namespace Kk

/-- A genuine singleton support, available for ell≥2. -/
def trackFSingletonSupport (d ell : Nat) (i : Fin d)
    (hell : 2 ≤ ell) : IntegerGraphSupport d ell := by
  refine ⟨{i}, ?_⟩
  constructor
  · simp
  · simp
    omega

/-- The actual normalized integer clique canonicalizer is exactly
the raw singleton bound under support monotonicity and the natural
ell−1 capacity cap. The RAW B need not be a genuine graph age. -/
theorem trackFCanonical_singleton_eq_raw
    (d ell : Nat) (hell : 2 ≤ ell)
    (B : IntegerGraphSupport d ell → Nat)
    (hMono : TrackFRawSupportMonotone d ell B)
    (i : Fin d)
    (hCap : B (trackFSingletonSupport d ell i hell) ≤ ell - 1) :
    integerGraphAgeCanonical d ell B
      (trackFSingletonSupport d ell i hell) =
    B (trackFSingletonSupport d ell i hell) := by
  classical
  let S : IntegerGraphSupport d ell :=
    trackFSingletonSupport d ell i hell
  let a : Nat := B S
  have hACap : a ≤ ell - 1 := by simpa [a,S] using hCap
  have hALt : a < ell := by omega
  let aFin : Fin ell := ⟨a,hALt⟩
  let zero : Fin ell := ⟨0,by omega⟩
  let v : Fin d → Fin ell :=
    fun j => if j = i then aFin else zero
  have hVal (j : Fin d) : (v j).val = if j = i then a else 0 := by
    by_cases hj : j = i
    · simp [v,hj,aFin]
    · simp [v,hj,zero]
  have hSum : Finset.univ.sum (fun j : Fin d => (v j).val) = a := by
    simp only [hVal, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  let w : IntegerCliqueWeights d ell := ⟨v,by
    rw [hSum]
    exact hCap⟩
  have hMass (U : IntegerGraphSupport d ell) :
      integerCliqueOnSupport w U =
        if i ∈ U.1 then a else 0 := by
    unfold integerCliqueOnSupport
    change U.1.sum (fun j => (v j).val) =
      if i ∈ U.1 then a else 0
    simp only [hVal, Finset.sum_ite_eq']
  have hFeasible :
      WitnessRespects
        (integerCliqueOnSupport (d := d) (ell := ell)) B w := by
    intro U
    rw [hMass]
    by_cases hiU : i ∈ U.1
    · rw [if_pos hiU]
      have hSU : S.1 ⊆ U.1 := by
        simpa [S,trackFSingletonSupport] using hiU
      exact hMono S U hSU
    · rw [if_neg hiU]
      exact Nat.zero_le _
  have hSval : integerCliqueOnSupport w S = a := by
    rw [hMass]
    simp [S,trackFSingletonSupport]
  apply Nat.le_antisymm
  · exact integerGraphAgeCanonical_le_raw d ell B S
  · change a ≤ integerGraphAgeCanonical d ell B S
    rw [← hSval]
    exact witnessValue_le_canonical
      (integerCliqueOnSupport (d := d) (ell := ell))
      B w hFeasible S

end Kk
