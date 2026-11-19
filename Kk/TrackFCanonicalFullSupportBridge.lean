import Kk.TrackFAllRanksSourceTargetFiniteAgeIff
import Kk.FiniteCliqueIntegerWitness
import Mathlib.Tactic

/-!
# Track F: exact-support clique tests and complete canonical integer-age tests

English proof and adversarial scope audit were committed FIRST in
docs/track_f_canonical_full_support_bridge_english_audit_20261119.md.

The verified Track F source/target finite-class equivalence (#383) checks
a clique's exact sort image. Integer-witness canonicalization instead checks
ALL admissible supports on every clique, including unused sorts.

The bridge uses genuine raw support monotonicity and, for the converse,
the complete finite K_ell-free hypothesis on the *abstract graph B*.
No compatible target fibres are constructed, and no diary/BRD is claimed.
-/

namespace Kk

/-- Genuine physical raw age is monotone INCREASING as the sort support
grows: bigger supports have smaller common old-neighbour pools, hence
no larger old clique capacity. This is true for empty supports too,
though target/source transport elsewhere uses only nonempty ones. -/
theorem trackFCommonRawAge_mono_support
    (d ell front : Nat)
    (E : Nat → Nat → Bool)
    (U : Fin d → Finset Nat)
    (S T : Finset (Fin d))
    (hST : S ⊆ T) :
    trackFCommonRawAge d ell front E U S ≤
      trackFCommonRawAge d ell front E U T := by
  classical
  have hPools :
      trackFCommonNeighbourPool d front U T ⊆
        trackFCommonNeighbourPool d front U S := by
    intro x hx
    have hxT : x ∈ Finset.range front ∧
        ∀ i ∈ T, x ∈ U i := by
      simpa only [trackFCommonNeighbourPool,
        Finset.mem_filter] using hx
    change x ∈ (Finset.range front).filter
      (fun y => ∀ i ∈ S, y ∈ U i)
    refine Finset.mem_filter.mpr ⟨hxT.1, ?_⟩
    intro i hi
    exact hxT.2 i (hST hi)
  have hCap :=
    finiteDirectedCliqueCapacity_mono E
      (trackFCommonNeighbourPool d front U T)
      (trackFCommonNeighbourPool d front U S) hPools
  unfold trackFCommonRawAge
  omega

/-- For any fixed FINITE abstract B that is K_ell-free, requiring
all raw inequalities on each clique's EXACT sort-image is equivalent
to the manuscript's complete system of raw inequalities on EVERY
admissible nonempty support, counting only the clique vertices of
those sorts.

The exact→full direction uses a filtered clique and raw monotonicity.
The full→exact direction uses the true finite K_ell-free checker to
ensure C.image σ has size at most ell-1, as required for an
IntegerGraphSupport. Repeated labels are allowed. -/
theorem trackFExactClique_iff_fullRawIntegerSupport
    (d ell front N : Nat)
    (E B : Nat → Nat → Bool)
    (U : Fin d → Finset Nat)
    (σ : Nat → Fin d)
    (hBFree : finitePoolCliqueCheck B ell (Finset.range N) = false) :
    (∀ C : Finset Nat,
      C ⊆ Finset.range N → C.Nonempty →
      IsDirectedCliqueOn B C →
      C.card ≤ trackFCommonRawAge d ell front E U (C.image σ)) ↔
    (∀ C : Finset Nat,
      C ⊆ Finset.range N →
      IsDirectedCliqueOn B C →
      ∀ T : IntegerGraphSupport d ell,
        (C.filter (fun x => σ x ∈ T.1)).card ≤
          trackFCommonRawAge d ell front E U T.1) := by
  classical
  constructor
  · intro hExact C hCSub hClique T
    let D : Finset Nat := C.filter (fun x => σ x ∈ T.1)
    have hDSubC : D ⊆ C := Finset.filter_subset _ _
    have hDSubN : D ⊆ Finset.range N := hDSubC.trans hCSub
    have hDClique : IsDirectedCliqueOn B D := by
      intro x hx y hy hxy
      exact hClique x (hDSubC hx) y (hDSubC hy) hxy
    by_cases hDNonempty : D.Nonempty
    · have hSortSub : D.image σ ⊆ T.1 := by
        intro i hi
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
        exact (Finset.mem_filter.mp hx).2
      calc
        D.card ≤ trackFCommonRawAge d ell front E U (D.image σ) :=
          hExact D hDSubN hDNonempty hDClique
        _ ≤ trackFCommonRawAge d ell front E U T.1 :=
          trackFCommonRawAge_mono_support
            d ell front E U (D.image σ) T.1 hSortSub
    · have hDZero : D = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hDNonempty
      simp only [hDZero, Finset.card_empty]
      exact Nat.zero_le _
  · intro hFull C hCSub hCNonempty hClique
    have hSmall : C.card < ell :=
      finiteClique_card_lt_of_pool_cliqueFree
        B ell (Finset.range N) C hBFree hCSub hClique
    have hImageCard : (C.image σ).card ≤ C.card :=
      Finset.card_image_le
    have hBoundCard : (C.image σ).card ≤ ell - 1 := by
      omega
    have hImageNonempty : (C.image σ).Nonempty := by
      obtain ⟨x, hx⟩ := hCNonempty
      exact ⟨σ x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
    let T : IntegerGraphSupport d ell :=
      ⟨C.image σ, hImageNonempty, hBoundCard⟩
    have hFilter : C.filter (fun x => σ x ∈ T.1) = C := by
      apply Finset.filter_eq_self.mpr
      intro x hx
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have hBound := hFull C hCSub hClique T
    rw [hFilter] at hBound
    exact hBound

/-- Conditional equality of the COMPLETE normalized integer-witness
graph-age acceptance test for any finite symmetric K_ell-free B, at
actual source and target Henson type families.

This composes:
  * the exact-support ↔ full-RAW-support bridge above;
  * merged actual source/target exact-support feasibility iff (#383);
  * the verified generic all-support integer canonicalization theorem.

The source/target coding fibres and old-neighbour image cutoff are
EXPLICIT assumptions. This is an equivalence of complete tests,
NOT pointwise equality of raw or canonical numerical bounds,
NOT a construction of compatible multi-sort target fronts,
and NOT diary unavoidability or an exact BRD theorem. -/
theorem trackFAllRanks_source_target_canonical_full_support_iff
    (d ell m H N : Nat) (hell : 2 ≤ ell)
    (Esrc Etgt B : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (u : Fin d → HensonOneType ell Esrc)
    (v : Fin d → HensonOneType ell Etgt)
    (σ : Nat → Fin d)
    (hULevel : ∀ i, (u i).level = m)
    (hVLevel : ∀ i, (v i).level = H)
    (hImageBelow : ∀ i c, c ∈ (u i).neighbours → e c < H)
    (hLarge : ∀ i,
      RankLargeness.Large HensonOneType.rank
        (HensonOneType.sourceCodingFibre (E := Esrc)
          Etgt e (v i))
        (HensonOneType.rank (u i)) (u i))
    (hSymB : ∀ i j, B i j = B j i)
    (hBFree : finitePoolCliqueCheck B ell (Finset.range N) = false) :
    (∀ C : Finset Nat,
      C ⊆ Finset.range N →
      IsDirectedCliqueOn B C →
      ∀ T : IntegerGraphSupport d ell,
        (C.filter (fun x => σ x ∈ T.1)).card ≤
          integerGraphAgeCanonical d ell
            (fun Q : IntegerGraphSupport d ell =>
              trackFCommonRawAge d ell m Esrc
                (fun i => (u i).neighbours) Q.1) T) ↔
    (∀ C : Finset Nat,
      C ⊆ Finset.range N →
      IsDirectedCliqueOn B C →
      ∀ T : IntegerGraphSupport d ell,
        (C.filter (fun x => σ x ∈ T.1)).card ≤
          integerGraphAgeCanonical d ell
            (fun Q : IntegerGraphSupport d ell =>
              trackFCommonRawAge d ell H Etgt
                (fun i => (v i).neighbours) Q.1) T) := by
  classical
  have hCanonSource :=
    finiteClique_all_constraints_integerCanonical_iff
      B (Finset.range N) σ
      (fun Q : IntegerGraphSupport d ell =>
        trackFCommonRawAge d ell m Esrc
          (fun i => (u i).neighbours) Q.1) hBFree
  have hCanonTarget :=
    finiteClique_all_constraints_integerCanonical_iff
      B (Finset.range N) σ
      (fun Q : IntegerGraphSupport d ell =>
        trackFCommonRawAge d ell H Etgt
          (fun i => (v i).neighbours) Q.1) hBFree
  have hExactSource :=
    trackFExactClique_iff_fullRawIntegerSupport
      d ell m N Esrc B (fun i => (u i).neighbours) σ hBFree
  have hExactTarget :=
    trackFExactClique_iff_fullRawIntegerSupport
      d ell H N Etgt B (fun i => (v i).neighbours) σ hBFree
  have hExactIff :=
    trackFAllRanks_source_target_clique_feasibility_iff
      d ell m H N hell Esrc Etgt B hAvoid e he hInduced
      u v σ hULevel hVLevel hImageBelow hLarge hSymB
  exact hCanonSource.trans
    (hExactSource.symm.trans
      (hExactIff.trans
        (hExactTarget.trans hCanonTarget.symm)))

end Kk
