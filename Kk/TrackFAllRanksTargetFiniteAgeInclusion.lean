import Kk.TrackFAllRanksActualSourceRichness
import Kk.TrackFAllSupportTargetRawLower
import Mathlib.Tactic

/-!
# Track F: finite source-clique feasibility transfers to genuine target raw age

English-first proof and adversarial audit:
docs/track_f_source_target_finite_age_inclusion_english_audit.md

The source roots need only have individually rank-large ACTUAL coding-node
fibres of the respective genuine target types. The theorem turns this
assumption into the target feasibility of EVERY finite source-feasible B,
but does NOT prove synchronized target profiles exist.
-/

namespace Kk

/-- Transport ONE labelled abstract B-clique, using an ACTUAL chronological
source realization, to the true old-target raw support inequality.

The requested B vertices are labelled by σ on abstract indices; the
physical target theorem requires labels on ACTUAL source originals.
We construct that map on the finite image of the source embedding,
using its injectivity, and assign a dummy label everywhere else.
No monotonicity of the source-to-target embedding e is assumed. -/
theorem trackFLabelledSourceClique_target_raw_bound
    (d ell H N : Nat) (hell : 2 ≤ ell)
    (Esrc Etgt B : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel Etgt))
    (e : Nat → Nat) (he : Function.Injective e)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (v : Fin d → HensonOneType ell Etgt)
    (hVLevel : ∀ i, (v i).level = H)
    (f : Nat → Nat) (σ : Nat → Fin d)
    (hfInj : Set.InjOn f (↑(Finset.range N) : Set Nat))
    (hfEdges : ∀ i : Nat, i < N → ∀ j : Nat, j < N →
      i ≠ j → Esrc (f i) (f j) = B i j)
    (hfCoding : ∀ i : Nat, i < N →
      ∃ t : HensonOneType ell Esrc,
        t.level = f i ∧
        t ∈ HensonOneType.sourceCodingFibre
          (E := Esrc) Etgt e (v (σ i)))
    (C : Finset Nat) (hCSub : C ⊆ Finset.range N)
    (hClique : IsDirectedCliqueOn B C) :
    C.card ≤ trackFCommonRawAge d ell H Etgt
      (fun i => (v i).neighbours) (C.image σ) := by
  classical
  let W : Finset Nat := C.image f
  let label : Nat → Fin d :=
    fun w =>
      if h : ∃ i : Nat, i ∈ C ∧ f i = w then
        σ (Classical.choose h)
      else σ 0
  have hLabel (i : Nat) (hi : i ∈ C) :
      label (f i) = σ i := by
    dsimp [label]
    split_ifs with h
    · have hSpec := Classical.choose_spec h
      have hEq : Classical.choose h = i :=
        hfInj (hCSub hSpec.1) (hCSub hi) hSpec.2
      simpa only [hEq]
    · exact False.elim (h ⟨i, hi, rfl⟩)
  have hSort : ∀ w ∈ W, label w ∈ C.image σ := by
    intro w hw
    obtain ⟨i, hi, hiw⟩ := Finset.mem_image.mp hw
    have hσ : σ i ∈ C.image σ :=
      Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have hLi := hLabel i hi
    rw [hiw] at hLi
    rw [hLi]
    exact hσ
  have hSourceClique : IsDirectedCliqueOn Esrc W := by
    intro w hw z hz hwz
    obtain ⟨i, hi, hiw⟩ := Finset.mem_image.mp hw
    obtain ⟨j, hj, hjz⟩ := Finset.mem_image.mp hz
    have hij : i ≠ j := by
      intro heq
      subst j
      exact hwz (hiw.symm.trans hjz)
    have hiN : i < N := Finset.mem_range.mp (hCSub hi)
    have hjN : j < N := Finset.mem_range.mp (hCSub hj)
    have hE : Esrc (f i) (f j) = true := by
      calc
        Esrc (f i) (f j) = B i j := hfEdges i hiN j hjN hij
        _ = true := hClique i hi j hj hij
    simpa only [hiw, hjz] using hE
  have hCodingW : ∀ w ∈ W,
      ∃ t : HensonOneType ell Esrc,
        t.level = w ∧
        t ∈ HensonOneType.sourceCodingFibre
          (E := Esrc) Etgt e (v (label w)) := by
    intro w hw
    obtain ⟨i, hi, hiw⟩ := Finset.mem_image.mp hw
    have hiN : i < N := Finset.mem_range.mp (hCSub hi)
    obtain ⟨t, ht, htFibre⟩ := hfCoding i hiN
    have hLi := hLabel i hi
    have hFibreLabel :
        t ∈ HensonOneType.sourceCodingFibre
          (E := Esrc) Etgt e (v (label (f i))) := by
      simpa only [hLi] using htFibre
    refine ⟨t, ?_, ?_⟩
    · simpa only [hiw] using ht
    · simpa only [hiw] using hFibreLabel
  have hfInjC : Set.InjOn f (↑C : Set Nat) := by
    intro i hi j hj hEq
    exact hfInj (hCSub hi) (hCSub hj) hEq
  have hCard : W.card = C.card :=
    Finset.card_image_iff.mpr hfInjC
  have hLower :=
    trackFCommonRawAge_target_ge_sorted_source_clique
      d ell H hell Esrc Etgt hAvoid e he hInduced
      v hVLevel (C.image σ) W label
      hSort hSourceClique hCodingW
  change C.card ≤ trackFCommonRawAge d ell H Etgt
    (fun i => (v i).neighbours) (C.image σ)
  rw [← hCard]
  exact hLower

/-- Every finite graph B satisfying ALL genuine source raw clique
constraints satisfies ALL corresponding ACTUAL target raw constraints,
provided that each target-prefix coding fibre is rank-large above
the chosen genuine source root.

The full original-source realization comes from the verified all-ranks
source richness theorem (#367), and physical target feasibility from
the verified target clique lower-bound (#335).

This is a TARGET finite-class inclusion conditional on the simultaneous
individual large fibres, NOT a claim that compatible target prefixes
with the desired full profile can already be constructed. -/
theorem trackFAllRanks_source_feasible_implies_target_feasible
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
    (hLarge : ∀ i,
      RankLargeness.Large HensonOneType.rank
        (HensonOneType.sourceCodingFibre (E := Esrc)
          Etgt e (v i))
        (HensonOneType.rank (u i)) (u i))
    (hSymB : ∀ i j, B i j = B j i)
    (hGlobal : ∀ C : Finset Nat,
      C ⊆ Finset.range N → C.Nonempty →
      IsDirectedCliqueOn B C →
      C.card ≤ trackFCommonRawAge d ell m Esrc
        (fun i => (u i).neighbours) (C.image σ)) :
    ∀ C : Finset Nat,
      C ⊆ Finset.range N → C.Nonempty →
      IsDirectedCliqueOn B C →
      C.card ≤ trackFCommonRawAge d ell H Etgt
        (fun i => (v i).neighbours) (C.image σ) := by
  classical
  obtain ⟨f, hChron, _hAfter, hCoding, _hColumn, hEdges⟩ :=
    trackFAllRanks_realizes_all_feasible_sorted_source_graph
      d ell m N Esrc B u σ
      (fun i => HensonOneType.sourceCodingFibre
        (E := Esrc) Etgt e (v i))
      hULevel hLarge
      (fun i x hx => hx.1) hSymB hGlobal
  have hfInj : Set.InjOn f (↑(Finset.range N) : Set Nat) := by
    intro i hi j hj hEq
    by_cases hij : i = j
    · exact hij
    · rcases lt_or_gt_of_ne hij with hijLt | hjiLt
      · exact False.elim
          ((ne_of_lt (hChron i j hijLt
            (Finset.mem_range.mp hj))) hEq)
      · exact False.elim
          ((ne_of_lt (hChron j i hjiLt
            (Finset.mem_range.mp hi))) hEq.symm)
  intro C hC _hNonempty hClique
  exact trackFLabelledSourceClique_target_raw_bound
    d ell H N hell Esrc Etgt B hAvoid e he hInduced
    v hVLevel f σ hfInj hEdges hCoding C hC hClique

end Kk
