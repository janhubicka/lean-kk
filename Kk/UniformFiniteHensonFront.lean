import Kk.PinnedPrefixHensonExtension
import Kk.UniversalFutureExactProfile
import Kk.FiniteCliqueIntegerWitness
import Mathlib.Tactic

/-!
# KK Track A: one anchored Henson embedding carries ALL feasible clique profiles

English proof and adversarial audit committed first:
  docs/track_a_uniform_finite_henson_front_english_audit.md

The input is ONE compatible finite universal labelled target A on the
entire old fixed prefix, not an unrelated family of patterns.
The verified pinned-prefix theorem embeds that A **once** in the
unchanged left-dense Henson original graph, identity on [0,b),
preserving all directed L bits and zeros to every skipped earlier
original. We transport every feasible normalized clique vector at
once through that SAME induced embedding and prove absence of
spurious clique vectors in its actual finite future image.

The existence of the compatible finite universal target A is an
INDEPENDENT construction obligation. Neither a standalone universal
W_B nor independent per-vector realizations over fixed old E are
silently promoted to a common physical W.
-/

namespace Kk

/-- A physical labelled support predicate on the image of one finite
future W, defined using the UNIQUE original preimage under f.
The existential form avoids constructing an unsupported total sort
function on Nat when d=0. -/
def pulledBackFiniteSortIn
    {d ell : Nat} (W : Finset Nat)
    (sort : Nat → Fin d) (f : Nat → Nat)
    (T : IntegerGraphSupport d ell) (z : Nat) : Prop :=
  z ∈ (W.filter (fun x => sort x ∈ T.1)).image f

/-- Exact support multiplicities commute with an injective finite
image using the actual pulled-back sort predicate on the image.
Every support T is handled simultaneously by the same injection f. -/
theorem pulledBackFiniteSort_count_image_eq
    {d ell : Nat} (W s : Finset Nat)
    (sort : Nat → Fin d) (f : Nat → Nat)
    (hSW : s ⊆ W)
    (hInj : Set.InjOn f ↑W)
    (T : IntegerGraphSupport d ell) :
    ((s.image f).filter (pulledBackFiniteSortIn W sort f T)).card =
      (s.filter (fun x => sort x ∈ T.1)).card := by
  classical
  have hFilterImage :
      (s.image f).filter (pulledBackFiniteSortIn W sort f T) =
        (s.filter (fun x => sort x ∈ T.1)).image f := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzImg,hzType⟩ := Finset.mem_filter.mp hz
      obtain ⟨x,hx,hxz⟩ := Finset.mem_image.mp hzImg
      obtain ⟨y,hy,hzy⟩ := Finset.mem_image.mp hzType
      obtain ⟨hyW,hyt⟩ := Finset.mem_filter.mp hy
      have hxy : x = y :=
        hInj (hSW hx) hyW (hxz.trans hzy.symm)
      apply Finset.mem_image.mpr
      refine ⟨x,Finset.mem_filter.mpr ⟨hx,?_⟩,hxz⟩
      simpa only [hxy] using hyt
    · intro hz
      obtain ⟨x,hx,hxz⟩ := Finset.mem_image.mp hz
      obtain ⟨hxs,hxt⟩ := Finset.mem_filter.mp hx
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨x,hxs,hxz⟩,?_⟩
      exact Finset.mem_image.mpr
        ⟨x,Finset.mem_filter.mpr ⟨hSW hxs,hxt⟩,hxz⟩
  rw [hFilterImage]
  have hInjFiltered :
      Set.InjOn f ↑(s.filter (fun x => sort x ∈ T.1)) := by
    intro x hx y hy hxy
    apply hInj
    · exact hSW (Finset.mem_filter.mp hx).1
    · exact hSW (Finset.mem_filter.mp hy).1
    · exact hxy
  exact Finset.card_image_iff.mpr hInjFiltered

/-- Clique truth transports BOTH ways under an exact induced map
on one finite ambient future W. No ambient symmetry and no
one-sided positive-edge shortcut are used. -/
theorem finiteClique_iff_injective_image
    (A E : Nat → Nat → Bool)
    (W s : Finset Nat) (f : Nat → Nat)
    (hSW : s ⊆ W)
    (hInj : Set.InjOn f ↑W)
    (hAgree : ∀ x ∈ W, ∀ y ∈ W, x ≠ y →
      A x y = E (f x) (f y)) :
    IsDirectedCliqueOn A s ↔
      IsDirectedCliqueOn E (s.image f) := by
  constructor
  · intro hc u hu v hv huv
    obtain ⟨x,hx,hxu⟩ := Finset.mem_image.mp hu
    obtain ⟨y,hy,hyv⟩ := Finset.mem_image.mp hv
    have hxy : x ≠ y := by
      intro h
      subst y
      exact huv (hxu.symm.trans hyv)
    have hEdge := hc x hx y hy hxy
    have hTransport := hAgree x (hSW hx) y (hSW hy) hxy
    have hImageEdge : E (f x) (f y) = true :=
      hTransport.symm.trans hEdge
    simpa only [hxu,hyv] using hImageEdge
  · intro hc x hx y hy hxy
    have hfne : f x ≠ f y := by
      intro h
      exact hxy (hInj (hSW hx) (hSW hy) h)
    have hImgEdge : E (f x) (f y) = true :=
      hc (f x) (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
        (f y) (Finset.mem_image.mpr ⟨y,hy,rfl⟩) hfne
    exact (hAgree x (hSW hx) y (hSW hy) hxy).trans hImgEdge

/-- For a subset t of an injective image f(W), the finite pullback
W ∩ f^{-1}(t) has image EXACTLY t. This makes the later
'no spurious feasible profiles' direction constructive on sets. -/
theorem finiteImage_pullback_image_eq
    (W t : Finset Nat) (f : Nat → Nat)
    (ht : t ⊆ W.image f) :
    (W.filter (fun x => f x ∈ t)).image f = t := by
  classical
  apply Finset.Subset.antisymm
  · intro z hz
    obtain ⟨x,hx,hxz⟩ := Finset.mem_image.mp hz
    exact hxz ▸ (Finset.mem_filter.mp hx).2
  · intro z hz
    obtain ⟨x,hx,hxz⟩ := Finset.mem_image.mp (ht hz)
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_filter.mpr ⟨hx,?_⟩, hxz⟩
    exact hxz ▸ hz

/-- ONE fixed genuine Henson finite extension simultaneously contains
cliques of EVERY feasible normalized labelled multiplicity vector,
and no clique of its physical future image has a spurious vector.

The finite target A itself must have been constructed **over the
entire fixed old prefix** [0,b), be K_ell-free there together with
all its future vertices, and realize ALL feasible vectors on the
SAME finite target W. These are real explicit compatibility
hypotheses: the standalone abstract W_B does not supply them.

One resulting f is identity on every old original, order-preserving,
exact on ALL directed binary atoms, and has negative old-gap
columns for every appended original. The physical sort predicate is
pulled back along f and is meaningful without inventing a global
colouring of every Henson original.
-/
theorem henson_leftDense_uniform_finite_profiles_over_fixed_prefix
    (ell b N d : Nat) (hell : 2 ≤ ell) (hbN : b ≤ N)
    (A E : Nat → Nat → Bool)
    (hASym : ∀ x y, A x y = A y x)
    (hALoops : ∀ x, A x x = false)
    (hOldEq : ∀ x y, x < b → y < b → x ≠ y → A x y = E x y)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (hAFree : ¬ HasCliqueBelow A N ell)
    (W : Finset Nat) (sort : Nat → Fin d)
    (B : IntegerGraphSupport d ell → Nat)
    (hFuture : ∀ x ∈ W, b ≤ x ∧ x < N)
    (hUniversal : ∀ v : IntegerCliqueWeights d ell,
      v ∈ feasibleIntegerCliqueVectors d ell B →
        ∃ s : Finset Nat,
          s ⊆ W ∧ IsDirectedCliqueOn A s ∧
          (∀ T : IntegerGraphSupport d ell,
            (s.filter (fun x => sort x ∈ T.1)).card =
              integerCliqueOnSupport v T))
    (hNoSpurious : ∀ s : Finset Nat,
      s ⊆ W → IsDirectedCliqueOn A s →
      ∀ T : IntegerGraphSupport d ell,
        (s.filter (fun x => sort x ∈ T.1)).card ≤ B T) :
    ∃ f : Nat → Nat,
      (∀ i, i < b → f i = i) ∧
      (∀ i j, i < N → j < N → i < j → f i < f j) ∧
      (∀ i j, i < N → j < N → i ≠ j →
        E (f i) (f j) = A i j) ∧
      (∀ m, b ≤ m → m < N → ∀ z, z < f m →
        z ∉ (Finset.range m).image f →
          E z (f m) = false ∧ E (f m) z = false) ∧
      (∀ x ∈ W, b ≤ f x) ∧
      (∀ v : IntegerCliqueWeights d ell,
        v ∈ feasibleIntegerCliqueVectors d ell B ↔
        ∃ t : Finset Nat,
          t ⊆ W.image f ∧ IsDirectedCliqueOn E t ∧
          (∀ T : IntegerGraphSupport d ell,
            (t.filter (pulledBackFiniteSortIn W sort f T)).card =
              integerCliqueOnSupport v T)) := by
  classical
  obtain ⟨f,hFix,hMono,hGraph,hGaps⟩ :=
    henson_leftDense_embeds_finite_over_fixed_prefix
      ell b N hell hbN A E hASym hALoops hOldEq
      hAvoid hDense hAFree
  have hInjW : Set.InjOn f ↑W := by
    intro x hx y hy heq
    have hxN := (hFuture x hx).2
    have hyN := (hFuture y hy).2
    rcases lt_trichotomy x y with hxy | hEq | hyx
    · have hlt := hMono x y hxN hyN hxy
      omega
    · exact hEq
    · have hlt := hMono y x hyN hxN hyx
      omega
  have hWGraph :
      ∀ x ∈ W, ∀ y ∈ W, x ≠ y →
        A x y = E (f x) (f y) := by
    intro x hx y hy hxy
    exact (hGraph x y
      (hFuture x hx).2 (hFuture y hy).2 hxy).symm
  have hFuturesAfter : ∀ x ∈ W, b ≤ f x := by
    intro x hx
    have hbx := (hFuture x hx).1
    have hxN := (hFuture x hx).2
    by_cases hb0 : b = 0
    · omega
    · have hLast : b - 1 < b := by omega
      have hLastN : b - 1 < N := by omega
      have hLastBefore : b - 1 < x := by omega
      have hfLast := hFix (b - 1) hLast
      have hMon := hMono (b - 1) x hLastN hxN hLastBefore
      omega
  refine ⟨f,hFix,hMono,hGraph,hGaps,hFuturesAfter,?_⟩
  intro v
  constructor
  · intro hv
    obtain ⟨s,hsW,hsClique,hsCounts⟩ := hUniversal v hv
    refine ⟨s.image f, Finset.image_subset_image hsW, ?_, ?_⟩
    · exact (finiteClique_iff_injective_image
        A E W s f hsW hInjW hWGraph).mp hsClique
    · intro T
      exact (pulledBackFiniteSort_count_image_eq
        W s sort f hsW hInjW T).trans (hsCounts T)
  · rintro ⟨t,htW,htClique,htCounts⟩
    let s : Finset Nat := W.filter (fun x => f x ∈ t)
    have hsW : s ⊆ W := Finset.filter_subset _ _
    have hsImage : s.image f = t :=
      finiteImage_pullback_image_eq W t f htW
    have hsClique : IsDirectedCliqueOn A s := by
      apply (finiteClique_iff_injective_image
        A E W s f hsW hInjW hWGraph).mpr
      rw [hsImage]
      exact htClique
    change v ∈ Finset.univ.filter
      (WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell)) B)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro T
    have hCountImage := pulledBackFiniteSort_count_image_eq
      W s sort f hsW hInjW T
    rw [hsImage] at hCountImage
    have hBound := hNoSpurious s hsW hsClique T
    rw [←hCountImage,htCounts T] at hBound
    exact hBound

#print axioms Kk.pulledBackFiniteSort_count_image_eq
#print axioms Kk.finiteClique_iff_injective_image
#print axioms Kk.finiteImage_pullback_image_eq
#print axioms Kk.henson_leftDense_uniform_finite_profiles_over_fixed_prefix

end Kk
