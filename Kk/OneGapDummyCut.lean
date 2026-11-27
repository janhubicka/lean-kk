import Kk.OneGapPartialStructure
import Kk.OneGapStructuralExclusion
import Kk.OneGapPrescribedPool

/-!
# Omitted dummy cuts and complete retained pairs

A dummy has zero new ordinary bits, although retained future originals can
have nonzero old columns. Derive full next-type coherence and full corrected
B3 directly from the zero cut row. Retaining complete gap/vertex pairs
separately excludes original endpoints, including ineligible originals.

English proof and independent review precede this implementation:
`docs/one_gap_dummy_cut_english_audit_20261127.md`.
-/

namespace Kk
open SuccessorTree
open SuccessorTree.V10
open SuccessorTree.SMTree.Envelope

/-- The anchor and complete gap/vertex pairs for an actual finite selection. -/
def oneGapPairedLevels (S : Finset Nat) : Finset Nat :=
  insert 0 ((S.image (fun i => 2*i+1)) ∪ S.image oneGapAddress)

@[simp] theorem oneGapPairedLevels_zero (S : Finset Nat) :
    0 ∈ oneGapPairedLevels S := by
  simp [oneGapPairedLevels]

/-- A retained meaningful coordinate retains its actual preceding gap. -/
theorem oneGapPairedLevels_preceding_gap (S : Finset Nat) (v : Nat)
    (hv : v ∈ oneGapPairedLevels S) (hReal : oneGapReal v) :
    v-1 ∈ oneGapPairedLevels S := by
  change v ∈ insert 0 ((S.image (fun i => 2*i+1)) ∪ S.image oneGapAddress) at hv
  rcases Finset.mem_insert.mp hv with hZero | hPair
  · subst v
    have hPos := hReal.1
    omega
  · rcases Finset.mem_union.mp hPair with hGap | hVertex
    · obtain ⟨i, _hi, hEq⟩ := Finset.mem_image.mp hGap
      have hEven := hReal.2
      omega
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hVertex
      apply Finset.mem_insert_of_mem
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨i, hi, by unfold oneGapAddress; omega⟩

/-- Pair retention gives endpoint retention by the actual free-level formula. -/
theorem oneGap_freeLevel_mem_of_pair_retention
    (G : Nat → Nat → Bool) (N : Nat) (I : Set Nat) (hZero : 0 ∈ I)
    (v : Fin N) (hPair : oneGapReal v.val → v.val-1 ∈ I) :
    ((oneGapPartial G).finitePrefix N).freeLevel v.val ∈ I := by
  rw [oneGapPartial_freeLevel G N v.val v.isLt]
  split_ifs with hReal
  · exact hPair hReal
  · exact hZero

/-- Every name in complete finite pairs has its free endpoint in those pairs. -/
theorem oneGapPairedLevels_freeLevel_mem
    (G : Nat → Nat → Bool) (N : Nat) (S : Finset Nat)
    (v : Fin N) (hv : v.val ∈ oneGapPairedLevels S) :
    ((oneGapPartial G).finitePrefix N).freeLevel v.val ∈ oneGapPairedLevels S :=
  oneGap_freeLevel_mem_of_pair_retention G N (oneGapPairedLevels S : Set Nat)
    (oneGapPairedLevels_zero S) v (oneGapPairedLevels_preceding_gap S v.val hv)

/-- At a positive cut the sole possible endpoint is the next meaningful name.
Such an original is not eligible for the crossing source at this cut. -/
theorem oneGap_freeLevel_eq_positive_iff
    (G : Nat → Nat → Bool) (N cut : Nat) (hPos : 0 < cut) (v : Fin N) :
    ((oneGapPartial G).finitePrefix N).freeLevel v.val = cut ↔
      oneGapReal v.val ∧ v.val = cut+1 := by
  rw [oneGapPartial_freeLevel G N v.val v.isLt]
  by_cases hReal : oneGapReal v.val
  · rw [ite_eq_left hReal]
    simp only [hReal, true_and]
    have hVPos := hReal.1
    omega
  · simp [hReal, Nat.ne_of_lt hPos]

/-- Both new ordinary directions vanish at every dummy coordinate. -/
theorem oneGap_dummy_binary_zero
    (G : Nat → Nat → Bool) (N cut : Nat) (hDummy : ¬ oneGapReal cut)
    (v : Nat) :
    ((oneGapPartial G).finitePrefix N).L.binary cut v (0 : Fin 1) = false ∧
      ((oneGapPartial G).finitePrefix N).L.binary v cut (0 : Fin 1) = false := by
  change oneGapEdge G cut v = false ∧ oneGapEdge G v cut = false
  simp [oneGapEdge, hDummy]

/-- Actual finite one-gap prefixes inherit the original forbidden avoidance. -/
theorem oneGap_finitePrefix_avoids
    (G : Nat → Nat → Bool) (ell : Nat) (hell : 2 ≤ ell)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel G)) (N : Nat) :
    ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids ((oneGapPartial G).finitePrefix N).L :=
  (oneGapPartial G).finitePrefix_avoids_family (hensonForbiddenFamily ell hell)
    (oneGapPartial_avoids G ell hell hAvoid) N

private theorem oneGap_finitePrefix_graph_atoms
    (G : Nat → Nat → Bool) (N : Nat)
    (hSym : ∀ x y, G x y = G y x) (hLoops : ∀ x, G x x = false) :
    (∀ x y, ((oneGapPartial G).finitePrefix N).L.binary x y (0 : Fin 1) =
      ((oneGapPartial G).finitePrefix N).L.binary y x (0 : Fin 1)) ∧
    (∀ x, ((oneGapPartial G).finitePrefix N).L.binary x x (0 : Fin 1) = false) ∧
    (∀ x, ((oneGapPartial G).finitePrefix N).L.diagonal x (0 : Fin 1) = false) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    change oneGapEdge G x y = oneGapEdge G y x
    by_cases hx : oneGapReal x <;> by_cases hy : oneGapReal y <;>
      simp [oneGapEdge, hx, hy, hSym]
  · intro x
    change oneGapEdge G x x = false
    by_cases hx : oneGapReal x <;> simp [oneGapEdge, hx, hLoops]
  · intro x
    change oneGapEdge G x x = false
    by_cases hx : oneGapReal x <;> simp [oneGapEdge, hx, hLoops]

/-- Zero new cut bits supply full fibre coherence without any old-zero premise. -/
theorem oneGap_full_fibre_of_zero_cut
    (A : EnumeratedPartialStructure 1 0 1)
    (V : Set (Fin A.size)) (cut : Nat)
    (hSym : ∀ x y, A.L.binary x y (0 : Fin 1) = A.L.binary y x (0 : Fin 1))
    (hLoop : ∀ x, A.L.binary x x (0 : Fin 1) = false)
    (hDiag : ∀ x, A.L.diagonal x (0 : Fin 1) = false)
    (hZero : ∀ v, A.L.binary cut v (0 : Fin 1) = false) :
    ∀ v ∈ V, ∀ w ∈ V,
      cut+1 ≤ A.freeLevel v.val → cut+1 ≤ A.freeLevel w.val →
      A.partialTypeAt cut v.val = A.partialTypeAt cut w.val →
      A.partialTypeAt (cut+1) v.val = A.partialTypeAt (cut+1) w.val := by
  apply oneGap_full_fibre_of_pool_columns A V cut hSym hLoop hDiag
  intro v _hv w _hw _hFreeV _hFreeW _hOld
  rw [hZero v.val, hZero w.val]

/-- The actual complete retained-pool prescription satisfies full B3 at a zero
cut. Its source may be empty or contain auxiliary originals and cap types. -/
theorem oneGapRetainedPoolData_correctedB3_of_zero_cut
    (ell : Nat) (hell : 2 ≤ ell) (cut : Nat)
    (A : EnumeratedPartialStructure 1 0 1) (hCut : cut < A.size)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell → bad.Avoids A.L)
    (hSym : ∀ x y, A.L.binary x y (0 : Fin 1) = A.L.binary y x (0 : Fin 1))
    (V : Set (Fin A.size))
    (hZero : ∀ v, A.L.binary cut v (0 : Fin 1) = false) :
    (oneGapRetainedPoolData A cut V).CorrectedB3 (hensonForbiddenFamily ell hell) := by
  apply oneGap_correctedB3_of_no_positive ell hell cut A hCut hAvoid hSym
    (oneGapRetainedPoolData A cut V)
  intro T hT
  obtain ⟨v, _hv, _hFree, _hOld, hNew⟩ :=
    oneGapRetainedPoolData_source_original A cut V T hT
  exact ⟨v.val, hNew, hZero v.val⟩

/-- Construct an actual one-step map from a zero cut row and complete pool
coverage. This crossing theorem does not assert endpoint exclusion. -/
theorem oneGap_retained_pool_skip_of_zero_cut
    (ell : Nat) (hell : 2 ≤ ell) (cut : Nat)
    (A : EnumeratedPartialStructure 1 0 1)
    (hCut : cut < A.size) (hPos : 0 < cut)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell → bad.Avoids A.L)
    (hSym : ∀ x y, A.L.binary x y (0 : Fin 1) = A.L.binary y x (0 : Fin 1))
    (hLoop : ∀ x, A.L.binary x x (0 : Fin 1) = false)
    (hDiag : ∀ x, A.L.diagonal x (0 : Fin 1) = false)
    (V : Set (Fin A.size))
    (Z : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (hPool : Z ⊆ ambientPrefixPool (hensonForbiddenFamily ell hell) A hAvoid V)
    (hZero : ∀ v, A.L.binary cut v (0 : Fin 1) = false) :
    ∃ D : SMTree.MMap (normalizedKptSMTree (hensonForbiddenFamily ell hell)),
      D.map.SkipsOnly cut ∧
      ∀ ⦃z : AdmissibleKptNode (hensonForbiddenFamily ell hell)⦄, z ∈ Z →
        ∀ (hc : cut < LevelTree.lev z),
          D (LevelTree.ancestor z cut (Nat.le_of_lt hc)) =
            LevelTree.ancestor z (cut+1) (Nat.succ_le_iff.mpr hc) := by
  exact oneGap_skip_of_complete_prescribed_B3 (hensonForbiddenFamily ell hell)
    Z cut hPos (oneGapRetainedPoolData A cut V)
    (oneGapRetainedPoolData_covers _ A hAvoid cut V Z hPool
      (oneGap_full_fibre_of_zero_cut A V cut hSym hLoop hDiag hZero))
    (oneGapRetainedPoolData_targets_admissible _ A hAvoid cut V)
    (oneGapRetainedPoolData_correctedB3_of_zero_cut ell hell cut A hCut
      hAvoid hSym V hZero)

/-- Dummy fibre coherence is derived from the actual padding, with no selected
front, selected age, old-column-zero or next-type coherence assumption. -/
theorem oneGap_dummy_full_fibre
    (G : Nat → Nat → Bool) (ell : Nat) (hell : 2 ≤ ell)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel G))
    (N cut : Nat) (hDummy : ¬ oneGapReal cut) (V : Set (Fin N)) :
    ∀ v ∈ V, ∀ w ∈ V,
      cut+1 ≤ ((oneGapPartial G).finitePrefix N).freeLevel v.val →
      cut+1 ≤ ((oneGapPartial G).finitePrefix N).freeLevel w.val →
      ((oneGapPartial G).finitePrefix N).partialTypeAt cut v.val =
        ((oneGapPartial G).finitePrefix N).partialTypeAt cut w.val →
      ((oneGapPartial G).finitePrefix N).partialTypeAt (cut+1) v.val =
        ((oneGapPartial G).finitePrefix N).partialTypeAt (cut+1) w.val := by
  obtain ⟨hLoops, hSym, _hNoClique⟩ :=
    (hensonForbiddenFamily_avoids_iff ell hell G).mp hAvoid
  obtain ⟨hSymA, hLoopA, hDiagA⟩ := oneGap_finitePrefix_graph_atoms G N hSym hLoops
  exact oneGap_full_fibre_of_zero_cut ((oneGapPartial G).finitePrefix N) V cut
    hSymA hLoopA hDiagA (fun v => (oneGap_dummy_binary_zero G N cut hDummy v).1)

/-- The possible immediate-successor endpoint is explicitly excluded.
Fibre coherence alone would not exclude this original's self-meet. -/
theorem oneGap_dummy_originals_no_meet
    (G : Nat → Nat → Bool) (ell : Nat) (hell : 2 ≤ ell)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel G))
    (N cut : Nat) (hPos : 0 < cut) (hDummy : ¬ oneGapReal cut)
    (V : Set (Fin N)) (hNext : ∀ v ∈ V, v.val ≠ cut+1) :
    ∀ v ∈ V, ∀ w ∈ V,
      SMTree.Envelope.SameComponent
        (((oneGapPartial G).finitePrefix N).kptOriginal
          (hensonForbiddenFamily ell hell) (oneGap_finitePrefix_avoids G ell hell hAvoid N) v)
        (((oneGapPartial G).finitePrefix N).kptOriginal
          (hensonForbiddenFamily ell hell) (oneGap_finitePrefix_avoids G ell hell hAvoid N) w) →
      LevelTree.lev (LevelTree.meet
        (((oneGapPartial G).finitePrefix N).kptOriginal
          (hensonForbiddenFamily ell hell) (oneGap_finitePrefix_avoids G ell hell hAvoid N) v)
        (((oneGapPartial G).finitePrefix N).kptOriginal
          (hensonForbiddenFamily ell hell) (oneGap_finitePrefix_avoids G ell hell hAvoid N) w)) ≠ cut := by
  apply oneGap_originals_no_meet_of_full_fibre (hensonForbiddenFamily ell hell)
    ((oneGapPartial G).finitePrefix N) (oneGap_finitePrefix_avoids G ell hell hAvoid N)
    V cut
  · intro v hv hEnd
    exact hNext v hv ((oneGap_freeLevel_eq_positive_iff G N cut hPos v).mp hEnd).2
  · exact oneGap_dummy_full_fibre G ell hell hAvoid N cut hDummy V

/-- A concrete dummy-cut skipping map for the actual padded ambient prefix. -/
theorem oneGap_dummy_retained_pool_skip
    (G : Nat → Nat → Bool) (ell : Nat) (hell : 2 ≤ ell)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel G))
    (N cut : Nat) (hCut : cut < N) (hPos : 0 < cut)
    (hDummy : ¬ oneGapReal cut) (V : Set (Fin N))
    (Z : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (hPool : Z ⊆ ambientPrefixPool (hensonForbiddenFamily ell hell)
      ((oneGapPartial G).finitePrefix N) (oneGap_finitePrefix_avoids G ell hell hAvoid N) V) :
    ∃ D : SMTree.MMap (normalizedKptSMTree (hensonForbiddenFamily ell hell)),
      D.map.SkipsOnly cut ∧
      ∀ ⦃z : AdmissibleKptNode (hensonForbiddenFamily ell hell)⦄, z ∈ Z →
        ∀ (hc : cut < LevelTree.lev z),
          D (LevelTree.ancestor z cut (Nat.le_of_lt hc)) =
            LevelTree.ancestor z (cut+1) (Nat.succ_le_iff.mpr hc) := by
  obtain ⟨hLoops, hSym, _hNoClique⟩ :=
    (hensonForbiddenFamily_avoids_iff ell hell G).mp hAvoid
  obtain ⟨hSymA, hLoopA, hDiagA⟩ := oneGap_finitePrefix_graph_atoms G N hSym hLoops
  exact oneGap_retained_pool_skip_of_zero_cut ell hell cut
    ((oneGapPartial G).finitePrefix N) hCut hPos
    (oneGap_finitePrefix_avoids G ell hell hAvoid N) hSymA hLoopA hDiagA V Z hPool
    (fun v => (oneGap_dummy_binary_zero G N cut hDummy v).1)

/-- In the actual padded structure, selected ordinary hypotheses are required
only at meaningful omitted cuts. Dummy cuts use their zero new bits directly.
The anchor and real originals' preceding gaps supply endpoint retention. -/
theorem oneGap_planned_envelope_of_real_selected_neutrality
    (G : Nat → Nat → Bool) (ell : Nat) (hell : 2 ≤ ell)
    (hAvoidG : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel G)) (N : Nat)
    (X : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (top : Nat) (hTopSize : top < N) (hXBound : X ⊆ levelLe top)
    (I : Set Nat) (hZero : 0 ∈ I) (hTop : top ∈ I)
    (hBound : ∀ q ∈ I, q ≤ top)
    (U V : Set (Fin N))
    (hX : X ⊆ ambientPrefixPool (hensonForbiddenFamily ell hell)
      ((oneGapPartial G).finitePrefix N) (oneGap_finitePrefix_avoids G ell hell hAvoidG N) U)
    (hUV : U ⊆ V)
    (hRet : ∀ i : Fin N, i.val ∈ I →
      0 < ((oneGapPartial G).finitePrefix N).freeLevel i.val → i ∈ V)
    (hSeedRet : ∀ z ∈ X, LevelTree.lev z ∈ I)
    (hPairRet : ∀ v ∈ V, oneGapReal v.val → v.val-1 ∈ I)
    (d : Nat → Nat) (selected : (c : Nat) → Fin (d c) → Nat)
    (hPositive : ∀ c, c < top → c ∉ I → oneGapReal c →
      ∀ v ∈ V, c+1 ≤ ((oneGapPartial G).finitePrefix N).freeLevel v.val →
        oneGapEdge G c v.val = true → ∃ j, v.val = selected c j)
    (hNoSplit : ∀ c, c < top → c ∉ I → oneGapReal c → ∀ i j : Fin (d c),
      c < selected c i → c < selected c j →
      (∀ p < c, oneGapEdge G p (selected c i) = oneGapEdge G p (selected c j)) →
      oneGapEdge G c (selected c i) = oneGapEdge G c (selected c j))
    (hOtherZero : ∀ c, c < top → c ∉ I → oneGapReal c →
      ∀ v ∈ V, c+1 ≤ ((oneGapPartial G).finitePrefix N).freeLevel v.val →
      (¬ ∃ j, v.val = selected c j) → ∀ p < c, oneGapEdge G p v.val = false)
    (hAge : ∀ c, c < top → c ∉ I → oneGapReal c →
      ∀ T : IntegerGraphSupport (d c) ell,
      integerGraphAgeCanonical (d c) ell
        (finiteOldColumnRawBound (oneGapEdge G) ell (d c)
          (Finset.range c) (fun p j => oneGapEdge G p (selected c j))) T =
      integerGraphAgeCanonical (d c) ell
        (finiteOldColumnRawBound (oneGapEdge G) ell (d c)
          (Finset.range (c+1)) (fun p j => oneGapEdge G p (selected c j))) T) :
    ∃ F : SMTree.MMap (normalizedKptSMTree (hensonForbiddenFamily ell hell)),
      StageFullInvariant (normalizedKptSMTree (hensonForbiddenFamily ell hell))
        X top 0 I F ∧ F.map.levelRange = {q | q ∈ I ∨ top < q} := by
  let family := hensonForbiddenFamily ell hell
  let A := (oneGapPartial G).finitePrefix N
  have hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L :=
    oneGap_finitePrefix_avoids G ell hell hAvoidG N
  obtain ⟨hLoopsG, hSymG, _hNoClique⟩ :=
    (hensonForbiddenFamily_avoids_iff ell hell G).mp hAvoidG
  obtain ⟨hSym, hLoop, hDiag⟩ := oneGap_finitePrefix_graph_atoms G N hSymG hLoopsG
  have hEndRet : ∀ v ∈ V, A.freeLevel v.val ∈ I := by
    intro v hv
    exact oneGap_freeLevel_mem_of_pair_retention G N I hZero v (hPairRet v hv)
  have hLocal : ∀ c : Nat, c < top → c ∉ I →
      let Z := closure (admissibleKptSTree family) {q | q ∈ I ∧ c+1 ≤ q} X
      (∀ z ∈ Z, LevelTree.lev z ≠ c) ∧
        ∃ F : PrescribedBoringData c 1 0 1,
          CoversClosureCrossing family Z c F ∧
          (∀ S, S ∈ F.source → IsAdmissibleRawType family
            (⟨c+1,F.target S⟩ : RawPartialTypeNode 1 0 1)) ∧
          F.CorrectedB3 family := by
    intro c hc hNot
    have hCut : c < A.size := by change c < N; omega
    have hCutData :
        (∀ v ∈ V, ∀ w ∈ V,
          c+1 ≤ A.freeLevel v.val → c+1 ≤ A.freeLevel w.val →
          A.partialTypeAt c v.val = A.partialTypeAt c w.val →
          A.partialTypeAt (c+1) v.val = A.partialTypeAt (c+1) w.val) ∧
        (oneGapRetainedPoolData A c V).CorrectedB3 family := by
      by_cases hReal : oneGapReal c
      · exact ⟨oneGap_full_fibre_of_selected_neutrality
          A ell (d c) c hell V (selected c) hSym hLoop hDiag
          (hPositive c hc hNot hReal) (hNoSplit c hc hNot hReal)
          (hOtherZero c hc hNot hReal) (hAge c hc hNot hReal),
          oneGapRetainedPoolData_correctedB3_all ell hell (d c) c A hCut
            hAvoid hSym V (selected c) (hPositive c hc hNot hReal) (hAge c hc hNot hReal)⟩
      · have hZeroCut : ∀ v, A.L.binary c v (0 : Fin 1) = false :=
          fun v => (oneGap_dummy_binary_zero G N c hReal v).1
        exact ⟨oneGap_full_fibre_of_zero_cut A V c hSym hLoop hDiag hZeroCut,
          oneGapRetainedPoolData_correctedB3_of_zero_cut ell hell c A hCut
            hAvoid hSym V hZeroCut⟩
    have hRetStage : ∀ i : Fin A.size,
        i.val ∈ {q | q ∈ I ∧ c+1 ≤ q} → 0 < A.freeLevel i.val → i ∈ V :=
      fun i hi => hRet i hi.1
    have hSeed : ∀ z ∈ X, LevelTree.lev z ≠ c := by
      intro z hz heq
      exact hNot (heq ▸ hSeedRet z hz)
    have hEnd : ∀ v ∈ V, A.freeLevel v.val ≠ c := by
      intro v hv heq
      exact hNot (heq ▸ hEndRet v hv)
    have hStructural := oneGap_planned_closure_structural_of_full_fibre
      family A hAvoid {q | q ∈ I ∧ c+1 ≤ q} X U V
      hX hUV hRetStage c hSeed hEnd hCutData.1
    refine ⟨?_, oneGapRetainedPoolData A c V, ?_, ?_, hCutData.2⟩
    · intro z hz hlev
      exact hStructural.1 ⟨z, hz, hlev⟩
    · exact oneGapRetainedPoolData_covers_planned_closure family A hAvoid
        c {q | q ∈ I ∧ c+1 ≤ q} X U V hX hUV hRetStage hCutData.1
    · exact oneGapRetainedPoolData_targets_admissible family A hAvoid c V
  obtain ⟨F, hF⟩ := oneGap_planned_Kpt_envelope family X top hXBound
    I hZero hTop hBound hLocal
  refine ⟨F, hF, ?_⟩
  simpa only [Nat.not_lt_zero, false_or] using
    stageFullInvariant_levelRange (normalizedKptSMTree family) X top 0 I F hF

end Kk
