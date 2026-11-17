import Kk.TrackFPositiveInsertionCapacity
import Kk.TrackFActualCodingFibre
import Kk.TrackFRankLargeFiniteFan
import Mathlib.Tactic

/-!
# Track F: actual triangle richness at manuscript singleton rank three

The English proof and hostile audit were committed before Lean in:
docs/track_f_rank_three_triangle_english_audit.md

Rank here is zero-based; rank 2 means manuscript rank 3.
All selected x,y,z are ACTUAL original-vertex coding nodes,
not hypothetical types. We use THREE rank-one large disjoint-marker
daughters, preserve rank one when inserting x as a neighbour
of b,c, choose a rank-zero DENSE descendant of c_x, then choose
y LATE beyond its new markers from b_x. Exact mutual-neighbour
capacity preserves rank zero when inserting y into c0; density
then supplies z adjacent to x and y, forming a true triangle.

No published diary characterization, Henson OnePointLeftDense
hypothesis, or BRD theorem is assumed in this conditional richness.
-/

namespace Kk.HensonOneType

variable {ell : Nat} {E : Nat → Nat → Bool}

/-- Pairwise disjoint FRESH positive markers over common u
imply any old positive neighbour shared by b and c belongs
to u. Neither b nor c needs to have the same level. -/
theorem shared_neighbours_sub_root_of_disjoint_fresh
    (u b c : HensonOneType ell E)
    (hDisj : Disjoint (b.neighbours \ u.neighbours)
      (c.neighbours \ u.neighbours)) :
    b.neighbours ∩ c.neighbours ⊆ u.neighbours := by
  classical
  intro x hx
  have hxb : x ∈ b.neighbours := (Finset.mem_inter.mp hx).1
  have hxc : x ∈ c.neighbours := (Finset.mem_inter.mp hx).2
  by_contra hxNotU
  exact (Finset.disjoint_left.mp hDisj)
    (Finset.mem_sdiff.mpr ⟨hxb, hxNotU⟩)
    (Finset.mem_sdiff.mpr ⟨hxc, hxNotU⟩)

/-- If x is a REAL coding vertex beyond all old markers of a,b
and is chosen above the zero-padding of a, then its complete
old column has NO positive edge to b's fresh markers. All
actual b-old vertices mutually adjacent to x belong to
the common source root u. This retains both edge directions. -/
theorem mutual_sub_root_from_disjoint_coding
    (u a b x : HensonOneType ell E)
    (H : Nat)
    (haH : a.level ≤ H)
    (hbH : b.level ≤ H)
    (hAx : zeroPad a H haH ≤ x)
    (hxCoding : IsCodingNode x)
    (hDisj : Disjoint (a.neighbours \ u.neighbours)
      (b.neighbours \ u.neighbours)) :
    mutualLinkedNeighbours E b.neighbours x.level ⊆
      u.neighbours := by
  classical
  intro p hp
  have hpB : p ∈ b.neighbours :=
    (Finset.mem_filter.mp hp).1
  by_contra hpNotU
  have hpFreshB : p ∈ b.neighbours \ u.neighbours :=
    Finset.mem_sdiff.mpr ⟨hpB, hpNotU⟩
  have hpLtH : p < H :=
    lt_of_lt_of_le (b.below p hpB) hbH
  have hpLtX : p < x.level :=
    lt_of_lt_of_le hpLtH hAx.1
  have hpEdge : E p x.level = true :=
    (Finset.mem_filter.mp hp).2.1
  have hpX : p ∈ x.neighbours := by
    have hpDecision := (hxCoding p hpLtX).1
    have hTrue : decide (p ∈ x.neighbours) = true :=
      hpDecision.symm.trans hpEdge
    simpa only [decide_eq_true_eq] using hTrue
  have hpA : p ∈ a.neighbours := by
    have hPad : p ∈ (zeroPad a H haH).neighbours :=
      (hAx.2 p hpLtH).mpr hpX
    exact hPad
  exact (Finset.disjoint_left.mp hDisj)
    (Finset.mem_sdiff.mpr ⟨hpA,hpNotU⟩)
    hpFreshB

/-- A rank-two source u and rank-one daughter d, together with a
REAL later coding original x whose mutual neighbourhood with d
lies inside u, yield a safe positive extension d_x of EXACTLY
the same rank one. This is the full graph-specific rank-budget
argument used twice in the triangle proof. -/
theorem safe_insert_keeps_rank_one
    (u d : HensonOneType ell E)
    (x : Nat) (hdx : d.level ≤ x)
    (huRank : rank u = 2)
    (hdRank : rank d = 1)
    (hMutual :
      mutualLinkedNeighbours E d.neighbours x ⊆
        u.neighbours) :
    ∃ hSafe : finitePoolCliqueCheck E (ell - 1)
        (insert x d.neighbours) = false,
      rank (appendPositive d x hdx hSafe) = 1 := by
  have hUSafe :
      finiteDirectedCliqueCapacity E u.neighbours < ell - 1 :=
    (finitePoolCliqueCheck_false_iff_capacity_lt
      E (ell - 1) u.neighbours).1 u.safe
  have hDSafe :
      finiteDirectedCliqueCapacity E d.neighbours < ell - 1 :=
    (finitePoolCliqueCheck_false_iff_capacity_lt
      E (ell - 1) d.neighbours).1 d.safe
  have hUCap : finiteDirectedCliqueCapacity E u.neighbours + 4 = ell := by
    dsimp [rank, finiteHensonTypeRank] at huRank
    omega
  have hDCap : finiteDirectedCliqueCapacity E d.neighbours + 3 = ell := by
    dsimp [rank, finiteHensonTypeRank] at hdRank
    omega
  have hxNot : x ∉ d.neighbours := by
    intro hxD
    have hxLt := d.below x hxD
    omega
  have hMutualCap :
      finiteDirectedCliqueCapacity E
        (mutualLinkedNeighbours E d.neighbours x) ≤
      finiteDirectedCliqueCapacity E u.neighbours :=
    finiteDirectedCliqueCapacity_mono E
      (mutualLinkedNeighbours E d.neighbours x)
      u.neighbours hMutual
  have hInsertEq :
      finiteDirectedCliqueCapacity E (insert x d.neighbours) =
        finiteDirectedCliqueCapacity E d.neighbours :=
    finiteDirectedCliqueCapacity_insert_eq_of_safe_mutual
      E d.neighbours x hxNot (by omega)
  have hSafe : finitePoolCliqueCheck E (ell - 1)
      (insert x d.neighbours) = false := by
    apply (finitePoolCliqueCheck_false_iff_capacity_lt
      E (ell - 1) (insert x d.neighbours)).2
    rw [hInsertEq]
    exact hDSafe
  exact ⟨hSafe, (rank_appendPositive_eq_of_capacity
    d x hdx hSafe hInsertEq).trans hdRank⟩

/-- Every rank-two-large set of ACTUAL original coding vertices
contains a genuine 3-clique. This is manuscript singleton
RANK THREE (Lean zero-based rank 2).

The x/c0/y/z ordering is essential: choose the third daughter's
rank-zero dense cone BEFORE choosing the second coding vertex,
so y can be zero padded past all extra third-daughter markers.
No Henson left-density or diary/BRD axiom is assumed. -/
theorem rank_two_large_actualCoding_contains_triangle
    (S : Set (HensonOneType ell E))
    (u : HensonOneType ell E)
    (hu : rank u = 2)
    (hLarge : RankLargeness.Large rank S 2 u)
    (hActual : ∀ z : HensonOneType ell E,
      z ∈ S → IsCodingNode z) :
    ∃ x y z : HensonOneType ell E,
      x ∈ S ∧ y ∈ S ∧ z ∈ S ∧
      x.level < y.level ∧ y.level < z.level ∧
      E x.level y.level = true ∧
      E y.level x.level = true ∧
      E x.level z.level = true ∧
      E z.level x.level = true ∧
      E y.level z.level = true ∧
      E z.level y.level = true := by
  classical
  have hEmpty :
      ∀ t ∈ (∅ : Finset (HensonOneType ell E)),
        u ≤ t ∧ rank t = 1 := by
    intro t ht
    simp at ht
  obtain ⟨a, hua, haRank, haLarge, _, _⟩ :=
    rank_large_fresh_daughter S 1 u hu hLarge
      (∅ : Finset (HensonOneType ell E)) hEmpty
  have hA : ∀ t ∈ ({a} : Finset (HensonOneType ell E)),
      u ≤ t ∧ rank t = 1 := by
    intro t ht
    have hta : t = a := Finset.mem_singleton.mp ht
    subst t
    exact ⟨hua,haRank⟩
  obtain ⟨b, hub, hbRank, hbLarge, _, hMarkB⟩ :=
    rank_large_fresh_daughter S 1 u hu hLarge
      ({a} : Finset (HensonOneType ell E)) hA
  have hAB : Disjoint (a.neighbours \ u.neighbours)
      (b.neighbours \ u.neighbours) :=
    hMarkB a (by simp)
  have hABFamily : ∀ t ∈
      ({a,b} : Finset (HensonOneType ell E)),
        u ≤ t ∧ rank t = 1 := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with hta | htb
    · subst t; exact ⟨hua,haRank⟩
    · subst t; exact ⟨hub,hbRank⟩
  obtain ⟨c, huc, hcRank, hcLarge, _, hMarkC⟩ :=
    rank_large_fresh_daughter S 1 u hu hLarge
      ({a,b} : Finset (HensonOneType ell E)) hABFamily
  have hAC : Disjoint (a.neighbours \ u.neighbours)
      (c.neighbours \ u.neighbours) :=
    hMarkC a (by simp)
  have hBC : Disjoint (b.neighbours \ u.neighbours)
      (c.neighbours \ u.neighbours) :=
    hMarkC b (by simp)
  let H : Nat := max a.level (max b.level c.level)
  have haH : a.level ≤ H := le_max_left _ _
  have hbH : b.level ≤ H :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hcH : c.level ≤ H :=
    (le_max_right _ _).trans (le_max_right _ _)
  let az : HensonOneType ell E := zeroPad a H haH
  have haz : a ≤ az := le_zeroPad a H haH
  have hazRank : rank az = 1 := (rank_zeroPad a H haH).trans haRank
  have hazLarge : RankLargeness.Large rank S 1 az :=
    RankLargeness.large_mono_cone rank S 1 a az haz haLarge
  obtain ⟨x, hazx, hxS⟩ :=
    RankLargeness.large_has_member rank S 1 az hazRank hazLarge
  have hxCoding : IsCodingNode x := hActual x hxS
  have hHx : H ≤ x.level := hazx.1
  have hbX : b.level ≤ x.level := hbH.trans hHx
  have hcX : c.level ≤ x.level := hcH.trans hHx
  have hMutB :
      mutualLinkedNeighbours E b.neighbours x.level ⊆
        u.neighbours :=
    mutual_sub_root_from_disjoint_coding
      u a b x H haH hbH hazx hxCoding hAB
  have hMutC :
      mutualLinkedNeighbours E c.neighbours x.level ⊆
        u.neighbours :=
    mutual_sub_root_from_disjoint_coding
      u a c x H haH hcH hazx hxCoding hAC
  obtain ⟨hbSafe, hbXRank⟩ :=
    safe_insert_keeps_rank_one u b x.level hbX hu hbRank hMutB
  obtain ⟨hcSafe, hcXRank⟩ :=
    safe_insert_keeps_rank_one u c x.level hcX hu hcRank hMutC
  let bx : HensonOneType ell E :=
    appendPositive b x.level hbX hbSafe
  let cx : HensonOneType ell E :=
    appendPositive c x.level hcX hcSafe
  have hbbx : b ≤ bx := le_appendPositive b x.level hbX hbSafe
  have hccx : c ≤ cx := le_appendPositive c x.level hcX hcSafe
  have hBXRank : rank bx = 1 := hbXRank
  have hCXRank : rank cx = 1 := hcXRank
  have hBXLarge : RankLargeness.Large rank S 1 bx :=
    RankLargeness.large_mono_cone rank S 1 b bx hbbx hbLarge
  have hCXLarge : RankLargeness.Large rank S 1 cx :=
    RankLargeness.large_mono_cone rank S 1 c cx hccx hcLarge
  obtain ⟨c0, hcxc0, hc0Rank, hc0Large⟩ :=
    hCXLarge cx (le_refl cx) hCXRank
  let K : Nat := max bx.level c0.level
  have hbK : bx.level ≤ K := le_max_left _ _
  have hc0K : c0.level ≤ K := le_max_right _ _
  let bz : HensonOneType ell E := zeroPad bx K hbK
  have hbbz : bx ≤ bz := le_zeroPad bx K hbK
  have hbzRank : rank bz = 1 := (rank_zeroPad bx K hbK).trans hBXRank
  have hbzLarge : RankLargeness.Large rank S 1 bz :=
    RankLargeness.large_mono_cone rank S 1 bx bz hbbz hBXLarge
  obtain ⟨y, hbzy, hyS⟩ :=
    RankLargeness.large_has_member rank S 1 bz hbzRank hbzLarge
  have hyCoding : IsCodingNode y := hActual y hyS
  have hKy : K ≤ y.level := hbzy.1
  have hc0y : c0.level ≤ y.level := hc0K.trans hKy
  have hxy : x.level < y.level := by
    have hxb : x.level + 1 ≤ bx.level := by
      dsimp [bx, appendPositive]
      omega
    omega
  have hxInBz : x.level ∈ bz.neighbours := by
    change x.level ∈ bx.neighbours
    change x.level ∈ insert x.level b.neighbours
    exact Finset.mem_insert_self _ _
  have hxInY : x.level ∈ y.neighbours :=
    (hbzy.2 x.level (by omega)).mp hxInBz
  have hXYTrue : E x.level y.level = true := by
    have h := (hyCoding x.level hxy).1
    simpa [hxInY] using h
  have hYXTrue : E y.level x.level = true := by
    have h := (hyCoding x.level hxy).2
    simpa [hxInY] using h
  have hC0CapSafe :
      finiteDirectedCliqueCapacity E c0.neighbours < ell - 1 :=
    (finitePoolCliqueCheck_false_iff_capacity_lt
      E (ell - 1) c0.neighbours).1 c0.safe
  have hUSafe :
      finiteDirectedCliqueCapacity E u.neighbours < ell - 1 :=
    (finitePoolCliqueCheck_false_iff_capacity_lt
      E (ell - 1) u.neighbours).1 u.safe
  have hUCap : finiteDirectedCliqueCapacity E u.neighbours + 4 = ell := by
    dsimp [rank, finiteHensonTypeRank] at hu
    omega
  have hC0Cap : finiteDirectedCliqueCapacity E c0.neighbours + 2 = ell := by
    dsimp [rank, finiteHensonTypeRank] at hc0Rank
    omega
  have hMutY :
      mutualLinkedNeighbours E c0.neighbours y.level ⊆
        insert x.level u.neighbours := by
    intro p hp
    have hpC0 : p ∈ c0.neighbours :=
      (Finset.mem_filter.mp hp).1
    have hpLtC0 : p < c0.level := c0.below p hpC0
    have hpLtK : p < K := lt_of_lt_of_le hpLtC0 hc0K
    have hpLtY : p < y.level := lt_of_lt_of_le hpLtK hKy
    have hpEdge : E p y.level = true :=
      (Finset.mem_filter.mp hp).2.1
    have hpY : p ∈ y.neighbours := by
      have hBit := (hyCoding p hpLtY).1
      have hTrue : decide (p ∈ y.neighbours) = true :=
        hBit.symm.trans hpEdge
      simpa only [decide_eq_true_eq] using hTrue
    have hpBz : p ∈ bz.neighbours :=
      (hbzy.2 p hpLtK).mpr hpY
    have hpBx : p ∈ bx.neighbours := hpBz
    have hpOld : p ∈ insert x.level b.neighbours := hpBx
    rcases Finset.mem_insert.mp hpOld with hpX | hpB
    · exact Finset.mem_insert.mpr (Or.inl hpX)
    · have hpLtX : p < x.level :=
        lt_of_lt_of_le (b.below p hpB) hbX
      have hpLtCX : p < cx.level := by
        dsimp [cx, appendPositive]
        omega
      have hpCX : p ∈ cx.neighbours :=
        (hcxc0.2 p hpLtCX).mpr hpC0
      have hpCInsert : p ∈ insert x.level c.neighbours := hpCX
      have hpC : p ∈ c.neighbours := by
        rcases Finset.mem_insert.mp hpCInsert with hEq | hC
        · have hNe : p ≠ x.level := by omega
          exact False.elim (hNe hEq)
        · exact hC
      have hpU : p ∈ u.neighbours :=
        shared_neighbours_sub_root_of_disjoint_fresh
          u b c hBC (Finset.mem_inter.mpr ⟨hpB, hpC⟩)
      exact Finset.mem_insert.mpr (Or.inr hpU)
  have hMutYCap :
      finiteDirectedCliqueCapacity E
        (mutualLinkedNeighbours E c0.neighbours y.level) ≤
      finiteDirectedCliqueCapacity E u.neighbours + 1 := by
    calc
      finiteDirectedCliqueCapacity E
          (mutualLinkedNeighbours E c0.neighbours y.level) ≤
        finiteDirectedCliqueCapacity E
          (insert x.level u.neighbours) :=
        finiteDirectedCliqueCapacity_mono E
          (mutualLinkedNeighbours E c0.neighbours y.level)
          (insert x.level u.neighbours) hMutY
      _ ≤ finiteDirectedCliqueCapacity E u.neighbours + 1 :=
        finiteDirectedCliqueCapacity_insert_le_succ_actual
          E u.neighbours x.level
  have hyNotC0 : y.level ∉ c0.neighbours := by
    intro hyC0
    have hyLt := c0.below y.level hyC0
    omega
  have hCapY :
      finiteDirectedCliqueCapacity E
        (insert y.level c0.neighbours) =
      finiteDirectedCliqueCapacity E c0.neighbours :=
    finiteDirectedCliqueCapacity_insert_eq_of_safe_mutual
      E c0.neighbours y.level hyNotC0 (by omega)
  have hSafeY :
      finitePoolCliqueCheck E (ell - 1)
        (insert y.level c0.neighbours) = false := by
    apply (finitePoolCliqueCheck_false_iff_capacity_lt
      E (ell - 1) (insert y.level c0.neighbours)).2
    rw [hCapY]
    exact hC0CapSafe
  let t : HensonOneType ell E :=
    appendPositive c0 y.level hc0y hSafeY
  have hc0t : c0 ≤ t := le_appendPositive c0 y.level hc0y hSafeY
  obtain ⟨z, htz, hzS⟩ := hc0Large t hc0t
  have hzCoding : IsCodingNode z := hActual z hzS
  have hyz : y.level < z.level := by
    have htLevel : t.level = y.level + 1 := rfl
    omega
  have hxCX : x.level ∈ cx.neighbours := by
    change x.level ∈ insert x.level c.neighbours
    exact Finset.mem_insert_self _ _
  have hxLtCX : x.level < cx.level := by
    dsimp [cx, appendPositive]
    omega
  have hxC0 : x.level ∈ c0.neighbours :=
    (hcxc0.2 x.level hxLtCX).mp hxCX
  have hxT : x.level ∈ t.neighbours := by
    change x.level ∈ insert y.level c0.neighbours
    exact Finset.mem_insert_of_mem hxC0
  have hyT : y.level ∈ t.neighbours := by
    change y.level ∈ insert y.level c0.neighbours
    exact Finset.mem_insert_self _ _
  have hxLtT : x.level < t.level := by
    dsimp [t, appendPositive]
    omega
  have hyLtT : y.level < t.level := by
    dsimp [t, appendPositive]
    omega
  have hxZ : x.level ∈ z.neighbours := (htz.2 x.level hxLtT).mp hxT
  have hyZ : y.level ∈ z.neighbours := (htz.2 y.level hyLtT).mp hyT
  have hXZ : E x.level z.level = true := by
    have h := (hzCoding x.level (lt_trans hxy hyz)).1
    simpa [hxZ] using h
  have hZX : E z.level x.level = true := by
    have h := (hzCoding x.level (lt_trans hxy hyz)).2
    simpa [hxZ] using h
  have hYZ : E y.level z.level = true := by
    have h := (hzCoding y.level hyz).1
    simpa [hyZ] using h
  have hZY : E z.level y.level = true := by
    have h := (hzCoding y.level hyz).2
    simpa [hyZ] using h
  exact ⟨x, y, z, hxS, hyS, hzS, hxy, hyz,
    hXYTrue, hYXTrue, hXZ, hZX, hYZ, hZY⟩

end Kk.HensonOneType
