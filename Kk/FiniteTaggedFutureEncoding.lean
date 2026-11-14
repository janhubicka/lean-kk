import Kk.UniversalFutureDisjointCliques
import Mathlib.Tactic

/-!
# Track A: finite tagged future numbered exactly after a fixed old prefix

English proof and adversarial audit FIRST:
  docs/finite_tagged_future_encoding_english_audit.md

For ANY finite type V, code_b:V→Nat injects onto the exact
interval [b,b+card V), with a total Option decoder. An arbitrary
symmetric loop-free finite V graph R can then be glued to the
unchanged old original table E on the literal prefix [0,b),
using *complete symmetric typed old-to-new columns* c.
The resulting Boolean table A is total on Nat, symmetric,
loop-free and copies every directed old/future/future atom exactly.

This only constructs and verifies the finite numbering and graph
table. It does NOT silently assert that the glued A is K_ell-free.
That requires the all-support old-neighbourhood raw-bound criterion
and the existing universal future clique-profile theorem before
one may invoke pinned Henson realization.
-/

namespace Kk

/-- The chosen code of a vertex of any finite type V, immediately
after the ENTIRE fixed old original prefix [0,b). No canonical
ordering of V is postulated or needed. -/
noncomputable def finiteTaggedIndex
    {V : Type*} [Fintype V] (b : Nat) (v : V) : Nat :=
  b + ((Fintype.equivFin V) v).val

/-- Every coded future lies in the exact new index interval. -/
theorem finiteTaggedIndex_range
    {V : Type*} [Fintype V] (b : Nat) (v : V) :
    b ≤ finiteTaggedIndex b v ∧
      finiteTaggedIndex b v < b + Fintype.card V := by
  have hv := ((Fintype.equivFin V) v).isLt
  dsimp [finiteTaggedIndex]
  omega

/-- No two distinct tagged future vertices share one original name. -/
theorem finiteTaggedIndex_injective
    {V : Type*} [Fintype V] (b : Nat) :
    Function.Injective (finiteTaggedIndex (V := V) b) := by
  intro x y h
  have hVal :
      ((Fintype.equivFin V) x).val =
        ((Fintype.equivFin V) y).val := by
    dsimp [finiteTaggedIndex] at h
    omega
  exact (Fintype.equivFin V).injective (Fin.ext hVal)

/-- Every index in [b,b+card V) codes a vertex of V.
For V=empty the interval is empty and the theorem is vacuous. -/
theorem finiteTaggedIndex_surjective_interval
    {V : Type*} [Fintype V] (b n : Nat)
    (hb : b ≤ n) (hn : n < b + Fintype.card V) :
    ∃ v : V, finiteTaggedIndex b v = n := by
  classical
  let t : Fin (Fintype.card V) := ⟨n - b, by omega⟩
  refine ⟨(Fintype.equivFin V).symm t,?_⟩
  unfold finiteTaggedIndex
  rw [Equiv.apply_symm_apply]
  dsimp [t]
  omega

/-- A total Option-valued inverse of the exact fresh interval.
Unlike an arbitrary default element of V, this works if V=empty. -/
noncomputable def finiteTaggedDecode
    {V : Type*} [Fintype V] (b n : Nat) : Option V :=
  if h : b ≤ n ∧ n < b + Fintype.card V then
    some ((Fintype.equivFin V).symm ⟨n-b, by omega⟩)
  else none

/-- The decoder inverts the code ON EVERY actual tagged future. -/
theorem finiteTaggedDecode_index
    {V : Type*} [Fintype V] (b : Nat) (v : V) :
    finiteTaggedDecode b (finiteTaggedIndex b v) = some v := by
  classical
  have hRange := finiteTaggedIndex_range b v
  unfold finiteTaggedDecode
  rw [dif_pos hRange]
  congr 1
  apply (Fintype.equivFin V).injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  simp [finiteTaggedIndex]

/-- The physical Nat future pool includes EXACTLY the codes of V,
with no phantom coordinates between old and future. -/
noncomputable def finiteTaggedFuturePool
    {V : Type*} [Fintype V] (b : Nat) : Finset Nat := by
  classical
  exact (Finset.univ : Finset V).image (finiteTaggedIndex b)

/-- The actual tagged future pool is precisely [b,b+card V). -/
theorem finiteTaggedFuturePool_mem_iff
    {V : Type*} [Fintype V] (b z : Nat) :
    z ∈ finiteTaggedFuturePool (V := V) b ↔
      b ≤ z ∧ z < b + Fintype.card V := by
  classical
  unfold finiteTaggedFuturePool
  constructor
  · intro hz
    obtain ⟨v,_,hv⟩ := Finset.mem_image.mp hz
    rcases finiteTaggedIndex_range b v with ⟨hb,hvUpper⟩
    constructor <;> omega
  · rintro ⟨hb,hUpper⟩
    obtain ⟨v,hvz⟩ :=
      finiteTaggedIndex_surjective_interval (V := V) b z hb hUpper
    exact Finset.mem_image.mpr ⟨v,Finset.mem_univ _,hvz⟩

/-- Complete symmetric old/future graph L on Nat, using the literal
old original table E on [0,b), a finite future V table R and
typed old columns c in BOTH tuple orientations.

All out-of-target pairs are false; the full table is total. -/
noncomputable def finiteTaggedOldFutureEdge
    {d : Nat} {V : Type*} [Fintype V]
    (b : Nat)
    (E : Nat → Nat → Bool)
    (R : V → V → Bool)
    (sort : V → Fin d)
    (c : Nat → Fin d → Bool)
    (x y : Nat) : Bool :=
  if x < b then
    if y < b then E x y else
      match finiteTaggedDecode (V := V) b y with
      | some v => c x (sort v)
      | none => false
  else if y < b then
    match finiteTaggedDecode (V := V) b x with
    | some v => c y (sort v)
    | none => false
  else
    match finiteTaggedDecode (V := V) b x,
        finiteTaggedDecode (V := V) b y with
    | some v, some w => R v w
    | _, _ => false

/-- The entire old initial segment is literally unchanged, not
relabelled, embedded in some other original graph, or approximated
by a selected subpool. -/
theorem finiteTaggedEdge_old_old
    {d : Nat} {V : Type*} [Fintype V]
    (b : Nat) (E : Nat → Nat → Bool) (R : V → V → Bool)
    (sort : V → Fin d) (c : Nat → Fin d → Bool)
    (x y : Nat) (hx : x < b) (hy : y < b) :
    finiteTaggedOldFutureEdge b E R sort c x y = E x y := by
  simp [finiteTaggedOldFutureEdge,hx,hy]

/-- Exact ordered old-to-future L bit. This holds for positive
and missing original column bits alike. -/
theorem finiteTaggedEdge_old_future
    {d : Nat} {V : Type*} [Fintype V]
    (b : Nat) (E : Nat → Nat → Bool) (R : V → V → Bool)
    (sort : V → Fin d) (c : Nat → Fin d → Bool)
    (x : Nat) (v : V) (hx : x < b) :
    finiteTaggedOldFutureEdge b E R sort c x
      (finiteTaggedIndex b v) = c x (sort v) := by
  have hge : ¬ finiteTaggedIndex b v < b := by
    have h := finiteTaggedIndex_range b v
    omega
  simp [finiteTaggedOldFutureEdge,hx,hge,finiteTaggedDecode_index]

/-- Exact reverse future-to-old L bit, separately checked. -/
theorem finiteTaggedEdge_future_old
    {d : Nat} {V : Type*} [Fintype V]
    (b : Nat) (E : Nat → Nat → Bool) (R : V → V → Bool)
    (sort : V → Fin d) (c : Nat → Fin d → Bool)
    (x : Nat) (v : V) (hx : x < b) :
    finiteTaggedOldFutureEdge b E R sort c
      (finiteTaggedIndex b v) x = c x (sort v) := by
  have hge : ¬ finiteTaggedIndex b v < b := by
    have h := finiteTaggedIndex_range b v
    omega
  simp [finiteTaggedOldFutureEdge,hx,hge,finiteTaggedDecode_index]

/-- All future-to-future L bits are copied exactly from the given
finite tagged graph R, including cross-component nonedges. -/
theorem finiteTaggedEdge_future_future
    {d : Nat} {V : Type*} [Fintype V]
    (b : Nat) (E : Nat → Nat → Bool) (R : V → V → Bool)
    (sort : V → Fin d) (c : Nat → Fin d → Bool)
    (v w : V) :
    finiteTaggedOldFutureEdge b E R sort c
      (finiteTaggedIndex b v) (finiteTaggedIndex b w) =
        R v w := by
  have hv : ¬ finiteTaggedIndex b v < b := by
    have h := finiteTaggedIndex_range b v
    omega
  have hw : ¬ finiteTaggedIndex b w < b := by
    have h := finiteTaggedIndex_range b w
    omega
  simp [finiteTaggedOldFutureEdge,hv,hw,finiteTaggedDecode_index]

/-- The total glued Boolean table is symmetric when the old and
future tables are symmetric. Typed crossings are symmetric by
definition, and unspecified coordinates remain isolated. -/
theorem finiteTaggedEdge_symmetric
    {d : Nat} {V : Type*} [Fintype V]
    (b : Nat) (E : Nat → Nat → Bool) (R : V → V → Bool)
    (sort : V → Fin d) (c : Nat → Fin d → Bool)
    (hE : ∀ x y, x < b → y < b → E x y = E y x)
    (hR : ∀ v w, R v w = R w v)
    (x y : Nat) :
    finiteTaggedOldFutureEdge b E R sort c x y =
      finiteTaggedOldFutureEdge b E R sort c y x := by
  by_cases hx : x < b
  · by_cases hy : y < b
    · simpa [finiteTaggedOldFutureEdge,hx,hy] using hE x y hx hy
    · simp [finiteTaggedOldFutureEdge,hx,hy]
  · by_cases hy : y < b
    · simp [finiteTaggedOldFutureEdge,hx,hy]
    · cases hdx : finiteTaggedDecode (V := V) b x <;>
        cases hdy : finiteTaggedDecode (V := V) b y <;>
        simp [finiteTaggedOldFutureEdge,hx,hy,hdx,hdy,hR]

/-- No loop is introduced on old, future, or out-of-range Nat names. -/
theorem finiteTaggedEdge_irreflexive
    {d : Nat} {V : Type*} [Fintype V]
    (b : Nat) (E : Nat → Nat → Bool) (R : V → V → Bool)
    (sort : V → Fin d) (c : Nat → Fin d → Bool)
    (hE : ∀ x, x < b → E x x = false)
    (hR : ∀ v, R v v = false)
    (x : Nat) :
    finiteTaggedOldFutureEdge b E R sort c x x = false := by
  by_cases hx : x < b
  · simpa [finiteTaggedOldFutureEdge,hx] using hE x hx
  · cases hdx : finiteTaggedDecode (V := V) b x with
    | none => simp [finiteTaggedOldFutureEdge,hx,hdx]
    | some v => simpa [finiteTaggedOldFutureEdge,hx,hdx] using hR v

/-- A TOTAL sort map on Nat, with arbitrary out-of-range default,
is available when the future sort set has at least one element.
The decoder itself needs no such positivity assumption. -/
noncomputable def finiteTaggedFutureSort
    {d : Nat} {V : Type*} [Fintype V]
    (hd : 0 < d) (sort : V → Fin d)
    (b x : Nat) : Fin d :=
  match finiteTaggedDecode (V := V) b x with
  | some v => sort v
  | none => ⟨0,hd⟩

/-- The numbered future sort is exact at every code. -/
theorem finiteTaggedFutureSort_index
    {d : Nat} {V : Type*} [Fintype V]
    (hd : 0 < d) (sort : V → Fin d)
    (b : Nat) (v : V) :
    finiteTaggedFutureSort hd sort b (finiteTaggedIndex b v) =
      sort v := by
  simp [finiteTaggedFutureSort,finiteTaggedDecode_index]

#print axioms Kk.finiteTaggedIndex_range
#print axioms Kk.finiteTaggedIndex_injective
#print axioms Kk.finiteTaggedIndex_surjective_interval
#print axioms Kk.finiteTaggedDecode_index
#print axioms Kk.finiteTaggedFuturePool_mem_iff
#print axioms Kk.finiteTaggedEdge_old_old
#print axioms Kk.finiteTaggedEdge_old_future
#print axioms Kk.finiteTaggedEdge_future_old
#print axioms Kk.finiteTaggedEdge_future_future
#print axioms Kk.finiteTaggedEdge_symmetric
#print axioms Kk.finiteTaggedEdge_irreflexive
#print axioms Kk.finiteTaggedFutureSort_index

end Kk
