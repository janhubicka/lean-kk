# Finite universal typed-clique witness gadget for raw integer graph-age bounds

**11 November 2026. English construction and adversarial audit before Lean.**

## Statement and exact scope

Fix `ell ≥ 2`, a finite set of sorts `Fin d`, and an arbitrary raw bound
`B : IntegerGraphSupport d ell → Nat`, using the **existing** KK age type
`IntegerGraphSupport d ell = {T: Finset (Fin d) // T.Nonempty ∧ |T|≤ell−1}`.

Let `Weights(d,ell)` be the library's actual finite normalized `IntegerCliqueWeights d ell`, i.e. vectors `w : Fin d → Fin ell` with `∑_j w_j ≤ ell−1`. Define feasible vectors
[
 V_B={winoperatorname{Weights}(d,ell):
       orall Tinoperatorname{IntegerGraphSupport}(d,ell),       sum_{jin T}w_jle B(T)}.
]
This set is finite; the zero vector belongs to it.

The following explicitly constructed **finite ordinary graph L-gadget**
has a reserved base and a future pool W:

1. For every admissible support T create one reserved clique block Q_T with exactly
   [
   r_T=(ell-1)-B(T)
   ]
   vertices, using natural truncated subtraction. Different Q_T blocks are mutually nonadjacent. If B(T)≥ell−1, Q_T is empty.
2. For every feasible vector w∈V_B create one future component C_w, a complete clique with **exactly w_j distinguishable vertices of sort j** for each j. Different future components have no edges.
3. Connect every q∈Q_T to every v∈C_w in **both directions** exactly when `sort(v)∈T`. No other edges are present.

Then the entire finite graph is K_ell-free, and its future pool W has the exact witness property:
[
oxed{
igl{	ext{normalized sort-count vectors of future cliques }ssubseteq Wigr}
 = V_B.}
]
Every feasible vector occurs as the full component C_w. Every clique of W is contained in one component (or empty), so its counts are coordinatewise ≤w; since B gives nonnegative **upper** support bounds, all these subvectors are also feasible. Thus there is no spurious normalized witness. The zero vector is represented by the empty clique.

Consequently the maximum supported multiplicity of future cliques is
[
max_{ssubseteq W, s	ext{ clique}}sum_{jin T}#s_j
 =
max_{win V_B}sum_{jin T}w_j
 = (operatorname{integerGraphAgeCanonical}(d,ell,B))(T).
]
This is a concrete **finite ordinary-L realization** of the canonical integer graph-age function G_B; it does not require B itself already to be an age.

## K_ell-freeness proof

Let s be any nonempty clique in the entire gadget.

**No reserved vertices:** all vertices of s lie in one C_w, since distinct future components are mutually nonadjacent. Its cardinality is at most `∑_j w_j ≤ ell−1`.

**At least one reserved vertex:** s intersects a unique Q_T, since distinct reserved blocks are mutually nonadjacent. Its future vertices must be from at most one C_w, and all such vertices have sorts in T (by the exact support edge rule). Thus
[
|s|le r_T+sum_{jin T}w_j
 le (ell-1-B(T))+B(T)leell-1.
]
The final inequality is valid also when B(T)>ell−1 because truncated subtraction makes r_T=0; in that case Q_T is empty, so the “reserved vertex” case cannot arise at all. For a **nonempty** Q_T we have B(T)≤ell−2, and ordinary subtraction/addition gives exactly `r_T+B(T)=ell−1`.

Thus s cannot have ell vertices. The argument relies on **complete exact directional support columns** and cross-nonedges, not a magical K_ell-free assertion.

## The sharp obstruction for an infeasible vector

Suppose w is normalized but violates the raw bound at T:
(sum_{jin T}w_j>B(T)).
Since (sum_j w_jleell-1), we must have B(T)<ell−1; therefore r_T>0. If one nevertheless adds a complete component C_w with the same prescribed support edges, the union of Q_T and the T-vertices of C_w contains a clique of size
[
 r_T+sum_{jin T}w_jgeell.
]
Hence **exactly** the violating vectors are forbidden by the literal reserved-clique constraints. This also explains the cover gadget's raw bound (ell-1-a) when the reserved clique capacity is a.

## Independent executable hostile regression

A separate **all-pairs clique oracle** enumerated the vertices and every candidate ell-subset for sample values (ellin{2,3,4}), (din{1,2,3}). Across **465** bound systems (including bounds 0, ell−1 and values above ell−1), it found **no forbidden K_ell**, and the set of realized future sort-count vectors agreed **exactly** with V_B. As a negative control, **377** runs deliberately inserted a violating normalized vector component; the oracle then found a genuine forbidden ell-clique. There were zero discrepancies. Script: `test_universal_witness_gadget.py` in the local validation workspace. These computations are finite regression tests, **not Lean proofs**.

## Adversarial audit

1. **Empty future pool is not universal.** This construction deliberately changes W; it does not claim that an arbitrarily fixed W realizes all normalized vectors.
2. **Only feasible vectors are included.** Adding every normalized vector regardless of B generally creates forbidden mixed cliques (negative regression).
3. **Vector multiplicity:** C_w has w_j *distinct vertices* of sort j, not merely one vertex per occupied sort.
4. **Internal completeness:** all vertices in a single C_w form a clique. The full component must realize exactly w, not only a subvector.
5. **Cross-nonedges are essential:** separate witness components and reserved blocks must have no cross edges beyond the specified support columns.
6. **Both directions:** the numerical-H application needs exact forward and reverse L bits, even though an abstract symmetric undirected graph could suppress the distinction.
7. **Natural subtraction:** if B(T)>ell−1, r_T=0. Do NOT use `(ell−1−B(T))+B(T)=ell−1` without a `B(T)≤ell−1` condition.
8. **Empty Q_T:** B(T)≥ell−1 imposes no constraint because every normalized vector already has total≤ell−1.
9. **Zero vector:** it is always feasible and realized by the empty future clique; the construction must not drop that boundary.
10. **Nonfeasible witness obstruction:** if w violates a support bound, the T-count together with Q_T creates a clique of size≥ell; a specific ell-subclique exists.
11. **No old graph P yet:** the construction has only the reserved base. Adding a pre-existing graph P with nontrivial future-neighbourhood constraints requires *individual compatible extensions* and the preceding finite free-amalgamation theorem.
12. **No numerical-H+ identity yet:** the constructed formal reserved blocks are actual cliques in an abstract graph, not yet identified with full generations of numerical-H originals, their auxiliary E columns, or Kpt closure records.
13. **Age versus B3:** matching all ordinary L-only clique vectors gives the canonical graph age G_B, not equality of the full parameter-closed corrected-B3 source.
14. **Chronological realization:** embedding the finite graph into a Henson graph does not automatically produce the diary's prescribed enumeration, selected levels, E/free cuts and common labelled inverse source.

## Lean implementation plan

First define the *single* complete typed component for an actual normalized weight vector w:
`WitnessVertex w := Σ j:Fin d, Fin ((w.1 j).val)`. Prove its total size is exactly `∑_j w_j`, is below ell, and for **every** support T the number of vertices of sorts in T is exactly `integerCliqueOnSupport w T`. No age or Kpt theorem is needed for these arithmetic facts.

Next construct the finite disjoint union of all feasible components, using the merged four-endpoint finite free-amalgamation lemma for K_ell-free components, and prove both directions of feasible-vector realization. Finally attach the reserved support blocks with size r_T and the exact two-direction support columns, and prove the overall no-K_ell condition by clique classification.

The **numerical-H physical adapter** remains a separate theorem: replace abstract Q_T by actual reserved real-copy prefixes of the verified capacity, replace future components by genuine top selected originals, verify complete old/gap/future columns, and synchronize parameter E/AlgorithmRun records. Do not claim this already follows from the abstract gadget construction. No protected-black manuscript changes or unsupported green validation marks.
