# Track F: exact one-coordinate isolation on genuine Henson common-neighbour profiles

15 November 2026. **English proof and hostile review committed before the Lean file.** Independent of the published diary characterization and the small-count recurrence.

## Genuine finite sorted old-neighbourhood data

Fix the ordinary graph adjacency table `E: Nat -> Nat -> Bool`, an old prefix `[0,m)`, a finite set of sorts `D = Fin d`, and for each sort `i` a finite old-neighbourhood set `U_i subset [0,m)`. On every nonempty support `S subset D` the original *raw* clique-capacity obstruction is determined by

`C_m(U,S)={x<m : for every i in S, x in U_i}`,

and its raw age bound is `ell-1-cap_E(C_m(U,S))`. Here `cap_E` is the actual maximum size of a directed old clique, not a selected diary age or an arbitrary user-specified number.

Suppose an actual later original `v >= m` is selected, and each sort is extended through all intervening indices by 0. Only one sort `j` receives 1 at `v`. Thus `U'_j=U_j union {v}`, while `U'_i=U_i` for `i != j`, now considered over the larger prefix `v+1`.

## Exact isolation lemma

1. **Support with another sort:** If some `i in S` differs from `j`, then `C_(v+1)(U',S)=C_m(U,S)` exactly. Proof: a vertex in the new intersection must lie in old `U_i subset [0,m)`, hence cannot be `v` or a gap index. Below `m`, adding `v` to `U_j` does not change membership. Both inclusions follow pointwise. Therefore the raw bound is unchanged for *every* such support, including triple and larger supports. No assumption about edges among the old vertices is needed for this equality.
2. **Selected singleton:** `C_m(U,{j})=U_j` and `C_(v+1)(U',{j})=U_j union {v}`. This follows from the old-prefix bound and the definition of the selected bit.
3. **One exact rank drop:** If `cap_E(U_j union {v})=cap_E(U_j)+1`, then on `{j}` the raw age bound decreases exactly one, provided `cap_E(U_j)+3<=ell`. Combining the preceding equality with the already verified actual physical rank-drop theorem in `TrackFRealHensonRankDrop.lean` yields an existential statement for a **genuine original v** under `OnePointLeftDense` and normalized forbidden-family avoidance.

The new graph-age class is therefore exactly the old class intersected with the single raw bound `w_j <= (ell-1-cap_E(U_j))-1`; this last identification uses the general raw-inequality/canonicalization theorem already present in the integer-clique formalization. The *canonical* capacity on mixed supports **can** decrease as a logical consequence of that singleton bound, even though the actual old common-neighbour raw bounds on mixed supports remain unchanged. Thus the correct claim is **raw locality**, not that the canonicalized mixed support values remain fixed.

## Hostile counterexample and assumption checks

- **Do not assert canonical mixed-age invariance.** Example `K_4`: if the old raw bounds on two sorts are `F({j})=2`, `F({i})=1`, `F({i,j})=3`, lowering singleton `j` to 1 forces the canonical joint capacity down from 3 to 2 despite the unchanged raw joint bound 3. One actual configuration has a singleton old neighbour for `j` and a disjoint old edge as the neighbour set of `i`, with no common neighbours. Raw bounds are invariant, but the canonicalized inequality system is a different object; its consequences must be recomputed.
- **Do not omit the requirement `S` contains another sort.** For `S={j}`, the new vertex belongs to the common pool, exactly as intended; for the empty support, the formal common-pool convention is the entire old prefix, which changes with the level, and the age is not defined on this support.
- **Do not silently allow nonzero bits at gaps.** If any other sort sees the new vertex or an intervening original, the mixed support pool can grow. The proof explicitly sets those bits to 0.
- **Directed adjacency matters only when computing clique capacity.** The intersection identity is a pure finite-set statement. The actual rank drop must use both edge orientations and the complete old neighbourhood certificate in the separate physical theorem.
- **No merging of two existing coordinates.** The index `j` stays in the active front during this rank drop; splitting/coding are distinct operations.
- **The theorem is local at one original.** It does not prove synchronized extensions of several source/target types, arbitrary induced Henson embedding transport, or the lower BRD colouring.

## Target formalization

Define `trackFCommonNeighbourPool m U S`, `trackFAddToOneSort U j v`, and `trackFCommonRawAge ell m U S`. Prove singleton-pool identities, exact preservation on any support containing a different sort, and the singleton drop under the real finite graph-capacity increment. Prove the existential physical Henson version using the now-merged real-rank-drop theorem, with explicit `OnePointLeftDense` and forbidden-family hypotheses.

The English proof deliberately keeps finite sorted graph ages and their canonicalization distinct. Green validation may be assigned only to exact Lean declarations which compile and pass the transitive-axiom gate; the multi-sort richness lemma and direct degree theorem remain pending.
