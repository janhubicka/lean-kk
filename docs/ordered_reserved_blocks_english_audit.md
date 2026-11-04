# English-first proof and adversarial audit: ordered isolated reserved blocks

**Stage:** English proof and hostile review written before Lean implementation (4 November 2026).

## Mathematical statement

Fix `ell >= 2`, a symmetric loop-free countable edge table `E : Nat -> Nat -> Bool`
which avoids the normalized Henson forbidden family, and the **additional**
complete-column `OnePointLeftDense E ell` property. For any starting cut `base`
and any *finite ordered list* of sizes `[r_0,...,r_(m-1)]` with every
`r_i < ell`, there is an equally long list of finite sets of **actual
original Henson indices** `[S_0,...,S_(m-1)]` such that:

1. `|S_i|=r_i`; every index lies at or beyond `base`;
2. each `S_i` is a directed clique in the original table `E`;
3. each chosen `y in S_i` has **both** old adjacency bits zero
   against every earlier `x<y` outside `S_i` (including gap indices);
4. for `i<j`, `x in S_i` and `y in S_j`, we have `x<y` and
   `E(x,y)=E(y,x)=false`.

The result uses the original `E` throughout. It does not replace the
fixed Henson graph with a newly edited finite graph.

## Proof in ordinary mathematical language

Induct on the length of the size list. The empty list is immediate.

For a nonempty list `r::tail`, the verified theorem
`henson_leftDense_exists_reserved_originals` chooses a finite clique
`S` of size `r` above `base`; its theorem statement proves the
complete **earlier-outsider isolation** condition in both orientations.

Let `nextBase := max(base, 1 + max(S))`, with `max(empty)=0`. Thus
`base <= nextBase` and every `x in S` lies strictly below
`nextBase`. Apply the induction hypothesis to the remaining size
list starting at `nextBase`. It gives tail blocks `T`, all of whose
elements lie at or above `nextBase`, satisfying their own clique,
isolation, and pairwise separation properties.

For every `x in S`, `y in T`, we have `x < nextBase <= y`.
Moreover, `x notin T`, because every element of `T` is at least
`nextBase`. The **later block's** isolation condition at `y`
now yields `E(x,y)=E(y,x)=false`. This proves the new head-to-tail
pairwise condition; all tail-to-tail conditions follow from induction.
The sizes, clique status, and isolation properties are inherited
unchanged, completing the proof.

## Adversarial audit: what could make this statement false?

**A. Left density is an essential independent hypothesis.** Age avoidance
alone does not imply that a **specified enumeration** contains vertices
with complete prescribed passing columns and zero intervening bits.
The existing `emptyGraph_not_smallCliqueLeftDense` regression prevents
this inference. We assume the exact `OnePointLeftDense` statement and do
not pretend to construct the required enumeration in Lean.

**B. Strict size bound for subsequent selected adjacency.**
For reservation alone `r<ell` is sufficient. If a later selected
vertex must connect positively to *all* `r` members, `r=ell-1`
creates a forbidden `K_ell` with the selected vertex. The
stronger `r<ell-1` bound is needed for that application.
For example, in a `K_4`-free graph a reserved triangle is legal;
adding a vertex adjacent to all three is not.

**C. Gaps are not fully isolated.** A reserved original is forced
nonadjacent to earlier **outsiders**, not to every later outsider.
The proof of cross-block nonadjacency therefore invokes the later
block's isolation; it never assumes the earlier block controls later
gap bits.

**D. Every direction matters.** The original table is Boolean directed
at the interface, so the theorem records both `E(x,y)=false` and
`E(y,x)=false`. Relying only on one would not establish the complete
normalized undirected graph language without an additional symmetry
argument.

**E. Empty blocks.** Size zero is permitted; `S=empty` has no
members, and the next cut advances harmlessly. Multiple empty blocks
may be the same set without invalidating indexed pairwise separation
(vacuously true). The theorem must not assert pairwise *distinct* sets.

**F. Finiteness.** The induction treats a finite list. It gives no
uniform global choice for an infinite diary schedule or a proof that
each future selected extension is legal.

**G. No B3 conclusion.** Cross-block nonedges of **actual original
vertices** do not imply equality of full parameter-closed Algorithm 5.4
B3 records, nor that witnesses using arbitrary future upper
L-types behave like reserved original vertices. The numerical-H
K4 cut-10/cut-22 counterexample remains fully valid.

**H. Missing finite test.** The next selected vertex still has to
pass the **pure-unreserved** checker and **each actual interaction-pool**
checker from `finiteNeighbourCliqueCheck_false_iff_exact_mixing_pools`.
This result supplies the cross-block nonedge geometry, not those
negative Boolean certificate values.

## Formalization contract

Use a `List (Finset Nat)` in the returned theorem, a two-direction
`OrderedReservedBlockCrossNonedges` relation, and
`List.Pairwise OrderedReservedBlockCrossNonedges`. Keep
the exact original-index isolation property on every block, and
check named transitive axioms in the same strict whitelist as
`scripts/check_axiom_report.py`.

Only after the Lean implementation passes its build and exact axiom
audit may the olive manuscript mention this as a verified ingredient.
The bounded resolved copy, common labelled orbit, unconditional upper
and lower bounds remain pending.
