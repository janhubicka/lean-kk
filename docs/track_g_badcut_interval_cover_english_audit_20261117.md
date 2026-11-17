# Track G — cover all intrinsic bad cuts by terminals or single-node crossing frontiers

**17 November 2026. English proof and adversarial audit committed BEFORE the Lean module.**

## Exact verified source ingredients

- Merged G278 `Kk.TrackGBadCutNovelNodeWitness`: each intrinsic Kpt physical bad cut has an actual source node z∈Znew(c)\Zold(c), either terminal at c or realizing the complete dependent same-node old/upper L+ pair p absent from Zold(c).
- Merged G294 `Kk.TrackGCrossingFrontier`: for TWO genuine Kpt AlgorithmRuns in the same normalized tree, `kpt_actual_node_crossing_novel` is order-convex **for any fixed physical node z**, where `Covered_z(c)` means existence of an old pre-cut node w sharing z's actual upper Kpt ancestor at c+1.
- E55's `kptPhysicalBadCuts` is intrinsic and finite for a particular actual pair of source families.

All these components have independently passing direct strict named transitive-axiom gates. This note proves a missing *logical bridge*, not a new physical construction.

## Lemma 1 — missing full pair implies absence of upper-ancestor cover

Fix a real OLD AlgorithmRun Rold and its full pre-cut source
`Zold(c) = closure_(Rold.I(c+1))(X)`.
Fix z with `lev(z)>c`, and a *real* full old/upper pair
`p=(T,U)` of the **same z**:
`(c,T)=ancestor_c(z).val`, `(c+1,U)=ancestor_(c+1)(z).val`.
Assume `p∉FullPhysicalClosureCrossing(Zold(c),c)`.

Then `¬ kpt_actual_run_node_upper_covered(Rold,z,c)`.

**Proof.** If Covered held, some old live w∈Zold(c) would have
`ancestor_(c+1)(w)=ancestor_(c+1)(z)` as actual admissible Kpt nodes.
By the newly kernel-checked G294 lower-ancestor restriction lemma,
`ancestor_c(w)=ancestor_c(z)`. Applying `Subtype.val` to these two
node equalities gives exactly the old and upper complete L+ atoms
`(c,T),(c+1,U)` for w. Thus the *same w* would witness
`p∈FullPhysicalClosureCrossing(Zold(c),c)`, contradiction.
There is no need for the ancestor node itself to belong to the old closure;
the existential w is the genuine physical source witness.

If z also belongs to the NEW pre-cut source, then it satisfies
`kpt_actual_node_crossing_novel` at c.

## Lemma 2 — actual BAD cut has terminal or one-node interval witness

Let Rold,Rnew be two genuine Kpt AlgorithmRuns (same normalized family,
possibly different tops), and take source families
`Zold(c) = closure_(Rold.I(c+1))(X)`,
`Znew(c) = closure_(Rnew.I(c+1))(Y)`.
Assume `c ∈ kptPhysicalBadCuts family Rold.I oldTop Zold Znew`.

G278 yields c<oldTop, c∉Rold.I(c), and a genuine new-only
physical Kpt node z at that cut. If z is a level-c terminal,
we are in the first case. Otherwise it has an actual full pair
p missing from the old crossing relation. Lemma 1 shows
z belongs to the G294 single-node `NovelCross_z(c)` interval.
This is a covering of ALL actual bad cuts by terminal levels and
fixed-node crossing-novelty intervals; it does not require that the
bad cut was newly selected by Rnew, and does not assume Rold.X⊆Rnew.Y.

The corollary is a literal logical union statement:
```
Bad(Rold,Rnew) ⊆ TerminalDifference ∪
  ⋃_{z in actual Kpt nodes} NovelCrossingInterval(z).
```
The Lean theorem can express this via an existential z rather than
constructing an infinite union or choosing one global finite node set.

## Hostile non-implications

1. **Do not count bad cuts by the number of nodes or intervals.**
   Even ONE high z can have a crossing-novelty interval of arbitrary
   length. This is why G254 cardinal bounds with a diary-uniform
   finite Extra template remain conditional.
2. **Do not assert each bad-cut witness is a new ORIGINAL.**
   It may be a generated parameter/meet node, or a node absent from
   the OLD pre-cut closure but present in the OLD final closure.
3. **Do not assume source ancestry closure.** The old witness w in
   Lemma 1 must belong to the actual pre-cut closure; its ancestor
   need not be an element of that closure.
4. **Do not equate marginal old and upper type covers with a
   COMPLETE pair.** The same old source w must witness both types;
   I2 forks and auxiliary E bits are essential.
5. The conclusion is a covering by terminal witnesses and individual
   intervals; the overall Bad set need not be convex or a union of
   uniformly few intervals.
6. Intersecting any one interval with old-boring cuts can split it,
   and independently genuine I1/I2/I3/relative B3/monoid events
   can live along long intervals. No interval-interior collapse is
   currently proved.
7. The old and new AlgorithmRuns need not have nested seed sets
   for this logical covering, but they must be genuine runs in
   ONE normalized Kpt tree to invoke G294.
8. The cut-level constraint `c<oldTop` comes from E55 Bad
   membership, but `c<newTop` is NOT automatic. A correct theorem
   either includes `c<newTop` as an explicit premise or proves
   it from a genuine physical old/new height relation.
9. The G294 crossing-novelty definition is meaningful for any c
   as a set expression but its convexity theorem explicitly bounds
   c below BOTH scan tops and lev(z).
10. Do not infer the actual Kpt monoid map is unique from equality
    of full old/upper pair sets. Labelled assignments and parameter
    chronology are still needed for the common source orbit.
11. The K4 q2=22 / source 10, selected x=38 negative regression
    remains necessary in any microevent budget.
12. Full corrected-(B3)-loss vs relative continuation and the
    independently unavoidable infinite lower bound remain open.

## Verification gate

Implement the literal source-node implication and actual-bad-cut
bridge in a standalone Lean module importing G294 and G278;
explicit `#print axioms` of both public theorems with a dedicated
direct module build and negative parser self-test.

The result should be BLUE manuscript interface **only after**
exact-head success, never a global proof. The next *genuinely hard*
step remains a bound on the number of independent labelled interval
frontiers or a correct boring-interval monoid compression, derived
from an actual Henson resolved-copy recurrence instead of postulated.
