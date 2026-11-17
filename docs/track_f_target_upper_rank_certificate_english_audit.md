# Track F — transported old-neighbour clique forces target rank ≤ source rank

17 November 2026. English proof and adversarial audit BEFORE Lean.
This isolates the other half of target singleton-rank comparison
in the manuscript's non-root transport lemma. No diary
characterization or global BRD result is used.

## Setting

Let Esrc and Etgt be actual ordinary graph edge tables,
ell a finite clique threshold, and e:Nat→Nat an injective
INDUCED embedding of the directed graph tables:
Esrc(a,b)=Etgt(e(a),e(b)) for distinct a,b.

Let u be a source finite Henson one-type and v a target
finite Henson one-type, both with threshold ell.
Assume the target prefix level v.level is LARGER than
e(c) for every old source neighbour c∈u.neighbours.

Suppose x is a genuine source coding node extending u
with e(x.level)≥v.level whose target column matches the
target type v exactly on every earlier coordinate
(i.e. x∈sourceCodingFibre Etgt e v).

## Exact old-neighbour transport

Every c∈u.neighbours lies below u.level≤x.level and is
still a POSITIVE neighbour in x's complete source
coding type by the full chronological extension relation.
Because x is an ACTUAL coding node, Esrc(c,x.level)=true.
Inducedness gives Etgt(e(c), e(x.level))=true.
As e(c)<v.level, the definition of sourceCodingFibre says
that bit equals decide(e(c)∈v.neighbours). Hence

    e[u.neighbours] ⊆ v.neighbours.

This uses the exact source/target adjacency tables,
NOT an abstract rank/age assumption. The image map e
is injective and preserves ALL off-diagonal edges,
so the already verified finite clique-capacity
embedding theorem implies

    cap_Etgt(e[u.neighbours]) = cap_Esrc(u.neighbours).

Capacity monotonicity under subset inclusion gives

    cap_Esrc(u.neighbours) ≤ cap_Etgt(v.neighbours),

and by the exact one-type rank definition

    rank_target(v) ≤ rank_source(u).

The same inequality holds as soon as sourceCodingFibre
Etgt e v is rank_source(u)-large above u, since the
verified Large.has_member lemma produces a genuine
source coding witness x extending u.

## Crucial direction

This is rank_target ≤ rank_source from transported
OLD source clique certificates. The previously
verified future-clique lemma #275 forces the opposite
inequality rank_target ≥ rank_source, but only after
one proves a genuine source clique of the required
size exists IN the selected large fibre.

Thus equality can be reduced cleanly to the one-source
clique-richness lemma rather than being assumed.

## Hostile checks

1. H must lie after the image of EVERY old positive source
   neighbour, not merely above the original source index.
   The enumeration embedding need not be monotone.
2. Inducedness matters: injectivity alone does NOT
   preserve old source cliques.
3. Source coding nodes are ACTUAL originals with
   exact positive and negative columns; a hypothetical
   finite type would not supply Esrc(c,x.level)=true.
4. The target fibre must guarantee both that e(x.level)
   lies beyond H and that all target-prefix bits match.
5. e[c] is a finite image and e is injective, so
   its clique capacity is exactly the original one,
   not merely an upper/lower approximation.
6. Only old positive neighbours are transported;
   no claim that e maps the whole initial source
   segment below H is made.
7. The result is meaningful for any ell and any
   graph edge tables admitting the displayed
   consistent source/target finite types; normalized
   Henson avoidance is NOT used by the lemma itself.
8. A nonempty selected fibre suffices for this inequality,
   while the reverse inequality needs genuine CLIQUE
   richness, not just nonemptiness or largeness alone.
9. Mixed all-sort graph-age compatibility and diary
   history persistence remain separate open tasks.

## Lean endpoints

Prove (a) source old-neighbour image inclusion in the target
prefix from a genuine coding witness, (b) the source/target
rank upper bound via existing finite-clique capacity transport,
and (c) the same bound from an already rank-large source
coding fibre. Require a dedicated exact-head Lean build and
named standard-only axiom reports, with no new global
BRD manuscript validation marks.