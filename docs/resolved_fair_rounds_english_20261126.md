# Constructing fair resolved-Q rounds from actual old columns
26 November 2026. English proof and adversarial review before implementation.

The previous exact-head focused and root builds of a55bb14 failed in
ResolvedLiveFutureAge (singleton filter simplification and malformed
tactic quotation). No axiom report of the new modules is certified.
The repairs replace the singleton filter by a literal singleton equality
and split the witness proof into explicit goals. Downstream elaboration
is still to be checked by CI.

## Occupied finite partition

Represent the fixed original vertex set on even natural names. At a
finite old pool P and nonempty live W, the actual class of v in W is
the complete Boolean column E(-,v) on P. Its occupied image is a
nonempty finite subtype of (P -> Bool). Reindex it by Fin d using a
finite equivalence. A total label map outside W is obtained by using
any occupied class. Define columns by the inverse equivalence.
Then the live-stage columns, exactness (class equality iff all old
bits agree), and occupancy are proved, not extra hypotheses.

## Parallel private-marker refinement

Given a finite occupied class labelling c and a Boolean test f on W,
call class i mixed if both f bits occur in it. Take a fresh odd name
q_i for every mixed class, using 2*(max P + i)+1. The marker set Q is
the image of the mixed labels. New markers are mutually nonadjacent,
nonadjacent to P, and q_i is adjacent exactly to the f-positive members
of class i in W. Keep every other old/live edge. If the positive part
of W has no triangle, the whole new live graph is K4-free: any clique
meeting Q contains just one marker and at most two positive vertices;
a clique avoiding Q is an old/live clique. Unused reserved names do
not become vertices.

After the whole batch, equality of complete columns is exactly
(c(v)=c(w) and f(v)=f(w)). Indeed old columns are preserved. If equal
old classes have different bits, that class is mixed and its marker
separates them. Conversely, equal old class and test bit give equal
columns on each marker. This is a genuine refinement.

This simultaneous construction can be read in any order of Q. Before
inserting q_i, all vertices in class i have zero columns to every
other inserted marker; hence their old columns are identical. Different
old classes still have different old columns. Both children of class i
are nonempty by mixedness. Thus q_i splits precisely one current class,
not multiple classes at once. The exact positive neighborhood is its
positive child. Store Q and this partial-prefix property as an actual
batch certificate, rather than assuming an unverified split schedule.

Use f(v) = (v=r) first. It has at most one positive vertex; the result
isolates r. Then relabel the actual occupied columns and use
f(v)=E(r,v). This positive set is triangle-free: a triangle there
together with r is a K4, using symmetry and absence of loops.
Relabel once more. Refinement cannot destroy singleton isolation,
and adjacency to r is now constant on each active class.

## Normalized round

Apply the actual finite saturated cover construction to the resulting
live stage with its occupied class labelling. It keeps the literal
old-plus-live graph, and each auxiliary block has constant class bits,
so the class equality invariant persists. Its terminal age is actual
future clique capacity. Move r into P, delete r from W, retain all
edges. The survivor class is a whole class, because r was isolated.
The fixed-target age-neutrality proof below is simpler than building
an arbitrary new survivor enumeration.

For every finite list of surviving terminal vertices (repetitions
permitted), pull back the old saturated class age. For each support U
of the terminal labels, choose an actual maximum clique C in W whose
classes belong to the image of U. The singleton coded class is not in
that image, so C avoids r. Choose, for each x in C, a label in U with
the same old class as x; the choice need not be injective. Every old
column of x agrees with that terminal, and the new r column agrees by
the second refinement. Thus C, with these labels, is a literal
continuation over P+r. Its normalized multiplicity vector witnesses
the old capacity on U in the new canonical age. Antitonicity provides
the reverse inequality. If there are zero terminal labels, the support
domain is empty and equality is immediate. This proves full reference
neutrality at coding, without claiming every permitted configuration
is realized. The no-split certificate follows directly from old-class
exactness and the adjacency refinement.

## Infinite union

Let W_n be the even names 2*m with m>=n. Initial old pool is empty;
take the prescribed graph on even names and zero unused edges.
At each n perform the finite round for r=2*n, using the fact
W_n is nonempty and has infinitely many spare odd names. The next
live set is W_(n+1)=W_n minus {2*n}. Classical choice selects
one actual round and its certificates. Old sets increase. Every
previous old or live name remains in the next old-or-live domain.
All edges between such names are preserved. Thus the actual
old domains exhaust all even names and a subset of the odd names.
On their union, define the final edge by the first stage containing
both vertices in its old domain (or zero for unused names).
Monotonicity and preservation make every such choice consistent.
Every finite clique is already contained in a single old stage;
hence final K4-freeness. The induced graph on even names is the
original graph. Auxiliary names need not be numerically ordered:
the next step is chronological enumeration of the recorded marker
batches, cover blocks and coding vertices, with an isolated dummy
between every meaningful name.

## Scope and hostile checks
- No total sort map into Fin 0 is required. Only a nonempty live W
  is labelled. Empty selected front uses the empty support type.
- Insert markers only on mixed classes; private markers are not a
  single global neighbor marker which could split several classes.
- Q is disjoint from all live and old vertices, including coded even
  vertices. The two marker passes use the new old pool for fresh names.
- No old/old, old/live or live/live edge changes during preparation.
- Saturation preserves all old classes: equality of all old columns
  both implies and is implied by equality of their previous labels.
- Singleton isolation must precede coding, not just adjacency
  refinement. The latter does not by itself isolate r.
- The target multiplicity assignment may repeat labels, and one
  witness clique is selected separately for each support.
- The global limit is over increasing actual old domains, not over all
  natural names of the temporary edge tables; unused odd names can
  remain isolated.
- Chronological relabelling, dummy insertion, event-record parser,
  global history occurrence and exact BRD endpoints remain separate.
- The implementation below is a proposed batch until kernel and axiom
  reports on its exact head succeed.
