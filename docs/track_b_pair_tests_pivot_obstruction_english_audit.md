# Track B: pair tests do not determine the age after a real pivot

## Status and exact scope

This is an English finite counterexample, independently checked before any
possible formalization. It is not currently a Lean-verified fixture. It shows
that a pairwise passing test together with the usual global clique-size cap
does not, by itself, preserve the old survivor age when the new original is a
real pivot with prescribed old neighbours. It does **not** assert a contradiction
to a proved Track F theorem: those theorems specify their raw update operator
and additional hypotheses explicitly. Nor does this note assert that the
example satisfies every condition of a valid manuscript diary.

## The seven-vertex old graph and its complete columns

Take ell=4 and old sorts s,a,b. The old prefix P=[0,7) consists of

- q=0, isolated in the old graph;
- a two-vertex clique {1,2} assigned only to sort s;
- a two-vertex clique {3,4} assigned only to sort a;
- a two-vertex clique {5,6} assigned only to sort b.

There are no edges between these four components. Every edge is symmetric,
and there are no loops. Set the old-to-future column of q to one on all three
sorts. Each of the other six originals has column one exactly on the sort
assigned to its two-vertex clique. All other old-to-future bits are zero.

For a singleton support {i}, its old common-neighbour pool is q together with
the corresponding two-vertex clique, so its clique capacity is 2. For any pair
or the triple of sorts, its common-neighbour pool is exactly {q}, of clique
capacity 1. Therefore the actual raw bounds B=3-capacity are

| Support | B |
| --- | ---: |
| {s}, {a}, {b} | 1 |
| {s,a}, {s,b}, {a,b} | 2 |
| {s,a,b} | 2 |

These bounds are already canonical. Each singleton value is attained by a
one-vertex vector. Each pair value is attained by one vertex of each of its
two sorts. Any of these two-vertex vectors also attains the triple value 2.
All these vectors respect every bound. Thus this is a genuine positive
integer graph age, not an arbitrary inconsistent table.

## The already chosen pivot and its two positive children

Choose the actual new original v=7 of old sort s. Its neighbours in P are
exactly q,1,2. This is the complete column prescribed by sort s. The graph on
P union {v} is K4-free: its largest clique is {1,2,v}, and q has no edges to
1 or 2. The other two old edges are separate components.

Retain future sorts a and b and prescribe the positive bit to v on both of
them. All old bits below 7 are retained. This is the explicit pointed column
with cutoff H=8, parent map selecting a,b, and beta constantly true.

The new common-neighbour pool for a is {q,v,3,4}. Its induced graph consists
of the two disjoint edges qv and 34. Its capacity remains 2, so its new raw
singleton bound is 1. The same holds for b, using the edge 56. Consequently
both positive children have legal one-vertex extensions.

The common-neighbour pool for {a,b}, however, is now {q,v}, an edge of
capacity 2. Its new raw bound is therefore 1, and its canonical bound is also
1: a singleton of either sort witnesses the lower bound. Thus the old
survivor pair capacity drops from 2 to 1 although both children separately
survive.

Equivalently, an edge xy between a new positive a-vertex and a new positive
b-vertex would complete the forbidden K4 on {q,v,x,y}. No choice of later
original indices removes this obstruction.

## Why the two proposed tests miss it

The old pivot singleton has F({s})=1. For each surviving sort i in {a,b},

    F({s,i}) = F({i}) + 1 = 2.

Thus both sorts satisfy the pairwise numerical passing test. Also, every
nonempty support U contained in X={a,b} satisfies

    F(U) <= ell-2 = 2.

The old age restricted to a,b is therefore unchanged by an *isolated* coding
raw operator which merely caps all X-supported capacities at ell-2. The real
pivot is not isolated from its old common neighbours: it is adjacent to q,
which is the old common witness for a and b. The actual pointed update must
account for that link.

The missing joint test is visible at the old triple:

    F({s,a,b}) = 2 < F({a,b}) + 1 = 3.

The feasible old a-b edge cannot be extended to a clique containing a vertex
of sort s. More generally, testing a real pointed successor requires checking
the entire positive clique vector after adjoining one vertex of the pivot's
old sort, including its normalization and all support inequalities. Pair
tests and a global ell-2 cap alone do not imply those joint inequalities.

## Independent audit

A second reviewer checked the exact old and new common pools, the attained
canonical values, K4-freeness of P union {v}, survival of both singleton
children, and the concrete K4 created by a positive a-b edge. The reviewer
agreed with the obstruction and with the limited scope stated above.

This note identifies an application obligation when relating an abstract
word-column coding operation to a real-original pivot. It does not downgrade
or contradict any existing Lean theorem with its stated premises.
