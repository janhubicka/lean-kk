# A genuine (K_4)-free raw numerical-H event invisible after canonicalization

17 November 2026. Independent adversarial counterexample; includes a
literal finite numerical-H model regression.

## Why this matters

The verified [Track A raw event theorem PR #284](https://github.com/janhubicka/lean-kk/pull/284)
characterizes every strict ordinary-L RAW support change. The merged
[canonical-visibility PR #319](https://github.com/janhubicka/lean-kk/pull/319)
correctly asks for a *globally feasible normalized clique-multiplicity vector*
that saturates the old changing raw bound. A raw event alone is **not**
sufficient for a change after integer-witness canonicalization, even when
the source graph is genuinely (K_4)-free and the two future vertices
are distinct.

## Explicit graph (seven ORIGINAL vertices)

Let (E) be the symmetric irreflexive graph on original names
({0,1,2,3,4,5,6}), with **exactly** the following eight edges:

- triangle on ({0,3,5}): (03,05,35);
- triangle on ({1,2,6}): (12,16,26);
- two further edges (45,46).

There are no other edges. This is (K_4)-free: the only triangles
are the displayed pair, and neither can extend to a fourth
common neighbour. In particular, (56) is a nonedge.

Use forbidden-clique parameter (ell=4), numerical-H height (k=4),
current original (b=4), and the **distinct** later top-original
names (j(0)=5), (j(1)=6). Compare the physical old numbered
cuts (g=0) and (g=1) before generations (0) and (1)
of original (4). The literal numerical-H position is

[
  iota_4(i,q)=2(5i+q),
]

so the old prefixes are ([0,40)) and ([0,42)), including
all odd dummy addresses. The new real coordinate is
(iota_4(4,0)=40); address (41) is an odd dummy.

For future support (U), the exact common-neighbour capacities
and RAW ages are:

| Support (U) | Earlier original common neighbours (P_U) | (omega_E(P_U)) | Raw at (g=0) | Raw at (g=1) |
|---|---|---:|---:|---:|
| ({0}) (top original 5) | ({0,3}) | 2 | 1 | 1 |
| ({1}) (top original 6) | ({1,2}) | 2 | 1 | 1 |
| ({0,1}) | (arnothing) | 0 | **3** | **2** |

At (g=0) the common old pool to *both* future sorts is empty;
at (g=1), the only new common real vertex is current-original
generation (0). It is adjacent to both later top originals
because (45,46) are genuine original edges. It cannot join
any earlier common clique at generation (0), and every odd
dummy has zero ordinary-L future crossing bits.

Thus the **joint raw support bound truly falls by one**.

## Canonical graph age does NOT change

A normalized clique-weight vector (w=(w_0,w_1)) has
(w_0+w_1leqell-1=3), and full OLD feasibility means

[
   w_0leq1,qquad w_1leq1,qquad w_0+w_1leq3.
]

Consequently the *entire* feasible vector family is

[
 {(0,0),(1,0),(0,1),(1,1)}.
]

The last inequality (w_0+w_1leq3) is already redundant.
Replacing it by the NEW raw bound (w_0+w_1leq2)
does not exclude any vector, and the canonical old ages
at both cuts are the SAME:

[
 C({0})=1,qquad C({1})=1,qquad C({0,1})=2.
]

There is **no old-feasible vector saturating the old raw
joint bound 3**: the two singleton bounds force its value
to be at most 2. This is the precise missing hypothesis
in the false assertion *every raw support event changes
the canonical age*.

## Verification and scope

The accompanying
`scripts/check_k4_raw_event_canonical_redundancy.py`
reconstructs all relevant numbered physical vertices using
the REAL numerical-H generation gate in both orientations,
checks (K_4)-freeness and the literal old common-neighbour
capacities at each cut, enumerates ALL normalized integer
clique vectors, and verifies the canonical ages and the
absence of any old-feasible saturating vector.

This example uses a fixed (K_4)-free original graph, height
(k=ell=4), and two distinct later tops: no repeated
future names or illegal source clique is involved.

It does not address auxiliary (K^{mathrm{pt}}) incidence,
full dependent (I1)--(I3)/(B3) events, the recursively
prescribed original schedule or the labelled orbit theorem.
In particular, a redundancy counterexample is **not** a
counterexample to the verified PR #319 criterion; it
demonstrates why that criterion is genuinely sharper.
