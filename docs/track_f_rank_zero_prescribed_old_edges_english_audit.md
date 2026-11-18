# Track F — a dense actual coding fibre realizes one prescribed finite old adjacency pattern

18 November 2026. **English proof and adversarial audit committed BEFORE Lean.** This is the single-vertex base step of the still-pending joint multi-sort richness proof, not an assumed diary/BRD characterization.

## Genuine chronological type data

Fix ell≥2, actual source ordinary graph edge table E, a consistent finite Henson one-type u=(m,U) of zero-based rank0 (manuscript singleton rank1), and a set S of ACTUAL coding nodes which is rank0-Large (DENSE) above u. Every s∈S must satisfy the complete actual old-column predicate IsCodingNode s in BOTH directed orientations.

Let front≥m be a finite later source cutoff. Let P be a finite set of already chosen ACTUAL original vertices, all with indices in [m,front). Let Q⊆P be the subset which the next new vertex should see positively. Its old positive-neighbour set is T=U∪Q. Assume the TRUE finite K_(ell-1)-free test `finitePoolCliqueCheck E (ell-1) T=false`. This is exactly the graph-age consistency condition, not a numerical clique-cardinality shortcut.

## Statement

There is an ACTUAL coding type x∈S extending u, with x.level≥front and rank(x)=0, such that for EVERY p∈P, both E(p,x.level) and E(x.level,p) equal `decide(p∈Q)`. Hence one can prescribe ALL positive and negative edges to any previously chosen finite set while staying inside the dense source fibre, whenever the actual one-point neighbourhood T is safe.

## Proof

Form the hypothetical consistent type t=(front,T), where T=U∪Q. It is a legal finite Henson one-type by the explicit true `finitePoolCliqueCheck` hypothesis; every old neighbour lies below front since U lies below m≤front and Q⊆P⊆[m,front).

The source node u is a full chronological prefix of t, not just a positive-neighbour subset: below m, U's bits are unchanged because Q has NO coordinates below m. This includes negative old bits.

By rank0 largeness (density) of S at u, the extension t has an extension x≥t belonging to S. By the assumption on S, x is a genuine ACTUAL original coding type of its own index x.level. Thus x.level≥front. Since u≤x and rank(u)=0, rank antitonicity gives rank(x)=0.

For each p∈P, p<front≤x.level. Prefix agreement x≥t forces x's bit at p to be 1 exactly when p∈T, which is equivalent to p∈Q because p≥m and U⊆[0,m). The ACTUAL complete directed coding-column predicate identifies these bits with both E(p,x.level) and E(x.level,p). This proves the assertion.

## How this connects to full richness

When embedding a finite sorted graph B vertex by vertex into several rank0-Large coding fibres, at each step choose P to be the previously selected coding original indices and Q those prescribed to be adjacent to the new B vertex. This lemma handles the density/actual-coding step. The remaining work is a FINITE GLUING SAFETY INVARIANT: derive K_(ell-1)-freeness of U∪Q from K_ell-freeness of the original old-prefix gluing of B, using the already chosen vertices' exact columns. The new lemma deliberately takes that safety test explicitly and does not assert it follows from mere abstract rank largeness.

## Hostile checks

1. Q must be included in P; a prescribed positive index absent from the old finite history invalidates the intended adjacency statement.
2. Every p∈P must lie AFTER the entire source root prefix m and BEFORE front. Otherwise a desired positive bit could alter the frozen old source type or be unconstrained when selecting x.
3. T=U∪Q must pass the true K_(ell-1)-free test; mere cardinality bounds on Q do NOT ensure the one-point type is safe.
4. The chosen x is an ACTUAL coding original from S, not an arbitrary hypothetical type. Only IsCodingNode connects type bits to genuine graph edges.
5. Density is applied to t and works without an extra OnePointLeftDense assumption. If S is only rank-positive-large and not dense, the statement may fail without a rank drop.
6. Both positive and negative edges to P are prescribed; the chronological extension order preserves both bits below front.
7. The actual coding original x may have further positive neighbours between front and x.level; these are NOT claimed absent, and future steps must zero-pad through such gaps.
8. Rank zero of x follows by antitonicity and nonnegativity, not by assuming every descendant of a rank0 node has identical old neighbour set.
9. This is ONE actual source coding vertex with an externally supplied finite consistency certificate. Arbitrary finite multi-sort richness remains pending.
10. There is no target embedding e, diary statement, BRD lower bound, or new Henson universality assumption in this theorem.

## Lean acceptance

Define the safe hypothetical extension t, prove complete chronological root-prefix agreement and use the verified rank0 density to select a GENUINE coding x. Check actual bidirectional adjacency to P and rank(x)=0. Require an exact-head Lean build and strict named transitive-axiom report. Annotate only olive proof and keep full multi-sort richness / diary BRD marks pending.