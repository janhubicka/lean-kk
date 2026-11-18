# Track F — compose private rank-zero descendants with genuine finite graph realization

18 November 2026. English proof and adversarial scope audit committed BEFORE Lean.

## Statement

In a genuine source Henson one-type preorder, fix a common old source prefix m,
finite actual source types u_a at level m (a∈Fin d), and sets S_a of ACTUAL
source coding nodes. Assume S_a is recursively rank(u_a)-large above u_a.
Let B be any finite symmetric graph on [0,N), with parent source labels σ.
Assume every nonempty directed B-clique C obeys its actual old SOURCE raw
clique capacity bound:

   |C| ≤ trackFCommonRawAge(d,ell,m,E,oldU,σ[C]), oldU_a=u_a.neighbours.

Then there is a strictly increasing original-index map f on [0,N), whose
image is an induced copy of B in the actual original source edge relation E,
such that for all a<N:

* a genuine actual coding type t_a∈S_(σ a) has level f(a);
* f(a)≥m;
* for every p<m the exact source bit E(p,f(a)) equals
  decide(p∈u_(σ a).neighbours).

No target prefix, compatible tuple profile, or diary theorem is assumed.

## Reduction to private sorts

Set D=Fin(N+1), with one unused dummy private sort to make all Nat-labelled
sort maps total for N=0 as well. Define parent π(i)=σ(i.val). Define private
τ(a)=the residue a mod (N+1) interpreted in D. On the selected interval a<N,
τ(a) has value a, so τ is injective and π(τ(a))=σ(a).
For each private i, take source root vRoot_i=u_(π i) and coding-node set
S'_i=S_(π i). These are legitimate possibly repeated rank-large requests.

Merged theorem HensonOneType.rank_large_private_rank_zero_common_front
(PR #358) gives a common level H, private roots v_i with

  vRoot_i ≤ v_i, rank(v_i)=0, Large(rank,S'_i,0,v_i),

and globally pairwise-disjoint positive marker sets

  M_i = v_i.neighbours \ vRoot_i.neighbours.

Since the original vRoot_i all have level m, a true finite-type extension
preserves both positive and negative membership below m. Consequently

  m≤H, M_i ⊆ [m,H),
  v_i.neighbours = vRoot_i.neighbours ∪ M_i.

The last identity is set-theoretic, not a hypothesis about an invented
future coding vertex; it follows by subset inclusion on genuine finite
neighbour sets.

## Raw-age feasibility of every requested B-clique

Define physical old and new raw ages from E, oldU, and v_i.neighbours.
For any private support T containing two distinct private sorts, the
already-merged physical disjoint-marker collapse (#259) gives

  rawNew(T)=rawOld(π[T]).

For a singleton {i}, v_i.safe states that the maximum actual directed
old-neighbour clique has size STRICTLY LESS than ell−1. Hence its raw bound
ell−1−cap is at least 1 (and rank zero in fact forces equality to 1, but
equality is unnecessary).

The one-theorem pure all-clique bridge (PR #362) applies with τ and π.
It proves for EVERY nonempty directed B-clique C:

  |C| ≤ rawNew(τ[C]).

This does not assume B itself is a clique or make a claim about redundant
mixed canonical values. The duplicate-parent case is handled correctly:
two B vertices with the same parent still have two distinct private sorts.

## Select actual coding originals

Apply verified trackFRankZero_realizes_all_feasible_sorted_graph (#355)
to the private source roots v_i and sets S'_i at common H, using the
feasibility just proved. Its conclusions give the strictly increasing
source f, every edge AND nonedge of B, actual coding membership
t_a∈S'_(τ a)=S_(σ a), and exact old-source columns relative to H.

Because u_(σ a) ≤ v_(τ a), the complete old bit agreement holds for
every original p<m. Thus the H-column statement restricts to the
original m-column, as required. Since m≤H≤f(a), all chosen originals
lie beyond the original front. There is no chronology assumption on
an entirely separate source-to-target embedding.

## Adversarial audit

1. A positive-rank large fibre need not itself be dense; only the private
   rank-zero descendants are passed to #355.
2. Even if B is large and many vertices use the same parent sort, the
   family of private requests is finite and all marker sets stay disjoint.
3. The extra dummy sort is unused by selected vertices; its rank-zero
   extension is harmless and avoids an invalid Nat→Fin 0 map when N=0.
4. The old roots must share the SAME level m for the disjoint-marker
   raw-age collapse to use a common physical old pool.
5. Every marker is at least m and below H, not merely absent from other
   new-marker sets; otherwise mixed supports could gain old coordinates.
6. No claim that individual refined raw bounds equal their original
   singleton bounds; only singleton positivity is used.
7. Mixed collapse works when the parent image π[T] is a SINGLE sort,
   including two private copies of the same parent.
8. Every clique subgraph of B is tested. The full B is not assumed clique.
9. Old graph E must be the same in the raw capacity theorem and actual
   coding-node realization theorem.
10. Each coding type produced by #355 genuinely belongs to the ORIGINAL
    target-free source set S_(σ a), not to a proxy local coding fibre.
11. The source map f is strictly increasing only on [0,N); no assumption
    on its values at irrelevant later Nat indices is needed.
12. The final theorem proves finite SOURCE richness, not mixed-target
    type synchronization, diary persistence, all self-copy unavoidability,
    or the exact Big Ramsey degree/24-orbit theorem.

## Formalization acceptance

Import the private-sort transfer, PR #358 actual common-front descendants,
PR #259 raw disjoint-marker collapse, and PR #355 finite rank-zero graph
realization. Prove old-neighbour set inclusion and the finite fresh marker
location by full-prefix agreement. Construct the actual raw-age singleton
positivity and multi-support equality. Derive global private graph clique
feasibility and invoke #355. Run a strict named transitive axiom gate
(standard axioms only) and a full Lean build, then adversarially inspect
the final statement for any extra hypotheses.

The black manuscript text is frozen. This proof may justify later simplifying
the OLIVE richness induction, but its validation mark must not be used
for the target-side or final lower-BRD statement.
