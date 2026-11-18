# Track F — realize an entire feasible finite sorted graph in rank-zero actual fibres

18 November 2026. **English proof and hostile audit committed before Lean.** This is STACKED on the exact finite labelled next-vertex theorem of PR #352, which itself derives local one-point old-neighbour safety from the TRUE global source raw clique inequalities and uses the verified real coding-vertex density of PR #345.

## Precise source data

Fix a finite family of genuine source Henson one-types u_i, indexed by sorts i∈Fin d, all at one original source prefix level m, and each of ZERO-BASED rank 0 (manuscript singleton rank 1). For each sort i fix S_i, a 0-large/dense set of **ACTUAL** source coding nodes above u_i. The full source E edge table is the genuine original graph. No Henson left-density axiom is assumed in this conditional theorem, because S_i's density is already an explicit hypothesis.

Fix a finite requested labelled graph B on the abstract ordered vertex set [0,N). Its adjacency table B(a,b) is symmetric on different vertex indices, and σ(a)∈Fin d specifies the requested source sort.

Let U_i be the ACTUAL old neighbour set of u_i, with U_i⊆[0,m). Assume **global raw sorted clique feasibility**:

For every nonempty directed clique C⊆[0,N) in B,
  |C| ≤ ell−1−cap_E({p<m : p∈U_i for each i∈σ[C]}).

The raw old common-neighbour pool is EXACT, using the old ordinary graph E and maximum directed clique capacity. This is the B∈A(F) condition in the raw feasible-clique-vector form; canonicalized ages preserve its feasible labelled clique vectors by already verified results, but their numerical mixed bounds need not agree.

## Construction invariant after n abstract vertices

For n≤N maintain:
- a source original-index assignment f:Nat→Nat, injective on [0,n) and strictly chronological there (we can retain injectivity plus a common cutoff if easier);
- a current source cutoff front≥m, with m≤f(i)<front for every i<n;
- actual E(f(i),f(j))=B(i,j) for EVERY ordered pair of distinct i,j<n, so the already selected original vertices form a genuine induced copy of the B-prefix;
- an actual sort map sort:Nat→Fin d on selected originals, with sort(f(i))=σ(i);
- complete forward old-prefix column E(p,f(i))=decide(p∈U_{σ(i)}) for every p<m;
- an actual coding node t_i∈S_{σ(i)} with t_i.level=f(i), for every i<n.

The actual S_i-membership and old-column invariant ensure no abstract fictitious vertices are inserted.

## Empty prefix

For n=0 choose arbitrary dummy maps f and sort, front=m. All selected-vertex invariants are vacuous. A map σ:Nat→Fin d exists by assumption, so sort can be chosen constantly σ(0) without a nonempty-Fin-d axiom.

## Induction step n→n+1

Suppose n<N and the above state holds. Take the next sort j=σ(n). Restrict the GLOBAL B feasibility assumption to the first n+1 abstract vertices. The parent source type u_j has rank0 and S_j is 0-large/dense of actual coding nodes.

Use the already verified source next-point theorem #352:
- selected past original set P=f[[0,n));
- positive subset Q={f(i):i<n, B(i,n)=1};
- requested source cutoff front;
- exact old source columns and induced partial B embedding from the state;
- local injectivity on the first n selected indices;
- global B raw clique feasibility on every T⊆[0,n+1);
- B(i,n)=B(n,i), from symmetry.

The resulting ACTUAL source coding node x∈S_j extends u_j, has x.level≥front, and satisfies:
1. E(p,x.level)=decide(p∈U_j) for every original old p<m;
2. E(f(i),x.level)=B(i,n), E(x.level,f(i))=B(n,i) for every i<n;
3. x has genuine source rank0 and exact old coding columns.

Define f'(n)=x.level, f'(i)=f(i) for i≠n; define new actual sort map sort'(x.level)=j and sort'(p)=sort(p) elsewhere; set front'=x.level+1.

Because every previously chosen f(i)<front≤x.level, x.level is distinct from all old source selected originals, and f' is injective on [0,n+1). All old edges, columns and coding witnesses are preserved, and the next edges are exactly the displayed two-column B conditions. Every selected f'(i) lies in [m,front'). The new t_n=x is an actual coding-node witness in S_j. This completes the induction step.

After N steps, restrict f to Fin N. It is an injective induced embedding of the FULL finite labelled graph B into the ACTUAL source ordinary graph, with each abstract vertex a mapped to a genuine original coding vertex belonging to S_{σ(a)} and extending its prescribed rank0 root source type.

## Adversarial checks

1. **No independent source sort map assumption in the final statement:** we construct and update sort at each new original; it is a bookkeeping map, not an extra graph relation. We must prove updating sort does not alter earlier labels because x is distinct from every old f(i).
2. **No spurious chronology:** f must be injective on the selected range and each new index later than every previous index. This follows from the maintained cutoff. Source-to-TARGET embedding ordering is never assumed anywhere.
3. **Both directed B edges:** the source E is Boolean directed in Lean; B symmetry and the actual coding-node full columns ensure E(f(i),x)=B(i,n) and E(x,f(i))=B(n,i), not just one orientation.
4. **No global graph universality axiom:** only explicit rank-zero largeness of the designated ACTUAL coding sets S_i, actual old neighbour columns, and genuine finite B raw clique feasibility are used. The source E may be arbitrary unless those hypotheses are satisfied.
5. **Global B feasibility must include ALL nonempty directed subcliques**, including partial neighbour cliques of each next vertex. Q itself need not be a clique.
6. **One common source old prefix level m:** all roots u_i must have the same level m and true source old neighbour sets U_i. This is not automatic from separately given arbitrary source types; manuscript's profile synchronization must arrange it before applying this theorem.
7. **Rank-zero only:** this is the bottom step of the richness induction, not a proof that any higher-rank S_i can realize B without rank-dropping via finite daughter fans and updating singleton capacities.
8. **Actual coding witnesses:** each selected point is a coding original x.level in S_i, not an arbitrary hypothetical finite type. This excludes a vacuous abstract-type realization.
9. **Preservation of old columns:** each new x has old E column U_j exactly, so the global source raw profile can be reused unchanged in the next step. Extra edges to unselected interval vertices do not affect the induction because future requested vertices are forced to give those intermediates zero bits at the relevant finite cutoff.
10. **No conflation with target compatibility:** selecting vertices in S_i=sourceCodingFibre(target_i) gives source vertices whose TARGET images share the assigned prefixes, but establishing their mixed target-profile equivalence and distinct target sort prefixes is a separate theorem.
11. **No diary degree count:** even a verified finite B realization does not establish that each chronological diary history is unavoidable in every induced Henson self-copy.
12. **No unproved canonical equality:** the theorem requires raw clique feasibility of B. A separate already verified canonicalization equivalence can translate from the manuscript's canonical graph-age presentation; do not assert raw numerical equality.

## Lean acceptance

Formalize a finite partial realized-history structure carrying f, sort, cutoff, inducedness, old columns and actual coding-witness membership. Prove an exact next-state extension theorem using the verified PR #352 third endpoint. Then iterate by Nat induction for n≤N, extract an injective finite induced copy with all source sort-specific coding membership. Check named theorem assumptions and transitive axioms in an exact-head hosted Lean gate. Do not modify frozen black manuscript or promote its full multi-sort richness marker: only rank-zero finite graph realization would be certified.

**Important stacking caveat:** PR #352's three-theorem exact-head gate must pass before this finite induction may be considered certified.