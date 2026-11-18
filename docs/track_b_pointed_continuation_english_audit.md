# Track B: a constructed continuation around the same selected original

## Scope and status

This English argument is written before its new Lean formalization. It addresses
the ordinary graph part of the next-column gap left by
`UniformStageNonvacuousSortWitness.lean`. It does not identify the full
parameter-closed numerical-H source, prove corrected B3, prescribe an arbitrary
diary transition, or supply an infinite resolved copy.

The gain is that the next complete passing column is now defined, rather than
assumed, and its entire compatible finite future is constructed while fixing the
already selected original and any previously protected finite prefix.

## Data and explicit column

Let E be a fixed left-dense K_ell-free original graph, ell >= 2. Let P=[0,b),
let c(p,t) be complete old columns on d sorts, and let v>=b be an ALREADY
CHOSEN original of sort s: for every p<b, both E(p,v) and E(v,p) equal c(p,s).
Choose any H>v. In particular H may exceed every original in an existing finite
stage, so all of that stage can be kept fixed in the next realization.

Choose a finite new sort set, written Fin e, with e>0 for the physical tagged
realization, a parent map pi:Fin e -> Fin d,
and a bit map beta:Fin e -> Bool. Repeated parents are allowed. For a literal
binary split use the pairs (t,0),(t,1), after any fixed finite enumeration.
The new COMPLETE column is

    C(p,u) = c(p,pi(u))   if p<b,
             beta(u)     if p=v,
             0           otherwise.

The two first cases are disjoint because b<=v. Every actual original between b
and H other than v has an explicit zero column. Its old graph edges are retained.
In particular previous witnesses are fixed as graph vertices, but are not being
promised preservation as still-active future sorts.

## 1. Exact simultaneous successor bound

For a nonempty new support U with |U|<=ell-1, put S=pi[U] and

    N(S) = {p<b : c(p,t)=1 for every t in S},
    rho(S) = maximum clique size in E restricted to N(S).

These definitions make sense for EVERY finite S, including S union {s} when
that enlarged support has ell elements and is outside IntegerGraphSupport.

Claim: the exact common-old-neighbour capacity over the FULL prefix [0,H) is

    rho(S),                                  if some beta(u)=0 in U;
    max(rho(S), 1+rho(S union {s})),           if every beta(u)=1 in U.

Proof. An old p<b belongs to the common pool exactly when it belongs to N(S).
The selected v belongs exactly when all beta bits on U are one. Any other
p<H has C(p,u)=0 for any chosen u in the NONEMPTY U, so cannot belong.
Thus the actual common pool is N(S) or N(S) union {v}. In the second case a
clique either avoids v, or consists of v and a clique in N(S) whose vertices
are adjacent to v in BOTH directions. The exact old column of v identifies
that latter pool with N(S union {s}). Both maxima are attained in finite sets,
including the empty clique, so this is equality, not merely an upper bound.

Consequently the exact next raw age is ell-1 minus this quantity, with natural
truncated subtraction. No canonical-age transport across different sort
dimensions is claimed. Joint canonicalization is performed in the new dimension.

## 2. A genuine next future with the same fixed pivot

Apply the already verified
`henson_leftDense_realizes_all_finite_numericH_L_columns_and_profiles`
to cutoff H and the explicitly defined column C. That theorem constructs its
finite target from all raw-feasible normalized integer clique vectors; target
existence is not a premise. It returns ONE chronological induced embedding g
and ONE numerical cutoff M with all exact columns and the complete profile.

The embedding g fixes every p<H, hence g(v)=v and every protected old witness
below H remains the SAME actual original. It realizes every feasible new
clique vector in ONE common finite future, with all support counts at once and
no spurious vectors. Every old p<b has c(p,pi(u)), the selected v has beta(u),
and every p in [b,H) except v has zero; both directions hold at every real
generation up to the chosen finite numerical height. All additional omitted
originals between subsequently embedded future vertices also have zero columns
to the later selected future. Carrier bounds are retained with the same g,M.

Substitute the exact formula in section 1 for this actual raw bound. This
constructs the compatible next column AND its finite realization around an
already chosen v. It does not demand positivity on every child. If a branch
has no legal one-vertex extension, no such vertex is inserted into the future.

The finite result can be applied to the physical v supplied by the preceding
selected-witness theorem, because its full old column is supplied by the
original single stage embedding. That full column must be extracted from the
same stage data, not inferred solely from reserved-Q edges.

## 3. Exactly which branches survive

A new sort u supports a one-vertex extension precisely when

    rho({pi(u)}) < ell-1,

and, if beta(u)=1, additionally

    1+rho({pi(u),s}) < ell-1.

Indeed a one-vertex extension is safe exactly when its complete old
neighbourhood has no (ell-1)-clique. The formula in section 1 gives these
inequalities. To relate this to simultaneous raw feasibility, the one-vertex
weight on u has count one precisely on supports containing u, and count zero
elsewhere. Common pools for supports containing u are subsets of the singleton
common pool; hence the singleton inequality supplies every support inequality.
Conversely the singleton support forces the same inequality. Thus testing only
singleton compatibility is valid for branch EXISTENCE, not for the age of
arbitrary mixtures of several surviving sorts.

In particular every old singleton-safe sort retains its zero child. Positive
children may disappear. If all desired new sorts satisfy these explicit tests,
the new canonicalized raw age is a genuine positive integer graph age by
`finiteOldColumnCanonical_is_age_of_singleton_safe`. If they do not, retain only
the safe children (or keep the ambient domain and allow zero branches); never
silently assert positivity of the unpruned domain.

## 4. Adversarial audit obligations

1. The original E is unchanged and v is fixed, not reselected by an unrelated
   existential theorem.
2. H exceeds v; old columns and pivot columns cannot overlap.
3. Full actual gaps are included and given zero columns in both directions.
4. U is nonempty; otherwise the gap-elimination argument fails.
5. pi may be noninjective; use its image, not a support of the same cardinality.
6. S union {s} is a plain finite set; it need not be an admissible old support.
7. Clique capacity, not common-neighbour cardinality, controls the bound.
8. Both directed old-pivot atoms are needed for the mutual-neighbour identity.
9. The +1 term includes the empty clique, so an isolated pivot still contributes.
10. Natural subtraction is kept truncated; unsafe branches can have bound zero.
11. Every clique profile and every column use the SAME next embedding and M.
12. Existing vertices below H are fixed, but the theorem does not preserve an
    arbitrary previous designation of future sorts or prescribed positive links.
13. A singleton-safe branch test does not replace the all-support constraints
    on mixed new cliques.
14. Reindexing raw capacities is not a claim that canonicalization commutes
    with arbitrary sort maps.
15. No full auxiliary E, parameter closure, I1/I2/I3/B3, labelled inverse-source
    orbit, or global Ramsey bound follows merely from this ordinary graph step.

## Independent audit before formalization

Two independent source-level reviews agreed with the finite construction and
the exact capacity formula. The adversarial review of this written proof found
one interface condition to make explicit: the physical tagged realization
requires e>0, because its global sort decoder uses a default element. The
pure common-pool and capacity identities do not require this condition.
It is now included above. The reviews separately checked all fifteen points,
including the oversized S union {s} and the distinction between fixed old
vertices and retained active future roles. The finite ordinary-L proof passed
with that amendment; none of the global obligations in item 15 was discharged.

## 5. Sharper continuation from a maximizing clique (English extension)

There is a useful stronger finite statement when the chosen pivot is retained
as part of a maximizing clique, rather than merely as a vertex of a sort in T.
Suppose C is an actual clique disjoint from [0,b), all its vertices have sorts
in T, its old columns are c, and |C|=n. Suppose also that the actual old raw
bound at T is n (as occurs at the saturated physical cover). Choose ANY v in C
and define beta(t)=1 exactly on T with pi the identity. Let H>v and use the
pointed column of section 1.

Then the new canonical T-capacity is EXACTLY n-1, provided the actual graph
on [0,b) union C is K_ell-free.

Upper bound: v has a sort s in T. Therefore N(T union {s})=N(T), and the
new common-neighbour capacity at T is rho(T)+1. Since C is nonempty and
n=ell-1-rho(T), the new raw bound is n-1. Canonicalization is at most raw.

Lower bound: set R=C minus {v}. Relative to the smaller old pool
[0,b) union {v}, the ACTUAL clique R has precisely the new column: its old
columns are c and all its vertices are adjacent to v. The graph on that old
pool union R is the original K_ell-free graph on [0,b) union C. Hence the
already proved all-support mixed-clique theorem makes R's integer weight
vector feasible for the new raw bounds. The complete-prefix gap identity
identifies those bounds with the bounds over [0,H), even if some vertices of
R themselves lie in that prefix: they are used only as an abstract finite
witness for the smaller pool and are then CLONED by the next universal
realization. They are not falsely claimed to be disjoint from [0,H).
The witness has T-count |R|=n-1, so canonicalization is at least n-1.

This proof includes n=1: R is empty, the new T-value is zero, and the positive
T branch disappears. It proves one-unit loss at the named coordinate only;
other supports may change too, so it does not assert that the full age changes
by exactly one cover. The old raw-tightness and chosen maximizing clique must
both be established in any application. Merely choosing an arbitrary T-sort
vertex is insufficient for the lower bound.

Independent review of this extension passed before formalization. The review
checked the smaller-pool/full-prefix distinction, both directed crossing
columns, the nonempty pivot clique, the empty remainder at n=1, and the fact
that the conclusion is coordinatewise rather than a global age cover. The
canonical lower bound can use the existing canonical all-support equivalence
directly, avoiding any extra normalization assumption.

## 6. Two constructed finite stages with common actual vertices

Assume G_B(T)>0 for the actual old-prefix raw function B at (b,c). Start with
ANY supplied full numerical-stage certificate f,M; the existing constructive
theorem can supply one if it is not already given. Positivity supplies a
genuine tagged w in its universal future W
with tau(w) in T, using the already checked tagged nonvacuity theorem.
This is an actual member of W, not the default value of its sort decoder.

Let H=max(M+1,max(b,1+max f[W])), with the empty finite maximum interpreted as zero
(W is nonempty here). Every first-stage image is strictly below H. The
original-column clause for the SAME first certificate identifies the complete
old type of v=f(w) as tau(w); its chronological clause gives b<=v.
Now apply section 2 at this H to obtain g,M' for the explicit pointed column.
Return BOTH full certificates, the actual tagged w, the cutoff inequalities,
and the exact raw formula. Since g fixes [0,H), it fixes f(x) for EVERY x in W,
including the selected v. Thus the two finite realizations are coherent on
their actual original graph vertices, not merely separately existential.
The new numerical cutoff may also be chosen strictly larger than M: the
second certificate bounds the real top-generation address of the original
with index M (which is below H) by M', and that address is at least M.
This numerical inequality is not a claim of full auxiliary-source coherence.

The main agent audited this addendum before implementation: the finite supremum
strict bound, nonvacuity, same-certificate full old columns, and simultaneous
retention of both witnesses are sufficient. New branches may be empty; their
nonempty ambient sort domain is only an encoding condition. The caveat about
active future roles remains unchanged: other first-stage witnesses receive
zero incidence to the new future. This does not yet justify a prescribed
infinite diary schedule or its complete dependent source records.
The factorization for any supplied first certificate and the ordered-cutoff
choice were also audited before their implementation.

## 7. Audit example: individual live children do not settle their joint age

For ell=4 take old sorts s,a,b. The old graph consists of three disjoint
edges Q_s,Q_a,Q_b and one further isolated vertex z. Both vertices of Q_t
have positive columns only on sort t; z is positive on all three sorts.
Then the old common-neighbour capacity is 2 on singletons and 1 on every
pair and on {s,a,b}. Its raw and canonical ages are therefore 1 on singletons
and 2 on pairs and the triple. The canonical equalities are witnessed by
single vertices and pairs of distinct sorts, while the raw bounds give the
opposite inequalities.

A genuine pivot of old sort s is adjacent to Q_s and z. Consider positive
children of a and b. Each is individually live: its old singleton capacity is
2, and its common capacity with s is 1. But the common new neighbourhood for
the pair {a,b} contains the edge {z,v}, so its new raw and canonical pair
value is 1. An edge between two such future vertices would complete a K4
with z,v. Thus checking that both children exist, the pairwise passing
equalities F({s,t})=F({t})+1, and F({a,b})<=ell-2 is still insufficient to
preserve the old pair profile around an actual pivot.

Two independent mathematical reviews checked this example. It is recorded
as an obstruction to those INSUFFICIENT hypotheses, not as a contradiction
to any theorem whose full hypotheses also impose the joint pointed-clique
constraints. No separate Lean validation mark is assigned to this example.
