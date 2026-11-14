# Track A — one explicit finite universal continuation target over the actual old prefix

**14 November 2026. English proof and hostile audit BEFORE Lean.**
Stacked on exact finite numbering PR #147 and
the generic raw-profile relative K-free target PR #151.
The purpose is to DISCHARGE the finite universal-target
existence hypothesis used by the one-embedding uniform
Henson transport of PR #137.

## Input

Fix the literal entire old prefix P=[0,b) in one original
Boolean graph E; assume its finite directed clique checker
is K_ell-free, with ell>=2, and let the marked sort
set have size d>=1. Prescribe *all* old-to-new type
columns c(p,t), for every p<b and t∈Fin d,
with exact matching in both ordered directions.

Define the ACTUAL raw continuation bound

  B(T) = ell−1−cap_E({p<b:∀t∈T,c(p,t)=true})

for every nonempty admissible support T. No a priori
positive integer-graph-age assumption is made; B(T) may
vanish, correctly excluding future singleton patterns
that would close a forbidden clique with the old prefix.

The existing `universalWitnessFuture d ell B` is a
finite dependent-sum future, consisting of a disjoint
clique component for EVERY normalized B-feasible
integer witness vector w. Each component has labels
from its second Sigma coordinate; distinct components
have NO ordinary-L edges.

## Explicit finite source subtype

Let V be the **subtype of vertices actually belonging
to that future pool**:

  V = {v : UniversalWitnessVertex d ell |
        v∈universalWitnessFuture d ell B}.

No witness is duplicated or silently added.
V is finite even if B has zero values or d=0.
Give V the inherited directed graph
R(v,w)=universalWitnessEdge(v.val,w.val)
and sort(v)=v.val.2.1.

Then prove in Lean:

1. R is symmetric and irreflexive on V;
2. every R-clique s has size <ell;
3. every R-clique s obeys **ALL** raw bounds B(T)
   on its labelled sort counts simultaneously;
4. for every normalized feasible vector w there
   exists a directed clique s⊆V with counts
   exactly w(T) for EVERY admissible support T
   (the common V is independent of w).

The source finite-clique lemmas follow by the
injective subtype value map to the checked
`universalWitnessFuture` graph, using the
existing `universalWitnessFuture_clique_card_lt`
and `universalWitnessFuture_clique_respects_raw`.

For item (4) use the literal single-component
subset
  s_w={v∈V:v.val.1=w}.
Its subtype image is exactly the already checked
`universalWitnessComponent w`, provided w is feasible.
The checked universal component theorem gives its
complete labelled cardinality vector and cliquehood.

## Genuine relative finite target

Let A be the *explicit* Nat graph constructed by
the exact encoder of PR #147, with old coordinates
[0,b), new coordinates exactly
[b,b+Fintype.card V), old edges E, future edges R,
and the prescribed full symmetric c columns.

The verified generic relative gluing theorem in
PR #151 gives, without any hidden model-theoretic
extension axiom,

  finitePoolCliqueCheck A ell
    (Finset.range (b+Fintype.card V))=false.

This is the precise missing finite compatibility
argument: for any old prefix and complete c, one
finite A exists and is K_ell-free, and its same
future interval W realizes every B-feasible
labelled clique vector, with no spurious profiles.

If E is a genuine left-dense Henson enumeration,
its forbidden-family avoidance additionally gives
E symmetric/irreflexive and its old prefixes Kfree.
The encoded A is symmetric/irreflexive, and agrees
with E on every old pair. Therefore the verified
`henson_leftDense_uniform_finite_profiles_over_fixed_prefix`
can be applied to this ONE target to obtain a
**single actual physical original future pool**
with all normalized B-feasible clique profiles
simultaneously, fixing the old prefix, with exact
ordered L atoms and skipped-original gap zeros.

The last Henson composition will be formalized
after the independent PRs #137/#147/#151 merge or
on a reviewed integration branch; this stacked
module discharges the entire finite A-existence
premise in ordinary L.

## Adversarial checks

1. **Whole prefix, not selected shadow:** every p<b
   contributes to B(T), including parameter/gap
   original vertices already committed.
2. **No arbitrary relative universality assumption:**
   A is a *specific constructed* table; its mixed
   Kfree condition is proved via all-support
   old-neighbour clique capacities.
3. **Not raw pointwise canonical equality:** B can be
   noncanonical and zero. The finite universal
   future captures the same feasible vectors as
   G_B, not equality B=G_B pointwise.
4. **Empty feasible vertex set:** the Sigma subtype
   may have no vertices; the proof of Kfree reduces
   to old E. No nonempty-choice assumptions.
5. **Zero raw bound:** a sort t adjacent to an old
   (ell−1)-clique has B({t})=0, and no feasible
   singleton of that sort exists.
6. **Labels with multiplicity:** V includes
   repeated copies of one sort inside a component;
   the subtype value injection never identifies
   these copies.
7. **No edge between distinct components:** R is
   literally the checked same-witness-index
   relation; without this, the union of all
   individually feasible components could
   create new forbidden mixed cliques.
8. **Two-directed crossing columns:** the Nat
   encoder supplies both A(p,w)=c(p,type(w))
   and A(w,p) identically.
9. **No numeric-H generation identification yet:**
   f(target) are actual original indices chosen by
   Henson left density; their top-generation copies
   arise only under the separate numerical-H transport.
10. **No H+ source/auxiliary E/B3 claim:** the
    constructed A controls ordinary graph L only.
11. **No infinite coherence:** even the eventual
    uniform finite physical future is chosen afresh
    for each fixed old prefix and typed columns.
    The resolved diary requires one coherent
    all-stage original selection preserving its
    canonical macro-record invariants.
12. **No Kfree proof from singleton safety alone:**
    the crucial future source hypothesis is the
    JOINT B(T) bound for every support; the source
    universal graph already satisfies it.
13. **No default Fin 0 in Nat sorts:** this specific
    target construction assumes d>0. The abstract
    source clique statements can be formulated
    without that restriction; any d=0 case is
    vacuous for nonempty supports and should be
    treated separately if needed.
14. **No assumption of canonicality of R:** the
    standalone future component graph is checked
    for every directed clique, not just one
    maximum-capacity representative.

## Lean deliverables

New `Kk/RelativeUniversalFiniteTarget.lean`:
finite subtype, exact clique/tagged-image transport,
raw bound, all feasible normalized witness
realization, and the literal old-prefix glued
Kfree finite target. Fully qualified named
standard-only transitive-axiom reports,
explicit exact-head module build and full lake build.
No global manuscript green mark or frozen prose edit.
