# Track F — a real non-root compatible target-prefix continuation (no rank equality yet)

17 November 2026. This is the English proof and hostile audit
**before** Lean, building on the verified injective cutoff and
monochromatic prefix refinement of PR #293 and the physical
target-type extraction drafted in PR #295.

## Exact conditional theorem

Let Esrc and Etgt be ordinary graph edge tables. Assume Etgt
has the verified normalized K_ell-free Henson forbidden-family
avoidance predicate, and e:Nat→Nat is INJECTIVE (not ordered).
No order-preserving property of e is assumed.

Fix a genuine target finite type v0 of level h0 and an actual
source finite type u. Suppose the exact source coding-node fibre

A(v0)={x: x is an ACTUAL source coding node,
          e(x.level)≥h0,
          the full two-directed target column of e(x.level)
          on [0,h0) equals v0's old-neighbourhood bits}

is rank(u)-large above u. This is a weaker assumption than the
FULL paper compatibility predicate because no equality
rank(v0)=rank(u) is required.

For every H≥h0, there exist:
- a GENUINE target finite type vH of exact level H, extending v0,
- a source type uH extending u with rank(uH)=rank(u),
- such that A(vH) is rank(u)-large above uH.

**No claim** rank(vH)=rank(u) is made.

## English proof

By the verified eventual-preimage lemma (#293), choose M such
that e(x)≥H for every source index x≥M. Zero-pad the source
type u to at least M, preserving its rank and A(v0)-largeness.
Apply the verified finite target-prefix colouring theorem to
obtain one colour j (both directed adjacency columns on
[0,H)) and a same-rank source descendant uH where the
j-colour source fibre remains rank-large. Extract one REAL
source coding node x in that fibre. By the chosen cutoff
y=e(x.level)≥H. Since x∈A(v0), its y-column matches the
old target v0 below h0.

Construct vH from the ACTUAL target original y on [0,H)
using the physical K_ell-free certificate of PR #295:
the old-neighbour set {a<H: Etgt(a,y)=true} is
K_(ell-1)-free, hence an admissible target type; the
two directed target columns of y equal its recorded bits.

Then v0≤vH: they have compatible complete columns below
h0, because both agree with the same actual y. (This
step must use the equality of BOTH true and false old bits,
not just inclusion of positive neighbour sets.)

For each coding node z of the large selected j-colour fibre,
the equality c_H(z)=j=c_H(x) means the complete target
two-directed columns of e(z.level) and y coincide on
[0,H). Its image is beyond H by the cutoff. Since it was
in A(v0), z is an ACTUAL source coding node. Hence z∈A(vH).
The selected rank-large colour set is globally included
in A(vH). The verified monotonicity of Large under set
inclusion implies A(vH) remains rank(u)-large at uH.

This constructs an actual NON-ROOT large target fibre
without assuming target rank equality or source/target
enumerations are order compatible.

## Hostile audit

1. Etgt K_ell-freeness and symmetry are required to turn
   j into an admissible target type, not merely a binary
   colour. They follow from verified forbidden-family
   avoidance rather than an invented graph-age axiom.
2. The chosen colour j must have a REAL coding witness x;
   largeness plus sourceCodingFibre membership supply one.
3. The injective-map cutoff excludes all late-source images
   inside H. If e is not injective, this step may fail.
4. v0≤vH uses exact NEGATIVE as well as positive bits below
   h0; old target vertices cannot gain fresh adjacencies.
5. The target type is derived from an actual y, not created
   from an arbitrary claimed safe colour.
6. rank(uH)=rank(u) is verified by the rank-large partition;
   nothing in this argument forces rank(vH)=rank(u).
7. The result is conditional on A(v0) already large. Root/root
   largeness was verified in PR #285 under OnePointLeftDense;
   propagation of *matching target singleton ranks* is separate.
8. Even if all singleton target ranks match, mixed support ages
   of a finite tuple must be synchronized using the actual
   source and target clique certificates.
9. This is not a diary unavoidability or global BRD theorem.

## Acceptance

Implement the target-type reconstruction and column-equivalence
proof after the exact-head PR #295 gate, then compose the
rank-large prefix-colour result of merged PR #293.
Inspect the exact theorem statement and transitive axioms.
Do NOT promote the manuscript's full compatibility or
independent-set degree marks from this restricted result.
Frozen black manuscript prose remains unchanged.