# Track F — actual non-root continuation with certified target rank ≤ source rank

17 November 2026. English proof and hostile audit before Lean.
Composes verified genuine non-root rank-large target-prefix continuation
(PR #296) with the transported old-source clique certificate in
new PR #297 (awaiting its dedicated Lean gate at this point).

## Stronger transport statement

Let Esrc,Etgt be original graph edge tables of the same K_ell
threshold. Assume the target Etgt avoids the normalized
forbidden family (so every finite target prefix is K_ell-free).
Let e:Nat→Nat be an arbitrary injective induced embedding
of the directed edge tables; DO NOT assume e is order-preserving.

Take a genuine source finite one-type u, a genuine target
finite one-type v0, and assume its ACTUAL source coding-node
fibre A(v0) is rank(u)-large above u.

Given any prescribed finite target cutoff B, there exist:
- an ACTUAL target finite type vH, extending v0, of exact
  level H at least B;
- a genuine source finite type uH≥u with rank(uH)=rank(u);
- A(vH) remains rank(u)-large above uH;
- **rank(vH) ≤ rank(u)**.

This is a stronger, rank-one-sided component of the manuscript's
"compatible rank transport" claim. It does NOT establish equality
of ranks.

## Proof

First pick H larger than the requested cutoff B, the old target
level v0.level, and EVERY image e(c) of the finitely many old
source neighbour vertices c∈u.neighbours. Formally take
H=max(B,v0.level,1+sup{e(c):c∈u.neighbours}).

The verified non-root continuation theorem PR #296 constructs
vH and uH with v0≤vH, vH.level=H, u≤uH,
rank(uH)=rank(u), and A(vH) rank(u)-large above uH.

The verified largeness-has-member theorem provides a real
source coding node x∈A(vH) extending uH. Hence x extends
the ORIGINAL u. In particular each old source neighbour
c∈u.neighbours is adjacent to the actual source original
x.level. Because e is induced and e(c)<H=vH.level,
its image e(c) belongs to vH.neighbours. Thus
e[u.neighbours]⊆vH.neighbours. The previously verified
induced image clique capacity theorem yields

cap_Esrc(u.neighbours)
   = cap_Etgt(e[u.neighbours])
  ≤ cap_Etgt(vH.neighbours).

With the actual one-type rank definitions this is precisely
rank(vH)≤rank(u). Note that the bound is obtained from
old u, NOT from the possibly longer source type uH:
e[uH.neighbours] need not lie below H, so applying the
certificate to uH could be INVALID.

## Why the other direction remains open

Target rank ≥source rank follows from the already verified
future-target-clique obstruction (PR #275) IF one can choose
a genuine source clique X of size rank_manuscript(u)
inside the selected rank-large source fibre A(vH).
Then e[X] is a clique of target future originals fully joined
to vH.neighbours. This existence is the missing one-sort
clique-richness implication, a real subcase of the larger
multi-sort richness theorem. Neither rank-large partition
nor the finite-fan theorem on its own proves it.

## Hostile checks

1. The target cutoff H must exceed all e-images of OLD
   source neighbour markers, not source levels themselves.
2. The embedding must be injective AND edge-induced;
   a general injective index map does not transport clique
   capacity or old neighbour bits.
3. The source actual coding witness x is obtained via the
   rank-large fibre, not a hypothetical arbitrary type.
4. The certificate applies to the ORIGINAL u. Its extension
   uH may have extra old neighbours whose images occur
   after the chosen target H.
5. Source and target ranks are actual maximum-clique
   capacities on their genuine finite old-neighbour sets.
6. The target graph's Henson avoidance is used for the
   construction of vH, not for the pure induced-image
   old-clique inequality.
7. Rank equality must NOT be inferred from one-sided
   inequality or from finite target-prefix colouring alone.
8. No claim is made about complete mixed multi-sort profiles,
   diary persistence, or numerical BRDs.

## Lean acceptance

Compose PR #296 and PR #297 only after their exact-head
gates pass. Audit the source rank and target cutoff hypotheses
very carefully, especially the distinction between u and uH.
Require an exact-head Lean build and named transitive axiom check.
Do not promote global manuscript validation marks.