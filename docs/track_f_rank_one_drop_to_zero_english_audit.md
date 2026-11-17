# Track F — rank-one-to-zero compatible source/target drop

17 November 2026. English proof and hostile audit BEFORE Lean.
Lean zero-based rank 1 is manuscript singleton rank 2;
zero-based rank 0 is manuscript singleton rank 1.

## Statement

Let Esrc,Etgt be actual graph edge tables of the same
threshold ell and Etgt satisfy the normalized forbidden
K_ell-family condition. Let e:Nat→Nat be an injective
INDUCED graph embedding, not assumed order-preserving.

Fix any genuine source finite type u of Lean rank 1
and genuine target type v0. Suppose the exact ACTUAL
sourceCodingFibre Etgt e v0 is rank1-large above u.

For ANY target cutoff B, there exist source and target
types uH,vH with:
- u≤uH and rank(uH)=0;
- v0≤vH, level(vH)≥B and rank(vH)=0;
- the genuine coding-node target fibre sourceCodingFibre(vH)
  is rank0-large above uH.

This is the FULL rank-drop compatibility clause at
manuscript rank 2, with no requirement that the original
target rank be separately assumed equal to 1.

## Proof

Recursive rank1 largeness of A(v0) above u says that
for EVERY same-rank descendant w≥u, some lower-rank
node t≥w of rank0 supports rank0 largeness of A(v0).
Apply this definition with w=u (reflexivity) and
rank(u)=1 to choose such a t.

The now verified exact rank0 source-target continuation
theorem (merged PR #301) applies directly to the
pair (t,v0) and its rank0-large ACTUAL source coding
fibre. It gives arbitrary target cutoff B, target
type vH≥v0 of exact rank0, and source same-rank
refinement uH≥t of rank0, retaining rank0 largeness.
Since u≤t≤uH, the required result follows.

This proof is shorter than redoing a target old-clique
certificate and finite partition directly for the rank
drop. The lower-rank same-rank continuation theorem
already packages those arguments.

## Hostile checks

1. Rank largeness must be applied to u itself as a
   SAME-RANK descendant. Source rank1 is an explicit
   hypothesis; without it the successor-rank clause
   cannot be invoked on u.
2. The lower-rank witness t is a genuine consistent
   HensonOneType, but need not be an ACTUAL coding
   original. The fibre A(v0) is nevertheless about
   actual coding nodes, and its rank0 density is a
   genuine hypothesis of the continuation theorem.
3. No assumption that e respects source/target order.
4. Rank0 target equality is supplied by verified #301,
   not inferred from source rank alone.
5. Target v0 need not itself be rank0 or rank1 for
   the displayed mathematical implication; in the
   intended manuscript application it starts at rank1.
6. This proves only the rank1→0 drop; source rank2→1
   will use the separate rank1 SAME-RANK continuation
   of draft #302, once it passes exact-head Lean.
7. Multi-sort graph-age synchronization and history
   persistence remain separate, as does the global
   BRD lower theorem.

## Lean acceptance

Apply the defining successor clause of
RankLargeness.Large at node u, then call the
already verified rank0 continuation theorem
sourceCodingFibre_continue_equal_rank_zero and
compose the source extension inequalities.
Require a targeted exact-head Lean build and a named
standard-only transitive-axiom report. Do not promote
full diary or lower-degree manuscript validation.