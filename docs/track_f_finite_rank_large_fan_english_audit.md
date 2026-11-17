# Track F — finite fans of rank-large Henson one-type cones

16 November 2026. **English proof and adversarial audit committed before Lean.**
Depends only on the now-merged exact Henson one-type tree / rank-largeness
module and the nine verified abstract finite-colour partition theorems.
No diary count, JEMS unavoidability theorem, or global BRD characterization
is assumed.

## Starting data

Fix the *actual chronological finite one-type preorder*
\(P=\mathrm{HensonOneType}(\ell,E)\), from merged Track F PR #222.
A node \(u=(m,U)\) records the complete positive old-neighbour
set \(U\subseteq[0,m)\), with the genuine \(K_{\ell-1}\)-free finite
consistency test. The extension order preserves **all** positive
and negative bits below the old height.

The zero-based rank is \(\rho(u)=\ell-2-\omega_E(U)\). It is
antitone under extension. For any \(H\ge m\), the zero-padding
\(z_H=(H,U)\) satisfies \(u\le z_H\) and \(\rho(z_H)=\rho(u)\).

Suppose \(\rho(u)=r+1\) and \(S\subseteq P\) is recursively
\((r+1)\)-large above \(u\) in the actual type tree.

## A rank-drop descendant diverges from the zero spine

Choose any \(v\ge u\) with \(\rho(v)=r\), and let
\(z=\operatorname{zeroPad}(u,\operatorname{level}(v))\).
Then \(\rho(z)=r+1\), whereas \(\rho(v)=r\); their heights are equal.

**Claim.** \(v,z\) have no common extension. If \(t\) extended both,
their complete bit assignments below their common height would agree
with \(t\); hence \(v,z\) would extend one another and have equal
ranks by antitonicity, a contradiction.

This rules out a **common later cone**, not merely equality of nodes.

## Fresh daughter above an arbitrary finite family

Let \(D\) be any finite family of already selected descendants
\(v\ge u\) of rank \(r\), with \(\operatorname{Large}(r,S,v)\).
Choose \(H\) larger than every level appearing in \(D\), and
\(H\ge \operatorname{level}(u)\). Let \(z_H\) be the rank-\((r+1)\)
zero-padding of \(u\) to height \(H\).

By largeness of \(S\) above \(u\), applied to **this same-rank**
extension \(z_H\), there is \(w\ge z_H\) of rank \(r\) with
\(\operatorname{Large}(r,S,w)\).

For each old \(v\in D\), \(v\) is incompatible with \(w\):
the zero-padding \(z_{\mathrm{level}(v)}\le z_H\le w\)
is incompatible with \(v\), so any common extension of \(v,w\)
would contradict the preceding claim.

Moreover their **fresh positive-marker sets** are disjoint:
\[
  (U_v\setminus U_u)\cap(U_w\setminus U_u)=\varnothing.
\]
Indeed every \(x\in U_v\setminus U_u\) lies below
\(\operatorname{level}(v)\le H\). Since \(w\) extends the
zero-padded \(u\), the bit of \(w\) at \(x\) equals the bit of \(u\),
which is zero. This is stronger than merely choosing different nodes
or incomparable cones and connects directly to the verified
disjoint-marker theorem of PR #237.

## Arbitrarily many daughters

Induct on a prescribed number \(k\). For \(k=0\), take the empty
family. Given \(k\) rank-\(r\), \(r\)-large daughters with pairwise
incompatible cones and pairwise disjoint fresh positive-marker sets,
apply the fresh-daughter lemma to that finite family. The new node
is incompatible with all previous nodes and has disjoint fresh markers
from all of them, so it cannot already belong to the family.
Inserting it increases the cardinality to \(k+1\).
Thus every rank-\((r+1)\)-large source cone contains arbitrarily large
finite families of mutually incompatible rank-\(r\)-large daughter
cones with pairwise disjoint new positive-neighbour markers.

## Hostile checks

1. **Largeness, not mere nonemptiness:** We need a witness above
   *every* same-rank zero-padded refinement. A single rank drop at
   the root cannot provide arbitrary many large daughters.
2. **Full prefix agreement:** If extension preserved only positive
   bits without preserving negative bits, a later daughter could
   re-use an old forbidden marker. The actual type preorder preserves
   both.
3. **Zero padding must preserve rank:** This follows from unchanged
   neighbour *set* \(U_u\), not merely from a new free vertex being
   available in the graph.
4. **Equal-height compatibility argument is essential:** Two
   incomparable nodes can still have a common extension in a
   general preorder; here exact bit agreement at the same height
   forbids it when their ranks differ.
5. **Marker disjointness is explicitly proved:** Incompatible cones
   alone do not imply disjoint sets of fresh positive old-neighbour
   coordinates.
6. **Avoid empty-tree sleight of hand:** A large rank-\((r+1)\) set
   yields a real rank-\(r\) descendant above each padding, so the
   finite selection induction never relies on artificially inserted
   unpopulated daughter cones.
7. **No simultaneous Henson fibre richness yet:** These are
   arbitrary *one-source* large coding-node sets \(S\). For many
   different source types \(u_i\), and an arbitrary induced embedding,
   proving the compatible target fibre \(A(v)\) is large and
   synchronizing the complete sorted graph profile remain distinct
   obligations.
8. **No new numerical BRD claim:** The theorem provides the
   finite branching/marker isolation needed inside the richness
   proof; it does not identify the resulting record count with
   big Ramsey degree.

## Formalization gates

First prove the equal-height/common-extension rank rigidity lemma
and the zero-spine incompatibility lemma in the concrete
\`HensonOneType\` structure. Then formalize finite-family selection
using \`Finset.sup\` of heights and the existing verified
\`RankLargeness.Large\` recursion. Keep both incompatible cones
and disjoint marker sets as explicit conclusions. Prove the
finite-cardinality induction, and audit all named theorems using
exact-head Lean build and strict transitive axiom checks.

No frozen black TeX should change. The manuscript's lower bound,
richness and synchronization claims remain pending until the
actual multi-sort gluing and compatibility claims are proved.
