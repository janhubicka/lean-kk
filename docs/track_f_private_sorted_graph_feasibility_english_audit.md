# Track F — all-clique raw feasibility under private rank-zero sort refinement

18 November 2026. English proof written before the Lean bridge.

## Problem and exact statement

Let \(B\) be a finite graph on the ordered vertex set \([0,N)\), and let
\(\sigma:[0,N)\to P\) be its parent-sort labelling. For every nonempty **directed clique**
\(C\subseteq [0,N)\), assume its cardinality is at most the actual raw age
\(R_{\rm old}(\sigma[C])\).

Replace its sort labels by a private sort per vertex. Formally choose a finite private
sort set \(D\), a map \(\tau:\mathbb N\to D\) which is **injective on** \([0,N)\),
and a map \(\pi:D\to P\) such that \(\pi(\tau(a))=\sigma(a)\) for every \(a<N\).
The private sorts may project to the SAME parent. We need only the following
properties of their new raw ages:

* \(R_{\rm new}(\{i\})\ge 1\) for every private sort \(i\);
* \(R_{\rm new}(S)=R_{\rm old}(\pi[S])\) for every private support with at least
  two distinct sorts.

Then **every nonempty directed clique** \(C\subseteq [0,N)\) obeys
\[
     |C|\le R_{\rm new}(\tau[C]).
\]

## Proof — two genuinely different cases

For \(|C|=1\), say \(C=\{a\}\), the image is \(\tau[C]=\{\tau(a)\}\). The new
singleton capacity is at least one, so the inequality holds. We do NOT attempt
to pull the singleton capacity back from the parent; a rank drop normally
changes that numerical capacity.

For \(|C|\ge 2\), injectivity of \(\tau\) on the selected interval gives
\(|\tau[C]|=|C|\ge 2\). We may use the actual mixed-support identity, obtaining
\[
 R_{\rm new}(\tau[C])
 = R_{\rm old}(\pi[\tau[C]])
 = R_{\rm old}(\sigma[C]).
\]
The last equality is pointwise label compatibility and holds even when
\(\pi\) identifies distinct private sorts. The original global clique
feasibility now gives \(|C|\le R_{\rm old}(\sigma[C])\), as required.

This is more economical than attempting to derive bounds for **all**
subsupports of \(C\). That route needs monotonicity of raw ages and is
unnecessary for the finite graph realization theorem, whose hypothesis only
ranges over supports actually occurring as images of directed cliques.

## Application to the actual Henson source

Take \(D=\mathrm{Fin}(N+1)\) so there is a dummy private sort even if \(N=0\),
and \(\pi(i)=\sigma(i.val)\). For each actual \(a<N\), let \(\tau(a)\)
be the canonical index \(a\) in \(D\), and send indices beyond \(N\)
to the dummy sort. Then \(\tau\) is injective on \([0,N)\) and
\(\pi(\tau(a))=\sigma(a)\) for \(a<N\).

The merged private-daughter theorem (#358) applied to
\(u'_i=u_{\pi(i)}\), \(S'_i=S_{\pi(i)}\) gives an actual common-level
family \(v_i\) of rank-zero roots with
\[
 M_i=v_i.neighbours\setminus u_{\pi(i)}.neighbours
\]
pairwise disjoint. Their common new level is \(H\ge m\). Exact
chronological extension of all positive AND negative old bits gives
\(v_i.neighbours=u_{\pi(i)}.neighbours\cup M_i\), with
\(M_i\subseteq[m,H)\).

For every private support of at least two distinct sorts, the merged
actual disjoint-marker raw-collapse theorem (#259) gives
\(R_{\rm new}(S)=R_{\rm old}(\pi[S])\). Each singleton has raw capacity at
least one because \(v_i\) is a **genuine safe finite one-type**:
the clique capacity of its old neighbourhood is strictly below
\(\ell-1\). Its rank is zero, as also required for applying the
finite sorted graph realization theorem (#355). Thus the abstract
all-clique bridge proves precisely the new global B-feasibility
hypothesis of #355, not a stronger unsupported numerical canonical
age equality.

Apply #355 with the actual coding-node sets \(S'_i\) and rank-zero
roots \(v_i\). It returns a genuinely chronological induced copy of B,
one actual original coding vertex in the corresponding old \(S_{\sigma(a)}\)
per abstract vertex, and exact old prefix bits. The points are selected
chronologically and all prescribed edges **and nonedges** hold.
To translate the old column from the new common prefix \(H\) to the
original prefix \(m\), use the full-bit prefix extension
\(u_{\sigma(a)}\le v_{\tau(a)}\), not merely positive-set inclusion.

This will establish **finite SOURCE richness conditional on the
displayed rank-large, actual coding-node source fibres**; it does NOT
establish target mixed-profile synchronization, full diary
unavoidability in every induced copy, or the BRD lower bound.

## Adversarial checks

1. The global hypothesis ranges over all nonempty cliques, not all vertex sets.
2. Singletons cannot use mixed raw equality; new singleton rank may be smaller.
3. A two-vertex clique with the SAME parent sort still uses TWO distinct private sorts.
4. \(\tau\) needs injectivity only on the selected interval, not on all Nat.
5. \(\pi\) may identify private sorts; pointwise compatibility is enough.
6. A finite graph need not be a clique globally. Apply the bridge to each clique separately.
7. Empty \(B\) is harmless; the extra dummy private sort supplies the total label map.
8. Genuine old Henson neighbours must lie below the original common prefix \(m\).
9. The new marker sets must lie above \(m\), below common \(H\), and be pairwise disjoint; merely disjoint unspecified *sets of changed bits* does not establish the physical collapse.
10. Safe rank-zero roots produce **positive** singleton raw bounds; no assumption of arbitrary future vertices is introduced.
11. The resulting source coding originals must be in the ORIGINAL \(S_{\sigma(a)}\), not just in some abstract descended type set.
12. This is a statement about the SOURCE graph. Do not promote manuscript diary/BRD validation marks or freeze changed black claims.

## Lean acceptance

First formalize the pure all-clique transfer from \((\pi,\tau)\), singleton positivity,
and mixed-support equality, with standard-axiom gate. Then compose it with
the physical disjoint-marker theorem, PR #358 common-front daughters, and
PR #355 real rank-zero finite graph realization. Audit the final theorem
statement for physical coding membership, full two-directed inducedness,
and chronological levels before promoting any olive richness lemma.
