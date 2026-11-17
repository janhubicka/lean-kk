# Track F — finite target-prefix colours inside rank-large Henson fans

17 November 2026. English proof and adversarial audit **before** Lean.
Depends on the successfully verified and merged one-type tree (#222), abstract
finite partition (#212) and finite-fan (#255) theorems. Neither JEMS diary
unavoidability nor the manuscript's exact BRD assertion is an input.

## Precisely scoped statement

Fix the *actual chronological finite Henson one-type preorder* (P),
the antitone zero-based rank (ho), a node (u) of rank (r+1),
and any set (Ssubseteq P) which is ((r+1))-large at (u).
Let (c:P	o C) be ANY colouring with **finite** palette (C).
For each prescribed bound (H) and number (k), there is a colour
(jin C), a same-rank descendant (vge u) of level at least (H),
and a set (F) of (k) daughter types of rank (r), such that:

- the (j)-coloured fibre (S_j={xin S:c(x)=j}) is ((r+1))-large at (v);
- every daughter (win F) extends (v) and (S_j) is (r)-large at (w);
- different daughters have no common later type, and their positive
  fresh-marker sets relative to (v) are pairwise disjoint.

**Proof.** First extend (u) to its all-zero type at level
(max(H,operatorname{level}(u))). This preserves rank and largeness.
Apply the already verified *finite-colour rank-large partition* to
(S), obtaining a colour and another same-rank descendant (v)
carrying that colour class largely. Apply the verified *finite-fan
theorem* at (v) to the selected fibre. All inequalities and ranks
follow by transitivity and the exact conclusions of these theorems.

**Finite removal strengthening.** For any fixed finite set (Q) of
bad source coding nodes, first apply the already verified
`HensonOneType.large_difference_finite`. Repeat the previous
argument with (Ssetminus Q). Each daughter's large fibre has
a genuine member above it by `RankLargeness.large_has_member`.
This member belongs to the selected colour class and avoids (Q);
members from different daughter cones are distinct, because those
cones are incompatible. This yields (k) distinct genuine
*type nodes* in one colour and outside (Q), although their
own later fresh-marker sets need **not** be disjoint.

## Target-prefix application boundary

For a fixed target enumeration bound (H), the binary prefix of a
potential image has type (C=(mathrm{Fin} H	omathrm{Bool})), a finite
palette. Thus the theorem applies to the colouring which sends a
**source coding node** to the adjacency vector of its image below
(H), once an actual coding-node/embedding map is separately
defined. It is independent of the ordering of source and target
enumerations: a finite target prefix still produces a finite palette.

**Crucially:** A colour-large source fibre in this theorem is NOT
automatically compatible at the *same singleton rank* with the
corresponding target type. Showing that rank is preserved requires
the actual one-sort richness / clique-witness theorem and induced
graph embedding, not just a finite-colour partition.
The theorem also does not synchronize the full multi-sort capacity
profile or prove that every prescribed history occurs.

## Hostile checks

1. **Positive rank required:** the finite-fan result is invoked at
   rank (r+1), not rank 0. At rank 0 only a dense monochromatic
   subcone is guaranteed, not a fan of lower-rank daughters.
2. **Colour function may be arbitrary but palette must be finite:**
   the host's one-point target prefix produces finitely many bit
   vectors, while the full infinite target coding type does not.
3. **No false preservation of exact target rank:** colour
   homogenization identifies a *prefix bit vector*; target rank
   alignment needs a separate graph-theoretic argument.
4. **Finite removal is prior to colour selection:** otherwise
   removed coding witnesses could exhaust the chosen colour
   on a subcone. The verified finite-deletion theorem makes the
   deduction valid.
5. **Daughter markers vs coding witnesses:** fresh-marker
   disjointness holds for the selected daughter TYPES. It is not
   asserted for arbitrarily late coding witnesses in their cones.
6. **No hidden induced-embedding hypothesis:** the formal theorem
   quantifies over an arbitrary finite colouring of actual finite
   source types. The embedding application is future work.
7. **No cardinality shortcuts:** the result gives finite fans
   inside a fibre; no big Ramsey degree count follows until
   the remaining richness/compatibility/history arguments.

## Lean acceptance

Formalize colour selection after zero-padding, its composition
with `rank_large_finite_fan`, and the strengthened version with
finite bad-node avoidance and a genuine coding-node witness in
each daughter cone. Add strict exact-head named axiom reports;
only after those pass should a narrowly scoped component mark
be considered. No global lower-bound or diary bijection mark
is promoted.