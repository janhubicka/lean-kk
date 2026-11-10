# Physical numerical-H reserved-prefix capacity: exact source-to-coordinate bridge

**10 November 2026. English proof and independent adversarial audit before dependent Lean implementation.**

## Data and target

Work in the actual Henson normalized single-binary-symbol graph model, with a symmetric Boolean original-edge table \(E:\mathbb N^2\to\mathrm{Bool}\). Fix the numerical-H height \(k\), an isolated reserved clique block of **consecutive original labels**
\[
  N,\ N+1,\ \ldots,\ N+r-1
\]
with \(1\le r\le k+1\), and a pivot \(0\le a<r\), \(0\le g\le k\). Assume every forward pair of distinct reserved originals has \(E(N+b,N+c)=1\) for \(b<c<r\); symmetry gives the reverse bit. Isolatedness from other original blocks is an **independent** hypothesis for eventual global gluing, not needed to compute the single-block capacity.

Let \(P_{a,g}\) be the finite pair-labelled prefix already defined in \`Kk.ReservedPrefixCapacity\`. Put
\[
F(b,t)=\iota(N+b,t)=2(k+1)(N+b)+2t,\qquad
Q_{N;a,g}=F[P_{a,g}]\subseteq\mathbb N.
\]
The intended result, for the **ordinary binary L relation** of the literal numerical-H graph, is
\[
\operatorname{finiteDirectedCliqueCapacity}
   (L_{H,k},Q_{N;a,g}) =
   \begin{cases}a,&g<a,\\a+1,&g\ge a.\end{cases}
\]
This uses the existing \`Kk.finiteDirectedCliqueCapacity\` on numbered H vertices and the existing literal \`hNumericBinary\`, not a replacement model.

## Step 1 — coordinate injection and finite carrier

The verified successor-tree theorem \`hPosition_injective_bounded\` states that for generations \(s,t\le k\),
\[
\iota(i,s)=\iota(j,t)\implies (i,s)=(j,t).
\]
Every member of \(P_{a,g}\) has generation \(\le k\), and \(N+b=N+c\) implies \(b=c\). Thus \(F\) is injective on the finite prefix, as required by \`reservedPrefixCapacity_image_transport\`.

If the chosen finite H carrier is \([0,M)\) with
\(M>\iota(N+a,g)\), every point of \(Q_{N;a,g}\) lies in it. Indeed, a copy in a strictly earlier original block has position **less** than the pivot even at generation \(k\), by \`hPosition_lt_of_block_lt\`; a copy of the pivot block at generation \(t\le g\) is **at most** its generation-\(g\) position, by the explicit formula. Merely bounding the original label \(N+a\) is insufficient; the numerical H position is the relevant quantity.

## Step 2 — every ordered binary atom, including absent ones

Fix distinct pairs \(x=(b,s),y=(c,t)\) in the prefix.

* If \(b<c\), use \`hNumericBinary_real_forward_iff\` on actual positions \(\iota(N+b,s),\iota(N+c,t)\), with \(s,t\le k\). The base bit is 1 by the original clique. Therefore
  \[
  L_H(Fx,Fy)=1\iff s<t\ \lor\ (s=t=k),
  \]
  exactly the positive half of \`reservedCopyEdge k x y\`. The reverse disjunct in that definition is false because \(b<c\).
* If \(c<b\), apply the same theorem with the endpoints exchanged. The existing \`hNumericBinary_symmetric_of_base\` converts back to the required direction. This use of symmetry is essential because the finite capacity predicate tests **both directed arcs**.
* If \(b=c\), there are **no** positive binary atoms between any two copies of the same original. To prove this, suppose \`hNumericBinary_true_iff\` supplies a crossing witness \(i<j\). The coordinates of both endpoints are two bounded-generation copies of \(N+b\). Applying \`hPosition_injective_bounded\` to the two witness positions forces \(i=j=N+b\), contradicting \(i<j\), in either orientation. This also handles equal pair positions when the underlying pairs are distinct by generation.

Consequently for **all distinct pair-labelled copies in the pool**, in their given ordered orientation,
\[
L_H(Fx,Fy)=1\iff \operatorname{reservedCopyEdge}(k,x,y).
\]
This equivalence gives both positive **and absent** crossing L atoms; positive preservation alone does not suffice.

## Step 3 — transfer exact capacity, not merely an upper bound

Apply the injective image-capacity theorem merged in [PR #74](https://github.com/janhubicka/lean-kk/pull/74). Its hypotheses are precisely Step 1 and Step 2. Identify the locally defined Boolean capacity \`reservedImageCliqueCapacity\` with the existing \`finiteDirectedCliqueCapacity\` by extensionality of their finset filters (both are maxima of cardinalities of the same directed cliques). Finally substitute \`reservedPrefixCapacity_eq_of_height\` from PR #74.

The result is about the actual **L** graph of \`infiniteNumericHL\`; the \`finiteNumericHL\` relation has the same literal binary atoms and is the desired finite carrier specialization once the bound \(M\) is supplied. This does not identify L with the auxiliary E-incidence relation.

## Hostile checks before implementation

1. **Generator aliasing:** \(\iota(i,k+1)=\iota(i+1,0)\). The bounded-generation assumption \(\le k\) is indispensable for injection.
2. **Reverse directed arc:** replacing \`E\` by a nonsymmetric directed table makes the claimed directed capacity wrong; the original graph symmetry must be used.
3. **Same original:** do not infer positivity from base loops; the literal crossing definition only uses \(i<j\). No edge joins two copies of one original.
4. **Top-generation exception:** the top-tie \(s=t=k\) is needed for the \(a\) earlier-top witness. Ignoring it destroys the formula.
5. **Height bound:** if \(g=k<a\), possible without \(r\le k+1\), the \(a+1\) top copies form a counterexample.
6. **Finite carrier:** \([0,M)\) is not enough unless **every** copy in \(Q\) is included. Showing \(M>\iota(N+a,g)\) works only after the block-order lemma is invoked.
7. **Fake coordinates:** only real even positions are in \(Q\). Other fake/selected positions require a separate capacity and isolation argument.
8. **No substitution of auxiliary E:** the capacity theorem is about ordinary \`L.binary\`, not the Kpt-closure incidence \`E\`.
9. **No automatic front:** the single-block result plus isolated-block finite gluing does not yet supply all simultaneous marked columns, selected supports, or corrected (B3) age.
10. **Zero boundary:** \(a=0\) yields a singleton prefix and capacity 1; a missing empty-witness argument can corrupt the \(g<a\) branch for \(a>0\).

## Dependent Lean implementation checklist

First prove actual \`hNumericBinary\` same-original negativity and coordinate injection (no new axioms). Next establish the complete directed real-copy gate equivalence on the entire prefix. Then identify \`reservedImageCliqueCapacity\` with the existing executable finite capacity and specialize the formula to both infinite and finite H binary tables. Lastly show the prefix lies in \`finiteNumericH\`'s carrier when the explicit numerical bound is met.

Do not mark manuscript statements green until the **literal physical specialization** compiles with a whole-repository build and exact named transitive-axiom audit. Even a successful physical prefix-capacity theorem leaves all-front column synchronization, integer-age canonicalizer bridging, parameter-closed envelopes, labelled common source, and unconditional Ramsey bounds open.
