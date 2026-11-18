# Track B — fully linked positive successors FORCE a genuine canonical-age loss

**18 November 2026. English proof and adversarial audit, BEFORE Lean code.**

## Correction to the previous Track B boundary

The last source-exact finite theorem proved that a later original \(v\), fully adjacent in both original \(E\) directions to the real post-cover reserved clique \(Q\), is *critical* at the cover support \(T\) provided its complete future-sort column is positive on all of \(T\). The manuscript correctly did **not** infer a canonical loss from arbitrary raw criticality: Track A has real counterexamples in which a raw constraint changes but the canonical age does not.

**The actual cover situation is stronger**, however. The exact cover equations and the genuine clique \(Q\) force the post-cover raw T-bound to equal the post-cover canonical T-age, namely \(F_{\rm lower}(T)\). Therefore a positive fully linked original at T necessarily makes the new canonical T-age **strictly smaller than** \(F_{\rm lower}(T)\). The proof does **not** require any assumption that all intervening real originals were neutral, nor a separate K_ell-free safety hypothesis; they can only contribute further old common-neighbour cliques.

## Step 1: a complete-physical-source clique lower bound

Let \(E:\mathbb N^2\to\{0,1\}\) be an arbitrary directed graph, \(d,\ell\in\mathbb N\), \(T\) any admissible nonempty future-sort support, \(F\le v\) real original indices, \(Q\subseteq[0,F)\) a genuine directed clique. Suppose:
* the complete typed future column \(c_{\rm next}(q,t)=1\) for **every** \(q\in Q\) and \(t\in T\);
* \(c_{\rm next}(v,t)=1\) for every \(t\in T\);
* both original edge bits \(E(q,v)=E(v,q)=1\) for every \(q\in Q\).

Then \(Q\cup\{v\}\) is a directed clique with \(|Q|+1\) vertices. Crucially, it is contained in the **entire physical** common-neighbour pool
\[
X_{[0,v+1),c_{\rm next}}(T)
=\{p<v+1:c_{\rm next}(p,t)=1\text{ for all }t\in T\}.
\]
No condition is imposed on original vertices in the gap \([F,v)\). Hence by monotonicity of actual directed-clique capacity,
\[
\rho_E(X_{[0,v+1),c_{\rm next}}(T))\ge |Q|+1.
\]
With natural truncated subtraction,
\[
B_{[0,v+1),c_{\rm next}}(T)
=\ell-1-\rho_E(X(T))
\le \ell-1-(|Q|+1).
\]
This fact uses no forbidden-free, symmetry, diary, canonical age or Henson density hypothesis.

## Step 2: the real cover saturates both RAW and CANONICAL distinguished T-age

Assume \(\mathrm{lower}\lessdot\mathrm{upper}\) is a genuine integer-witness graph-age cover at T, with
\(\mathrm{upper}(T)=\mathrm{lower}(T)+1\) and
\(\ell=\mathrm{lower}(T)+r+1\).
Let the complete original-prefix canonical age be upper and Q a genuine clique of size r, isolated in both directions from EVERY original \(p<b\), positioned in \([b,F)\), with complete gapped support-T future columns. The already verified \`isolatedSupportCanonicalAge_cover_step\` together with \`supportBlockGappedCanonicalAge_eq\` implies
\[
\operatorname{Can}(B_{[0,F),c_1})=\mathrm{lower}
\qquad(c_1=\mathrm{supportBlockGappedColumn}(b,Q,T,c)).
\]
Moreover the source-exact \`real_cover_anchor_common_capacity_exact\` gives
\(\rho_E(X_{[0,F),c_1}(T))=r\); thus
\[
B_{[0,F),c_1}(T)=\ell-1-r=\mathrm{lower}(T).
\]
The T coordinate is **not canonically redundant** after the real cover.

## Step 3: a later fully linked positive vertex forces STRICT canonical loss

Let \(c_{\rm next}\) agree with the whole \(c_1\) on every original \(p<F\), including ALL reserved, selected, parameter and real gap originals. Suppose a genuine \(v\ge F\) satisfies the three positive/link conditions from Step 1. The complete old-prefix age before v still equals lower by prefix locality; Step 1 with \(|Q|=r\) gives
\[
B_{[0,v+1),c_{\rm next}}(T)
\le \ell-1-(r+1)
=\mathrm{lower}(T)-1.
\]
The canonical age is pointwise below its raw bound. Since every genuine integer graph age has \(1\le\mathrm{lower}(T)\), it follows that
\[
\boxed{\operatorname{Can}(B_{[0,v+1),c_{\rm next}})(T)
      < \mathrm{lower}(T)
      =\operatorname{Can}(B_{[0,F),c_1})(T).}
\]
Here **[0,v+1)** is the entire actual original prefix, not the artificial subset \([0,F)\cup\{v\}\), and neither a no-gap certificate nor a K_ell-free premise was used. Such a future column might prevent further positive extension; that possibility is exactly what the canonical-age loss records.

## Hostile checks and counterexample

1. This argument is specific to an actually saturated support after a genuine age cover. Arbitrary raw criticality need NOT change a canonical age.
2. The strong conclusion uses both the concrete complete old column on Q and the complete future column on v. Agreement of only selected-front ages does not establish either.
3. Q is a genuine original directed clique, not a set of selected copies or a family of abstract age constraints.
4. Full mutual adjacency in BOTH E directions is necessary for the directed-clique argument. One-sided adjacency is insufficient.
5. Any real original gaps \([F,v)\) may contribute extra cliques: they can only *strengthen* the raw upper bound, not defeat it.
6. No K_ell-free safety is necessary for the purely algebraic implication; of course a genuine Henson application must separately satisfy forbidden-family avoidance.
7. The known post-cover age lower must be **pointwise the whole canonical age**, derived using the real source equations and \`AgeCover\`, not assumed from the raw clique block alone.
8. Natural truncated subtraction is essential if the new T-bound becomes zero, e.g. \(\mathrm{lower}(T)=1\). Positivity of lower comes from the age-cover axiom, so the strict inequality still holds.
9. This proves at least one canonical T-drop, NOT exactly one cover or exactly one unit of canonical decrease. A single original may change several coupled raw inequalities simultaneously.
10. Concrete K3-free counterexample to exactly-one canonical drop: let old originals a,b be nonadjacent. Sort 1 has old neighbour a alone and sort 2 has b alone. Before adding v, raw bounds at {1}, {2}, {1,2} are (1,1,2), canonical age at {1,2} is 2. Add v adjacent to both a,b (still a triangle-free star) with positive columns to both sorts. New raw bounds become (0,0,1) and canonical age at {1,2} becomes **0**: drop 2, despite the raw joint-bound dropping only 1. Therefore never assert an automatic *cover* event.
11. At a genuine first Henson finite top stage, additional work is needed to identify actual selected witness v and to specify which future support T it remains positive on. The finite existential top-stage theorem alone does not provide future-sort transport under split/coding.
12. This is a local ordinary-L canonical obstruction, not an unconditional unbounded diary, full dependent Kpt I1/I2/I3/B3 source, labelled inverse orbit or global BRD result. Existing black manuscript text remains frozen.

**Acceptance criteria:** exact-head \`lake build\`, strict transitive axiom audit on every newly registered theorem (only propext/Classical.choice/Quot.sound; no sorryAx), independent witness counterexample check, and concise olive corrections with source-pinned marks. Do not promote the bounded resolved copy.
