# Track F — order-free source/target-prefix fibre refinement

17 November 2026. English proof and hostile audit **before Lean**.
This targets the first concrete non-root part of compatible-rank transport,
without assuming a diary theorem or that an induced embedding is
monotone in the original enumerations.

## Lemma 1: every injective enumeration map leaves each target prefix

Let e:N→N be injective and H finite. Then there is M such that
x≥M implies e(x)≥H.

Proof: for each i<H with nonempty fibre e^{-1}({i}), choose its unique
preimage x_i; for an empty fibre choose 0. Let
M=1+max{x_i:i<H}. If x≥M and e(x)=i<H, injectivity forces
x=x_i<M, a contradiction. Note that M depends on e and H
and may be far larger than H. This is the exact replacement for
the invalid assumption that arbitrary induced Henson embeddings
preserve chronological enumeration.

## Lemma 2: cone-local monotonicity of rank largeness

Let u be a source type, and S,T subsets of its type tree. Assume
every descendant x≥u belonging to S also belongs to T (the
global inclusion S⊆T is NOT assumed). If S is n-large at u,
then T is n-large at u.

Prove by induction on n. Rank zero uses the source
descendant relation transitively. At successor rank, every
same-rank v≥u has a lower-rank w≥v carrying S largely;
the cone-local implication above w holds by transitivity,
and the induction hypothesis applies. This avoids an
unjustified global claim that an arbitrarily selected
finite-colour class contains only images beyond H: that
claim is true only after refining into the source cone
above the eventual-preimage bound.

## Lemma 3: the actual target-prefix colouring has a large fibre

Fix the actual Henson one-type preorder on the source graph
Esrc. Let S be any rank-n large set of source types at u.
Let Etgt be an arbitrary target binary table and e:Nat→Nat
an INJECTIVE original-index map. Fix H and the finite target
prefix colour

    c_H(x) = (i↦Etgt(i,e(x.level)), i↦Etgt(e(x.level),i))
              for i∈Fin H,

the actual two-directed-column colour defined in the
already verified coding-node module.

Choose M from Lemma 1, pad u by zeros to level max(M,u.level),
and use same-rank cone monotonicity of Large. Apply the
verified finite-colour partition theorem. Obtain a single
colour j and a same-rank node v extending the padding on
which the j-fibre of S is n-large.

Every source type x≥v satisfies x.level≥M and hence
e(x.level)≥H. Therefore by cone-local monotonicity of
largeness, the set

    {x∈S : c_H(x)=j AND e(x.level)≥H}

is n-large above v.

The existing Large.has_member theorem gives a genuine
source TYPE node x≥v in that set. If S is a subset of
actual coding nodes, x is an actual original-vertex code.
For a current source/target fibre S=A(targetOld) this
produces a nonempty rank-large image-prefix class, with
the target-cutoff and both orientations controlled.

## What the theorem does NOT prove

It does not yet build a target HensonOneType corresponding
to the chosen j. That requires an additional finite
K_ell-free graph-age certificate showing that the common
target prefix is admissible; one coding witness from the
fibre supplies that certificate when Etgt is normalized
Henson. Nor does it prove that the newly chosen target type
has source rank n: this will require the genuine richness
clique and the existing verified target-rank obstruction.

It proves neither complete multi-sort source/target profile
synchronization nor unavoidability of any diary.

## Hostile checks

1. An injective map can send a VERY late source original into
   a small target index; the proof bounds ALL such exceptions,
   not by claiming e(x)≥x.
2. Without injectivity, infinitely many source originals may map
   below H. The theorem must require injectivity.
3. The finite palette has BOTH directed columns. An arbitrary
   Boolean table need not be symmetric, even though Henson
   avoidance later implies it.
4. Source zero padding preserves rank and full old bit agreement.
   An arbitrary source extension may lower the rank.
5. The colour j only fixes a target prefix, not the full
   infinite target type or its rank.
6. The local S→T implication holds only above the chosen
   source refinement, not globally. The proof must use
   cone-local rank-largeness monotonicity rather than the
   unconditional global inclusion lemma.
7. A witness x from the colour class is only a genuine
   ORIGINAL vertex when S includes the IsCodingNode condition.
8. This is a single-source one-prefix statement. It does not
   create a common compatible refinement for several source
   sorts or decide edges among their future selected vertices.

## Lean acceptance

Prove the injective eventual cut-off, cone-local monotonicity
of recursive largeness, and monochromatic future target-prefix
rank-largeness with a genuine witness. Use no axioms beyond
the standard Lean ones and no unpublished global BRD statement.
Run exact-head build and named transitive-axiom checks.
Keep the manuscript's complete transport and lower-BRD
validation marks pending.