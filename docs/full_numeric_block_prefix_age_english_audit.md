# Track A — literal full numerical-H block prefix and exact original-age equality

**15 November 2026. English mathematics and hostile audit BEFORE Lean.**

This continuation is stacked on the independent Track A
`FullRealGenerationCapacity` PR #207. Its base theorem states
the TRUE directed ordinary-L clique capacity among all
`k+1` real generation copies of a finite set of originals equals
that set's original E clique capacity. The current step upgrades
from the *real-copy pool* to the **LITERAL full numbered H
prefix**, including every odd fake coordinate. It is not
valid at a partial cut inside a reserved original block.

## The exact complete-block cut

Fix a numerical-H height k and old original prefix length b.
Let
  m := hPosition(k,b,0) = 2*(k+1)*b,
  Real := Copies_k([0,b)),
  Odd := {z<m : z mod 2 = 1}.

Then, as literal FINITE SETS of actual numbered H coordinates,

  [0,m) = Real ∪ Odd,
  Real ∩ Odd = empty.

Proof: every numeric coordinate is either odd 2a+1 or
even `hPosition(k,i,q)` with q≤k, by the already
verified `numericCoordinate_odd_or_real`.
If z<m and z=hPosition(k,i,q), then i<b:
otherwise b≤i and
  m=2*(k+1)*b ≤ 2*(k+1)*i+2*q=z,
contradiction. Conversely if i<b, the block-order
lemma gives iota(k,i,q)<iota(k,b,0)=m.
All real positions are even, hence cannot be in Odd.

This covers k=0, b=0 and all intervening fake vertices
without a selected-shadow simplification.

## Complete physical old-to-future sort columns

Let c(i,t) be ANY complete old-original-to-future
type-column function, and let `orig_k(z)` decode
the unique original of a bounded real coordinate.

Define a TOTAL typed column on the numbered old H prefix:
  Col_{k,b}(z,t) =
    c(orig_k(z),t)  if z∈Real,
    false           otherwise.

For z in Odd the column is identically false. This matches
the verified exact odd dummy **ordinary-L** columns to
later selected top copies. It does not mean odd fake vertices
have zero auxiliary E incidences in the full H+ language.

For every admissible nonempty future type support U, the
FULL old common-neighbourhood is literally

  {z<m : ∀t∈U Col_{k,b}(z,t)=true}
    = Copies_k(R_b(U)),

where R_b(U)={i<b:∀t∈U c(i,t)=true}.
The two directions use exact real decoder and the
nonemptiness of U; odd dummies fail the column test at
any t∈U. No additional numeric vertices are overlooked.

## Exact age equality

The full old numbered prefix has ordinary L table
  L := (finiteNumericHL(normalizedGraphModel E) k M).binary.

Assuming E symmetric (as for a genuine Henson graph),
the separately verified mixed-generation projection shows
  cap_L(Copies_k(R_b(U))) = cap_E(R_b(U))
for EVERY U.

Therefore pointwise on ALL admissible supports

  finiteOldColumnRawBound(L,ell,d,[0,m),Col_{k,b})
    = finiteOldColumnRawBound(E,ell,d,[0,b),c).

The normalized integer graph-age canonicalizer and feasible
integer vector family are also EXACTLY equal, without
assuming that either raw function is a positive age.

This is the desired **complete-generation numeric prefix
old age = original old age** adapter. In a genuine finite H
carrier, additionally require m≤M: then every coordinate
z<m is a REAL physical vertex (odd fake or real generation).
The Boolean formulas alone are total on Nat even without
that carrier cutoff.

## Adversarial limitations

1. The cut is exactly at the start of original b's block.
   At a middle-generation cut inside a reserved original
   block, the real-copy pool is incomplete: the full capacity
   equality does not apply.
2. Real copies of one original never contribute multiple
   members to a numerical directed clique, by the literal
   generator. Multiple generations do not increase capacity.
3. The lower bound uses the TOP-generation real copies, not
   arbitrary equal non-top generations whose gate can be shut.
4. Every odd fake coordinate is present in the literal set
   [0,m), but its ordinary binary L crossing bit to a selected
   top original is zero. It can still have nontrivial
   auxiliary Kpt E incidence.
5. The common-neighbourhood equality needs U NONEMPTY:
   if U were empty, all odd fake coordinates pass the vacuous
   all-type test, and equality with a real-copy pool fails.
6. The original E is symmetric in the current full Henson
   use, but positive real-edge projection itself is
   valid even without that symmetry.
7. Zero raw age values are permitted in the equality;
   positivity of a genuine canonical age needs separately
   checked singleton eligibility.
8. Exact typed columns on original i must extend to ALL
   real generations q≤k; the finite pinned future
   result #169 proves this for actually selected later
   top copies, but only under its explicit geometric
   compatibility hypotheses.
9. The proof compares the WHOLE old reference prefix,
   not a selected set of old real addresses.
10. The cutoff's numerical value `hPosition(k,b,0)`
    must be below the carrier limit M when claiming a
    literal finite H substructure.
11. At an intermediate reserved pivot, use the already
    verified exact nonconsecutive reserved prefix capacity
    and conditional whole-prefix gluing theorem instead;
    do not replace it by the completed-block identity.
12. Equality of old age functions does not construct
    a coherent infinite diary schedule or prove that
    the pre-stage graph-age record equals the intended
    `upper` at every step.
13. Complete old ordinary L still does not settle
    auxiliary H+ parameter closure, corrected B3,
    common labelled source orbit, or BRD occurrence
    factorization.
14. b=0 yields empty numeric prefix and empty real+odd
    pools; the raw age bound is ell-1 on all supports.
15. k=0 is legitimate: every original has one generation
    and odd dummy coordinates still occupy half the block.

## Formalization

On a stacked independent feature branch:
- `numericHFullBlockOddPool`;
- `numericH_full_block_prefix_exact` and disjointness;
- `numericHFullBlockOldColumn`;
- `numericH_full_block_common_neighbourhood_eq`;
- `numericH_full_block_raw_age_eq_original`;
- canonical graph-age and feasible-weight equality;
- `numericH_full_block_carrier_of_cut`.

Import the explicitly kernel-checked `Kk.FullRealGenerationCapacity`
once #207's exact-head gate passes. Require complete
module build, strict fully qualified named transitive
axiom reports, and full Lake build. Do not edit
central Kk.lean, strict axiom registry, validation
marks or frozen manuscript text. Track G owns
reviewed integration.
