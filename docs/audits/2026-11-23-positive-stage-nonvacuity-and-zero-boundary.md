# Positive-stage consistency and the generation-zero boundary

## Status and scope

Read-only mathematical application review, 23 November 2026. The calculations
below were checked against the literal definitions and existing free-level
theorems. No new Lean theorem or compiler check is claimed for this example.
It establishes consistency of the repaired physical-stage hypotheses and
identifies a genuine boundary of extending them to generation zero. It does
not assert that the displayed level set is an AlgorithmRun stage or that this
small role graph is the manuscript's complete resolved-Q construction.

## A nonempty example with positive cut neighbours

Take k=2, N=29, and write `p(i,m) = hPosition 2 i m = 6*i + 2*m`.
Set `role 1 = .coded false`, `role 2 = role 3 = .coded true`, and every
other role to `.dummy`. Let the symmetric, loop-free base graph E have exactly
the two undirected edges `{1,2}` and `{1,3}`. All chronological role axioms hold:
dummy rows are zero, and there are no auxiliary roles. The two selected coding
bases are also independent. The tested base b=1 is non-dummy and omitted.

Use the actual finite model `A := finiteNumericH (normalizedGraphModel E) 2 29`,
the root cap `cap = 28 = p(4,2)`, and `U = {cap}`. For a simple arbitrary
physical stage choose `J = Plan = {16,22}`. Its exact original pool is
`Stage = {16,22,28}`. These are actual addresses in Fin 29.

| Address | Canonical base/generation | Role | Literal free level | L(6,address) | L(8,address) |
| --- | --- | --- | --- | --- | --- |
| 16 | (2,2), TOP | selected coding | p(1,2)+1 = 11 | true | true |
| 22 | (3,2), TOP | selected coding | p(2,2)+1 = 17 | true | true |
| 28 | (4,2), TOP | dummy root | p(3,2)+1 = 23 | false | false |

The free-level equations use `finiteNumericH_top_real_freeLevel` in
`SuccessorTree/V10/HTopRootFreeCut.lean`; they are not address-minus-one
calculations. The ordinary bits follow from `hNumericBinary_real_forward_iff`
and the two actual base edges.

At the positive lower cut `c = p(1,1) = 8`, all three names are genuinely
eligible: `c+1 = 9 ≤ 11,17,23`. The generation-zero coordinate is `q = 6 < 8`.
The root contract holds because the only bounded real presentation of 28 is
(4,2), whose role is dummy. The Plan contract holds because the only bounded
presentations of its two members are (2,2) and (3,2), both selected TOPs.
Uniqueness here is exactly `hPosition_injective_bounded`. Thus the repaired
contracts coexist with positive selected neighbours and a nonempty eligible
stage; they do not force all relevant base rows to zero.

There is also a nontrivial pair satisfying the complete old-type premise:
`A.partialTypeAt 8 16 = A.partialTypeAt 8 22`. For each upper name, the only
positive ordinary atom from an old coordinate below 8 is at coordinate 6;
the reverse ordinary column agrees by symmetry. Incoming E from every old
coordinate is true since both free levels exceed 8, outgoing E is false,
all singleton and self facts agree, and the internal socle is the same A.
These exhaust the fields of `PartialTypeWithE` and its `RelationalPrefixType`.
Their complete next types at 9 also agree, since both new ordinary bits at 8
are true and the eligible E bits agree. The root's old type at 8 differs from
both selected TOPs at the already old coordinate 6.

The ordinary finite numerical-H graph is bipartite, with real copies of base
1 on one side and copies of bases 2 and 3 on the other. It is therefore also
loop-free, symmetric, and triangle-free. Thus there is no obstruction here
from the Henson forbidden graph conditions at ell=3, k=2.

## What this does and does not show about an AlgorithmRun

The displayed J is an arbitrary level set used by the literal physical-stage
constructor. It is not claimed to equal `Run.I 9`. In particular, a run from
the literal cap/TOP seed family has top=23 and must retain that top level;
the simple set `{16,22}` does not include it.

One may enlarge both J and Plan to `{11,16,17,22,23}` without changing Stage
or any calculation above. The added addresses are odd, so they have free level
zero and do not contribute selected originals; the positive-free-level Plan
guard also excludes them. This enlarged set accommodates the top and the
free levels of the two selected originals, but no exact Run realization is
asserted here.

For the literal TOP seed construction, blocks `{2,3}` fit below cap's actual
free level 23 because their TOP addresses are 16 and 22. Source representation
and absence of a seed at c=8 therefore have the intended concrete meaning.
The remaining actual-run obligation is still to establish the displayed
higher-stage inclusion into the proposed Plan, using the genuine run. The
physical example is not a substitute for that descending construction.

## The same data refutes an unsupported generation-zero extension

Now test `c0 = p(1,0) = 6`. All three names remain eligible. Below 6 the only
real base is the initial dummy base 0, and odd coordinates have no ordinary
edges. Consequently all three complete old types at 6 are equal: their
ordinary old columns are zero, incoming E is true throughout the old prefix,
outgoing E is false, and all singleton/self and common-socle data agree.

At the new coordinate 6, however, the two selected TOP bits are true and the
root bit is false. Their complete next types at 7 differ. Thus the bounded
root/Plan contracts and chronological role axioms alone do not imply
generation-zero whole-stage coherence. Block convexity modulo dummies also
holds vacuously in this example, so that condition alone cannot repair the
gap. No splitting among selected TOPs holds here: their new bits are both
true. It fails to control comparison with the actual zero-old root type.

This is a counterexample to extending the new local theorem to g=0 under
its present hypotheses. It is not a counterexample to a stronger resolved-Q
construction statement whose additional geometry has yet to be supplied.

## Precise remaining construction obligation

At every tested positive generation-zero cut `c = hPosition k b 0`, the
construction must prove separation for every pair of actual stage originals
v,w satisfying all of the following: both belong to
`hStageOriginals K k N U (Run.I (c+1))`, both are genuinely eligible at c, and
their ordinary c-bits differ. Their complete old types at c must then differ.
Equivalently, equal complete old types must determine the c-bit on the entire
eligible stage. This is the goal to derive from construction data, not a
replacement hypothesis that would itself finish the structural argument.

The quantifier must include root originals and retained auxiliary originals,
even when they are not members of a marked selected tuple or already known
to represent a strictly crossing closure node. The I1 normal form needs the
complete original stage before crossing-source membership has been proved.

For an omitted non-dummy base, the checked block-separation lemma makes the
old ordinary columns of later retained auxiliary bases zero. In the intended
loop-free normalized graph, this suggests two explicit construction duties:

1. Among all relevant future selected TOP originals in the actual stage,
   equality of their old base profiles `(E p j)_{p<b}` must determine `E b j`.
2. A selected TOP with `E b j = true` must be separated from every actual
   eligible zero-old source class. With an eligible dummy cap this requires
   a genuinely old positive coordinate, equivalently an earlier base p<b
   with `E p j = true`.

The second duty is missing from a selected-TOP-only no-splitting assertion.
The example above violates exactly that duty at b=1. A proof that these two
base-profile duties cover every actual finite source name, together with the
same seed and source-representation gates used in the positive-generation
lift, remains a separate generation-zero construction argument. The chosen
corrected-B3 age verdict and the global descending Plan inclusion remain
additional obligations for full nonselection and the characterization.

