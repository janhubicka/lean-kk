# Track G — cross-height boring-factor stability on the full old physical Kpt source

18 November 2026. English proof and adversarial scope audit written BEFORE Lean.

## Goal and existing verified ingredients

1. Track G #331 (merged as 04e23e30f01331cdc569992a0b980daa98721476)
   proves exact ancestor action for each genuine all-boring run block
   and agreement on literal overlapping full-source nodes.
2. Track E E60, `crossheight_actual_preCut_Kpt_source_subset`, proves
   physical old-to-new source inclusion at each cut strictly below
   oldTop for nested seeds X⊆Y in one normalized Kpt tree, with
   oldTop≤newTop and an actual old-top seed.

## Proposition C — old-to-new restricted boring-factor naturality

Fix a normalized forbidden family and X⊆Y of ACTUAL Kpt seed nodes
in that SAME normalized Kpt tree. Let Rold and Rnew be genuine
AlgorithmRuns of heights oldTop≤newTop. Assume an ACTUAL old seed
x∈X with lev(x)=oldTop. Fix an old-range cut cut<oldTop and
low≤cut+1. Assume EVERY stage i∈[low,cut+1) is genuinely boring
in BOTH runs, with the complete parameter-closed source used
by its own `IsInterestingAt` test.

The two runs have unique accumulated TOTAL monoid maps Dold,Dnew
between low and cut+1. For EVERY actual Kpt node c in the
complete OLD high-end pre-cut source

  c∈closure(S, Rold.I(cut+1), X)

with lev(c)≥cut+1, their restricted actions coincide:

  Dold(ancestor(c,low)) = Dnew(ancestor(c,low))
       = ancestor(c,cut+1).

**Full proof.** The old-range inequality cut<oldTop yields
cut+1≤oldTop≤newTop. Apply the merged Track G #331 two-run
physical-overlap theorem to Rold,Rnew on the same interval
[low,cut+1). It supplies genuine accumulated factors for
both actual runs and equality on any literal c in BOTH complete
high-end source closures. By verified Track E E60 and the
seed/height/top-seed hypotheses,

  closure(S,Rold.I(cut+1),X)
      ⊆ closure(S,Rnew.I(cut+1),Y).

Therefore EVERY eligible old c is also a new high-end source
node; apply the two-run overlap conclusion. The full ancestor
identity holds by the individual G331 ancestor-action results.
No new source-index bijection, inverse map, envelope-choice
uniqueness, or unproved labelled source transport is required.

## Interpretation

This is a genuine **one-way old-to-new** stability theorem for
the total monoid factors restricted to EVERY retained old complete
Kpt ancestor. As E60 preserves full dependent old/upper L+/E
records of IDENTICAL physical nodes (under its actual finite index
assumptions), the restriction is compatible with those records.
It says nothing about action on new-only auxiliary nodes:
reverse physical transport can fail by the already verified
fresh-source-node obstruction, and must NOT be assumed.

## Adversarial checks

1. E60 needs literal nested X⊆Y, not isomorphic abstract diaries.
2. The old real top seed is a genuine premise, not optional.
3. E60 cut parameter is strictly `<oldTop`; choose high=cut+1.
4. Do not assert source inclusion at the new high top beyond E60.
5. Both runs have independent genuine boringness hypotheses.
6. No full selected-front shadow may substitute for all-boring.
7. A new-only (I1)/(I2)/(I3) microevent can make new boringness
   fail, so the statement does not cover arbitrary growth steps.
8. The old lower ancestor is an actual Kpt node and is mapped
   to the SAME actual upper ancestor by both factors.
9. Factor equality is only on the old-ancestor subset, NOT
   as total MMaps across unrelated source domains.
10. Full dependent L+/E preservation uses literal node identity;
    do not infer a new-to-old complete index surjection.
11. The singleton x at oldTop only guarantees E60's gate;
    it does not construct an unbounded numerical-H+ resolved copy.
12. Empty intervals low=cut+1 are correctly handled by identities.
13. The lemma is meaningful at true physical old source nodes
    but may still be vacuous at a given cut if none has level≥high.
14. K4 aux cuts 10 and 22 remain genuine and cannot be
    absorbed into a declared all-boring block.
15. No bounded number/length of exceptional intervals follows.
16. No order-compatible reindexing between different diary occurrences
    or identified inverse-source monoid orbits is constructed.
17. Corrected full-(B3)-loss vs relative continuation remains open.
18. No independent lower colouring or exact Kk-free BRD count follows.

## Lean protocol

Import the EXACT merged G331 and E60 modules. The proof should be
only two calls: G331 two-run overlap and E60 literal source inclusion.
Compile the standalone Kpt source, and run the dedicated exact-head
one-name strict standard-only transitive axiom gate plus full Lean CI.
Do not promote a global manuscript claim. Add a narrowly scoped BLUE
source marker to olive text only after successful verification.
