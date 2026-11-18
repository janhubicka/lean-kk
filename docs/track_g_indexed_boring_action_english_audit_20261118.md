# Track G — indexed old-to-new Kpt boring action with complete L+/E records

18 November 2026. English proof written FIRST; proof targets the actual
physical finite-index interface rather than abstract diary labels.

## Verified inputs

- Track G PR #331: actual boring-block ancestor action and two-run overlap.
- Track G PR #336: for literal nested Kpt seeds, a real old top seed,
  two truly boring old-range intervals, all surviving old complete
  source ancestors have identical actions under the old/new factors.
- Track E E60 `crossheight_old_live_Kpt_full_Lplus_records_retained`:
  from exact finite old/new source indices at every old cut and
  physical seed inclusion, each old live index has some new live
  index representing the IDENTICAL actual Kpt node, with the
  COMPLETE old/upper L+/E records unchanged.

## Proposition D — finite-index old-name naturality

Fix normalized Kpt family, nested seed sets X⊆Y, oldTop≤newTop
with an actual x∈X of level oldTop. Let Rold and Rnew be actual
AlgorithmRuns and fix cut<oldTop and low≤cut+1. Assume EVERY
stage [low,cut+1) is genuinely boring in both runs on their OWN
full pre-cut closures. Let oldNode:Fin P→Kpt, newNode:Fin Q→Kpt
and Boolean oldLive,newLive maps enumerate EXACTLY the complete
pre-cut sources of both runs at every cut <oldTop.

Then ∃ Dold,Dnew : genuine total MMaps, factoring each run
between low and cut+1, such that for each old index i with
oldLive(cut,i)=true and level(oldNode i)≥cut+1:

  ∃ new index j, newLive(cut,j)=true, newNode(j)=oldNode(i),

and the old/new complete dependent L+/E old/upper records of these
indexed Kpt nodes are equal, AND

  Dold(ancestor(oldNode(i),low))
       = Dnew(ancestor(oldNode(i),low)).

**Full proof.** Apply verified G336 once, producing global factors
Dold,Dnew and their equality on every eligible old complete Kpt
source node. For each old live i, exactness of hExactOld gives
oldNode(i) membership in the actual old pre-cut closure.
Apply verified E60 indexed-node retention to obtain j with
newLive(cut,j), literal newNode(j)=oldNode(i), and complete
old/upper L+/E record equality. The G336 restricted action
equality at c=oldNode(i), using the explicit level bound, yields
the last conjunct. The same two total factors work for ALL old
indices: they are chosen before the universal quantifier.

## Why this is useful and what it does not prove

This theorem simultaneously exports exact old-to-new physical
Kpt index matching, full auxiliary E and negative L records,
and strict action equality of the genuine accumulated monoid
factors on each eligible retained source ancestor. In particular
the finite indices can have different sizes/enumerations, and
new-only Kpt nodes are allowed. No reverse map is manufactured.

## Adversarial checks

1. The two factor witnesses are chosen once for the whole finite
   indexed source, not separately for every old index.
2. hExactOld and hExactNew enumerate FULL parameter-closed
   sources, not just selected original vertices.
3. The complete record equalities include dependent L+/E fields
   because E60 uses literal equality of actual Kpt nodes.
4. hExactNew is needed even if source inclusion is already proved:
   it gives an actual new index j for the same physical node.
5. No injectivity of the finite enumerators is assumed or needed
   for existential j; no uniqueness of j is claimed.
6. Each indexed factor equality uses the same cut coordinate
   in both actual runs; different diary reindexings remain open.
7. The old-top seed hypothesis is necessary for E60 retention.
8. hCut:cut<oldTop is essential; no assertion beyond oldTop.
9. A live old node may have level ≤cut; the factor action claim
   explicitly restricts to level≥cut+1.
10. The new index may represent an old node but also may include
    many new-only nodes; no new-to-old surjection follows.
11. Both runs must independently be genuinely boring at every
    cut in the interval; E60 inclusion alone does NOT force it.
12. G318 says actual selected-I endpoint equality is equivalent
    to all-boring; ordinary selected-front age equality is not.
13. K4 auxiliary cuts 10/22 are not silently removed.
14. The total monoid factors may differ on nodes outside this
    old enumerated source ancestor subset.
15. No uniform bound on exceptional intervals or factor label
    complexity follows from finite indexability of one stage.
16. No abstract labelled-source isomorphism between unrelated
    diary occurrences has been built, and no inverse Kpt orbit.
17. Relative corrected-(B3)-loss against continuation still open.
18. No infinite resolved copy or optimal BRD counts are claimed.

## Acceptance

Formalize only the precise imported E60+G336 theorem, not a new
axiom or generic presumption of source correspondence. Dedicated
exact-head Lake compile and one-name standard-only axiom parser gate
plus independent full Lean build; no manuscript global green claim.
