# Track C — source-exact physical → composable coherent index adapter

17 November 2026. English mathematical proof committed **before** Lean.
Starting source: Lean main \`4c0f5602754340e0ef82bc023a9c25824b1149c1\`,
which already includes verified merged Track C PRs #288, #291 and #292.
This work is original Track C, manuscript issue #25.

## Actual gap from the adversarial progress audit

The real physical theorem
\`Kk.finiteNumericH_constructed_old_new_coherent_source_index\`
(\`Kk/ConstructedPhysicalOldNewSourceIndex.lean\`) **constructs** two
genuine AlgorithmRuns from concrete old/new physical numerical-H+ data
and nested finite source-index universes with an injective map φ.
It proves literal old Kpt node identity, old→new live-cut preservation
for cuts c<oldTop, exact old/new source universe coverage,
complete same-node old/upper L+/E type records, and uniqueness of φ.

The separately verified composition theorem (\`Kk/CoherentKptIndexComposition.lean\`,
merged PR #292) packages these data as a structure
\`CoherentKptIndex family oldNode newNode oldLive newLive horizon\`.
There is no source-exact export from the PHYSICAL constructor
into the new composition API. Failing to make the bridge explicit
would leave a formal multi-stage coherence argument with unproved
premise that each genuine physical stage supplies a
\`CoherentKptIndex\` value.

## Target theorem A: physical coherent index adapter

Under the **exact hypotheses** already required by the physical
constructor (old/new original binary/unary/diagonal prefix
equality, \`N≤M\`, numerical block/chronological guards, old and new
whole-H+ forbidden avoidance, old finite original-prefix seed
representation, and genuine old exhaustive Kpt run with an old
top seed), construct actual old/new AlgorithmRuns together with
finite old/new Kpt source-index universes, their live-cut masks
and **one coherent index structure** of horizon \`oldTop\`.

The theorem preserves the old/new source-index EXHAUSTIVENESS
equivalences at every old cut as part of its conclusion, not just
the injection. The adapter is obtained by directly destructuring
the previously verified physical constructor and building
\`CoherentKptIndex\` from the five actual data objects:
\`map=φ\`, \`map_injective\`, \`same_node\`,
\`live_forward\`, with the exact same old/new index universes.
No new physical extension is assumed as a witness, and no
unproved reduction to ordinary graph-age shadows is used.

**Old → new only.** New-index nodes may not have old antecedents,
especially at genuine K4 auxiliary interesting cuts 10 and 22.

## Target theorem B: path-independent finite index labels

For two coherent index maps \`f,g:A→C\` with the same concrete
source/final Kpt node enumerations and a **genuinely injective final
node enumeration**, prove \`f.map=g.map\` by applying final-node
injectivity to
\`nodeC(f(i))=nodeA(i)=nodeC(g(i))\` for each source i.

From this, prove commuting triangles and diamonds of finite
physical source-index maps: any two composable paths with the
same initial and final index universes and same final literal
node enumeration give the SAME map on the old names. In particular
the composite is independent of arbitrary choices of intermediate
finite enumerations, PROVIDED those intermediates actually match
at the interfaces. This is a stronger coherence assertion than
bare composition but not a global source orbit.

## Optional exact reverse-coverage criterion (conditional)

For a pair of coherent maps \`f:A→B\`, \`g:B→A\` with **both**
endpoint node enumerations injective, prove that the underlying
maps are inverse and therefore bijective; old-live and new-live
bits are equivalent for any cut below the MINIMUM horizon.

This isolates precisely what NEW→OLD source coverage would buy.
It is NOT supplied by genuine one-way physical root extension;
such a reverse map would often be false because truly new
dependent nodes appear. It is only an interface one might later
verify between two separately normalized SAME-diary occurrences,
and even then both must be represented in one common actual
normalized Kpt node universe (not just isomorphic L-reducts).

## Hostile tests / non-theorems

1. Full physical initial column agreement is an explicit old
   hypothesis and not implied by equal selected-front graph ages.
2. Whole-H+ forbidden avoidance is required on BOTH old and new
   physical structures. It is not inferred by the adapter.
3. There is a REAL old top seed and a numerical height inequality;
   no phantom top is admitted.
4. The new stage seeds exactly one admissible NEW Kpt original,
   not all of its ancestors (the old all-prefix construction
   forces spurious I1 levels).
5. Cut live transfer is only for c<oldTop; no extension to
   c=newTop or arbitrary later scan levels.
6. Every Kpt original's complete E and negative/positive L
   atoms are retained by SAME NODE, not just ordinary graph age.
7. I2 forks can have multiple upper L+ types sharing one old
   source; injectivity must not collapse their Kpt nodes.
8. The new finite source index may have strictly larger
   cardinality than the old index; **surjectivity is FALSE in
   general** and must not be inserted as a premise of forward
   transport.
9. Commuting paths require the same actual final node
   enumeration and injectivity; equality of abstract
   labelled/front diary records is not enough.
10. Two-way coherence for nested ROOT GROWTH is generally NOT
    guaranteed and can be impossible; it is an independent
    conditional criterion, not a discovered property of #288.
11. Empty old source is allowed by the abstract path lemma;
    no hidden cardinality assumption.
12. The unique coherent map can have arbitrary horizon t;
    uniqueness from node identity does NOT depend on live-cut
    transport, though that property is necessary for stage use.
13. Horizon min(t,u) is essential when composing independent
    source chains; using max would be unsound.
14. This is Fin-index-map coherence, not an SMTree
    shape-preserving MMap; do not conflate index embeddings
    with monoid inverse-source orbit maps.
15. The construction remains ONE finite stage, even when
    the resulting maps are subsequently composable for every
    finite number of separately supplied physical stages.
16. No unbounded canonical resolved diary, diary-uniform
    finite carrier, reverse no-novelty, fully labelled common
    orbit, or big Ramsey-degree theorem is established.

## Process / checks

- Implement a Track-C-owned independent Lean module importing the
  existing verified concrete source theorem and CoherentKptIndex.
- Assert exact fully qualified \`#check\` and \`#print axioms\` for
  every new public endpoint in a separate audit module.
- Require an exact-head module build and independent full
  \`lake build\`; only after both pass consider integration.
- Preserve black manuscript text, old validation pins and
  global PENDING statuses. If manuscript changes are proposed,
  add narrowly scoped OLIVE notes/BLUE source pins only.
