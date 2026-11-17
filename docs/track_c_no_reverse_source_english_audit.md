# Track C — adversarial obstruction to reverse source transport

17 November 2026. English-first proof and scope audit **before** Lean.

## Why this matters

Verified Track C physical root growth constructs a coherent
OLD→NEW Kpt source-index embedding, and PR #304 verifies
a **conditional** two-sided equivalence theorem if coherent
source-index maps in both directions are supplied.

There is a tempting but WRONG next proof route: try to
construct the reverse NEW→OLD coherent map along actual
genuine growing numerical-H+ root stages. A new root may
contribute a fresh legitimate full Kpt node (or additional
I1/I2/I3 auxiliary nodes) which was NOT in the old source
universe. A reverse coherent map must identify every
new Kpt node with a literally equal OLD node. This is
impossible whenever one genuine new node is missing old.

The obstruction should be formal and visible at the precise
invariant interface, not merely a narrative warning.

## Theorem A: fresh physical source node rules out reverse map

Let old index names A=Fin P and new B=Fin Q enumerate
actual nodes \`oldNode : A→AdmissibleKptNode family\` and
\`newNode : B→AdmissibleKptNode family\`, with arbitrary
old/new Boolean live-cut records. Suppose there exists
\`j:B\` such that

  ∀ i:A, newNode(j) ≠ oldNode(i).

Then no \`CoherentKptIndex family newNode oldNode
newLive oldLive horizon\` can exist.

**Proof.** A hypothetical reverse map g sends j to an
old index g(j) and its definition requires

  oldNode(g(j)) = newNode(j).

This contradicts the fresh-source hypothesis with i=g(j).
No assumption about the level horizon, selected graph age,
forbidden-family avoidance, or selected diary is involved.

## Theorem B: strict index growth rules out reverse map

If Q>P, there is no coherent map from a Fin Q source
to a Fin P target: such a map is injective, implying
Q≤P by finite cardinality. This does NOT prove Q>P for
every physical root extension; that numerical inequality
requires separate hypotheses on the actual source universes.

## Adversarial cases

1. The existence of ONE genuinely new source node, even if
   it only participates at an auxiliary K4 q2 cut, prevents
   a reverse literal-source-name map of the ENTIRE new index.
2. A new node can have an OLD ordinary-L reduct but a
   different E bit/parameter name; matching only its
   L reduct is NOT enough for source identity.
3. A new index may contain extra *nonlive* names; this
   still defeats a reverse map of the entire index.
   If one only wants live-at-a-cut reverse transport,
   restrict the named universe first and prove that
   restriction satisfies its own explicit invariants.
4. A forward old→new injection can coexist with a
   fresh-node obstruction to any reverse map. Therefore
   the conditional two-way theorem from PR #304 cannot
   be applied automatically to real root growth.
5. Equal cardinalities alone do not establish two-way
   coherence: they can give a set bijection without
   preserving literal Kpt node identity or live masks.
6. A strict cardinality increase is SUFFICIENT for
   reverse failure, not a necessary condition; fresh
   nodes can replace old nodes even with equal counts.
7. The converse is false: absence of a *fresh* new node
   need not give a reverse coherent map if new index
   enumeration is noninjective or its live history
   is incompatible. State only the forward obstruction.
8. Unrelated Kpt presentations of two same-diary
   occurrences are NOT in a common literal source
   universe. To compare them one must first specify a
   faithful normalization/identification of all dependent
   Kpt nodes and their full L+/E source labels; this
   cannot be inferred from selected graph-age records.
9. Neither theorem produces an explicit physical stage
   with strict cardinality growth; do not overclaim.
10. The existence of the genuine K4 cuts 10 and 22
    remains a regression against selected-shadow
    projection; the new abstract theorem neither
    enumerates nor removes these cuts.
11. Source maps are Fin-index injections, not
    successor-tree monoid maps; do not misinterpret
    the obstruction as a statement about MMap actions.
12. The upper bound/labelled inverse orbit problem
    remains open. In particular, the target for
    multiple diary occurrences should be a common
    labelled *representation* or orbit under the
    successor monoid, not reverse inclusion into
    every preceding finite physical source index.

## Integration

Create a new Lean module with exactly two named theorems,
a strict exact-head direct-build/axiom gate, and independent
full project CI. If successful, annotate the existing
Track C OLIVE TODO as a mathematically certified negative
boundary. Do NOT alter black manuscript paragraphs or
promote global BRD/diary claims; a BLUE interface is the
strongest appropriate marker.
