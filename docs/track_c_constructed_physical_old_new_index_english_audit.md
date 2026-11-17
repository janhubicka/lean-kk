# Track C — derived coherent physical OLD→NEW finite Kpt source index

17 November 2026, English mathematical proof FIRST, prior to Lean. This
strengthens the already merged one-stage physical bare/full source
construction, and consumes the independently verified Track E E63
\`finiteNumericH_actual_nested_runs_coherent_source_index\`.

## Actual geometric input
Two finite numerical-H+ sources with base graphs K,L, old/new finite
carriers N≤M, fixed generation k and old base cutoff b, with:
* complete K/L old original binary/unary/diagonal L atoms identical
  on indices <b, including false bits and BOTH directions;
* N≤hPosition k b 0 and chronological new original top bound
  N≤T, where T=hPosition k (j−1) k+1;
* actual target w=hPosition k j k<M with k>0 and j>0;
* the normalized forbidden family avoided by BOTH complete actual
  finite numerical-H+ L reducts;
* old Kpt initial seeds X genuinely represented by one old physical
  original-prefix pool U;
* old \`HasPhysicalExhaustiveKptRun family X oldTop\`, including a
  REAL old seed at oldTop and a complete finite old source index.

No assumption of future diary canonicality or source orbit.

## Statement

For the new physical BARE Kpt original seed family
\`Y=X∪{kptOriginal_L(w)}\`, set \`T=hPosition k (j−1) k+1\`.
There exist two GENUINE AlgorithmRuns
\`Rold: AlgorithmRun family X oldTop\` and
\`Rnew: AlgorithmRun family Y T\`, and a finite exhaustive old
Kpt source index, a finite exhaustive new Kpt source index,
Boolean live masks for both, and an **injective map**
\`φ : Fin oldParams.card → Fin newParams.card\` such that

1. For every old source name i, newNode(φ i)=oldNode(i):
   **same actual fully dependent Kpt node**, not just same old L.
2. For every cut c<oldTop the old/new live masks represent
   exactly the TRUE pre-cut full closure nodes of their respective
   runs.
3. If an old node is live at c, its image φ i is live in the
   newer source at c. This is *one-way inclusion*.
4. For every old i,c, both **full old** and **full assigned upper**
   L+/E raw type nodes at c are exactly equal between the names;
   this includes all negative bits, fake coordinates and parameters.
5. The map φ is unique among all index maps preserving every
   actual old source node, because the new enumeration is injective.

The number of new names is finite but may be larger than the old
number and depends on physical carrier M. No reverse new→old
matching or uniform BRD source cardinality is asserted.

## Proof

1. Unpack the actual old \`HasPhysicalExhaustiveKptRun\` witness:
   the true old AlgorithmRun and the genuine old top seed x∈X.
2. Invoke the already verified Track C physical bare-root
   constructor \`finiteNumericH_bareTopRoot_construct_exhaustive_run\`
   using inherited-level parameter I=Rold.I0. It gives a genuine
   bounded new root run Rnew at EXACT physical top T.
3. Independently invoke
   \`finiteNumericH_bareTopRoot_seeds_represented_bounded\` with
   the same I. It constructs ONE actual new original-prefix
   pool V satisfying Y⊆ambientPrefixPool_L(V).
   Because X⊆Y definitionally, X is represented by the
   SAME new pool V, with no external hX hypothesis.
4. Invoke
   \`finiteNumericH_old_physical_top_le_new_chronological_top\`
   using the REAL old top seed, old prefix certificate
   and N≤T, deriving oldTop≤T from the physical data.
5. Apply Track E's already source-checked exact E63 theorem
   \`finiteNumericH_actual_nested_runs_coherent_source_index\`
   inside the ONE normalized Kpt tree \`family\`, with:
   physical model L, generation k, carrier M, shared pool V,
   seed sets X⊆Y, two TRUE runs Rold and Rnew and derived top
   inequality. E63 constructs both exhaustive indexes and
   the *single* injective old→new map with exact cut masks
   and full old/upper L+/E ancestor atoms.
6. Carry that existential tuple through unchanged. No
   arbitrary naming bijection, graph-age shadow or
   full inverse monoid orbit is introduced.

## Hostile mathematical checks

1. The common old physical Kpt nodes are fixed as nodes in
   \`AdmissibleKptNode family\`, independent of whether the
   old base graph was K and the new base graph L. The
   complete old-column fidelity is needed to justify their
   real source-prefix representation in L.
2. The source-map φ depends on the chosen finite enumerations
   but is unique once both enumerations are fixed; it is not
   a canonical numbering of arbitrary diary occurrences.
3. The old top seed cannot be replaced by formal \`topI={top}\`;
   otherwise oldTop≤newTop may fail.
4. No old parameter is discarded: Y contains X, including
   any legitimate old dependent seed in X.
5. The new O contains exactly ONE genuine original, NOT its
   ancestor prefix set, whose direct insertion forces
   spurious I1 at every lower cut.
6. Full normalized forbidden avoidance is required for both
   actual finite numerical-H+ structures; selected age
   consistency alone does not suffice.
7. The old and new base models may differ on new columns,
   but complete old binary/unary/diagonal atoms coincide
   below b and old actual real coordinates lie below the
   old block frontier.
8. The SOURCE index consists of full Kpt nodes. Matching
   only the ordinary-L reduct would lose auxiliary E and
   assigned dependent parameter types.
9. The injection is one-way: new-only I1/I2/I3/B3
   microevents are genuine and may survive, notably K4
   auxiliary cuts 10 and 22.
10. Cut masks are only compared in the OLD scanned range c<oldTop.
11. Distinct numerical physical base models live in the SAME
    normalized abstract Kpt tree; comparing unrelated
    label maps between two different diary occurrences is
    NOT justified by this theorem.
12. The old and new monoid maps F_i need not be equal.
13. Local source type agreement does not give a uniform
    finite source-size bound in terms of the target A.
14. Source node identity preservation here is stronger
    than equality of multisets of crossing spectra; it is
    insufficient to prove reverse new→old no-novelty.
15. The proof does not certify a recurrence realizing all
    canonical graph-age covers along an unbounded Henson graph.
16. It does not establish the equality of fully labelled
    inverse sources of two distinct diary occurrences or
    an exact big Ramsey degree.

## Lean gate and manuscript rule

Formalize in a separate Track C file using the already
merged E63 source module, independently compile it and
check its single exact public theorem under only standard
transitive axioms; run a full project build. No manuscript
global marker promotion before exact-head CI success. Keep
black prose frozen and K4 regression intact.
