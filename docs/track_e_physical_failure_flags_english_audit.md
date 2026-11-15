# Track E E55 — the two exact Boolean failure flags at a physical cut

**15 November 2026. English first; no new Lean theorem claimed until CI.**
This continuation is stacked on E54 PR #220, not an independent substitute
for its still-pending exact-head certification.

## Scope and precise statement

Fix a normalized admissible Kpt source with forbidden family \(\mathcal F\).
For old and new parameter-closed physical node sets \(Z_0,Z_1\) and one
**aligned literal source-coordinate** cut \(c\), define the flags

\[
 T_c(Z_0,Z_1):=
  \mathrm{I1}(Z_1,c)\ \land\ \neg\mathrm{I1}(Z_0,c),
\]
\[
 P_c(Z_0,Z_1):=
  \neg\bigl(\operatorname{Cross}_{L^+}(Z_1,c)
      \subseteq\operatorname{Cross}_{L^+}(Z_0,c)\bigr).
\]

Cross is the canonical **complete** same-node dependent old/upper L+
crossing *relation*, not a positive ordinary-L type spectrum. It
retains negative ordinary-L atoms, auxiliary E and competing I2 forks.

**Lemma E55.1 (exact Boolean normal form).** The physical predicate
NewRootNoNoveltyAtCut \((Z_0,Z_1,c)\) fails if and only if
\(T_c(Z_0,Z_1)\lor P_c(Z_0,Z_1)\).
This is a direct propositional equivalence from the established definition:
\(\neg[(A\Rightarrow B)\land C]
\iff(A\land\neg B)\lor\neg C\).
The equivalence is neither a new geometric construction nor an
unconditional interestingness theorem.

For physical source families \(Z_0(c),Z_1(c)\), an old selected-level
function \(I(c)\), and oldTop \(h\), define the **intrinsic finite set**

\[
 \mathrm{PhysBad}
 = \{c<h:c\notin I(c),\ T_c(Z_0(c),Z_1(c))
                                  \lor P_c(Z_0(c),Z_1(c))\}.
\]

This is finite because it is a subset of \([0,h)\). Unlike E54's
finite-index Bad, PhysBad does not mention any arbitrary index.

**Lemma E55.2 (indexed = physical).** If exact finite live Kpt
indices represent the complete old and new sources at every \(c<h\),
then E54's \`kptCanonicalOffPlanBadCuts\` equals PhysBad, element by
element. This uses E54's bidirectional indexed/physical equivalence
and E55.1. In particular, all complete finite indices of the
same actual sources give the same PhysBad. This does not construct
a diary-controlled source or choose a uniform cardinality.

**Lemma E55.3 (minimal two-flag cross-occurrence criterion).**
For TWO pairs of actual old/new source families in one normalized
Kpt tree with the same oldTop, suppose at **every c<h**:
1. the old-boring indicator \(c\notin I_0(c)\) agrees with
   \(c\notin I_0'(c)\);
2. the terminal-failure flag \(T_c(Z_0,Z_1)\) agrees with
   \(T_c(Z_0',Z_1')\);
3. the complete-pair-inclusion-failure flag \(P_c(Z_0,Z_1)\)
   agrees with \(P_c(Z_0',Z_1')\).

Then the corresponding intrinsic physical bad-cut *Finsets*
are identical. Proof: expand membership in the two Finsets
using E55.1 and the three pointwise equivalences. No bijection
between finite source indices is required, no equality of full
crossing relations is required, and the actual physical source
sets themselves can differ.

This is **not** the diary-to-geometry application: no assumption
above is derived from equality of a macrodiary. The source cut
coordinates are aligned as an explicit input and the premise
requires full L+ pair inclusion flags, not reduced age equality.

## Adversarial tests (16)

1. If new has a cut-terminal and old does not, terminal flag true.
2. If new has multiple terminals but old has any one, flag false.
3. New-to-old pair inclusion is ONE-SIDED; no reverse cover is assumed.
4. Pair coverage has same-node old/upper witnesses at every fork.
5. Ordinary L positive cut-star equality is insufficient.
6. Keep auxiliary E and negative ordinary-L atoms in raw types.
7. A failing full physical crossing can have multiple witnesses;
   the flag records only its existence, not multiplicity.
8. Equal flags do not imply crossing **relations** equal.
9. Equal flags do not imply underlying **Kpt node sets** equal.
10. Equal flags do not imply source-parameter meet recipes equal.
11. Equal flags do not imply assigned successor types to *labels* equal.
12. A label swap with the same unlabelled pair relation is invisible.
13. The meet-closed closure blindness regression shows even all
    cut-local verdicts can fail to reconstruct distinct node sets,
    under its hypotheses; it is NOT two resolved Henson diary runs.
14. Restrict comparisons to source-coordinate cuts c<h; numerical
    positions from two unrelated generations are not normalized.
15. No uniform bound on |PhysBad| from |diary| or ell is proved.
16. A full-labelled monoid orbit needs synchronized event/microevent
    participation, exact Kpt seed/parameter recipes, assigned upper
    L+ characters and compatible genuine outgoing MMaps, none of
    which is provided by the three Boolean flags.

## Do not duplicate existing orbit lemmas

\`Kk.FullEventIndexedOrbitBridge.full_event_source_eq_of_local_reconstruction\`
already proves that two full event-indexed records agree when selected
nodes, parameter nodes, presence masks and event frames agree and
their assigned types are reconstructed by the **same** functions.
\`full_event_source_common_selected_and_parameter_targets\` then
supplies common labelled source/parameter targets under actual
monoid maps. E55 does not repropose these conditional interfaces.

The real gap is a geometric theorem supplying equality of source
atoms and recipes, compatible event frames and same reconstruction
functions for distinct occurrences of one diary. E55 reduces only
the **bad-cut-support** part to the three flags, and cannot discharge
the stronger source-record and monoid-orbit hypotheses.

## Validation procedure

1. Compile standalone module \`Kk.TrackEPhysicalFailureFlags\`
   against the checked E54 branch.
2. Audit every new public theorem through a strict exact-head
   \`#print axioms\` gate with allowed axioms only
   (propext / Classical.choice / Quot.sound).
3. Require independent ordinary full \`lake build\`.
4. Keep PRs stacked and drafts until the direct gate is green;
   no new green or blue manuscript marks without proof/assumption
   checks and no edits to frozen black mathematics.
