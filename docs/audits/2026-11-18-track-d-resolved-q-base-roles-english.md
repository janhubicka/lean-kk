# Track D: resolved-Q chronological base-neighbour exclusion
18 November 2026. English proof and hostile audit BEFORE Lean.

## Mathematical setting

The manuscript inserts into a fixed Henson graph V finitely many
auxiliary blocks, each of size at most two, and isolated dummy bases.
Every Q base receives one unambiguous tag:
  Dummy;
  Coded(selected), where selected means in the fixed independent A;
  Auxiliary(block-id,retained), where retained means that whole block
  was selected for the proposed compressed diary.

We do NOT pretend this already constructs the countable Q or proves
that a true AlgorithmRun selects only proposed retained cuts.

Extract the four exact finite original-graph axioms:
(D) dummy bases have no edges to any Q base;
(CA) every earlier coded base is nonadjacent to every later
     auxiliary base (a block inserted after that coding);
(AA) members of *different* auxiliary blocks have no edges;
(B) two members of the SAME auxiliary block have the SAME
    retained flag (whole-block retention, not piecemeal).

Assume symmetric edge table E. Every later proposed kept source
base has one of the roles Dummy, Coded(true), Auxiliary(block,true).
No Coded(false) and no Auxiliary(block,false) is retained in the
selected source stage; this is a SEPARATE carrier hypothesis to be
derived from the descending Run.I(c+1) induction.

## Exact finite lemma 1

Let b<j, and suppose b is an OMITTED base, i.e. a dummy,
any coding base at an omitted generation/event, or an
auxiliary base with retained=false. Suppose j is a proposed
retained source base and E(b,j)=true.

Then j must be a selected Coded(true) base.

Proof: If j is dummy, (D) plus E symmetry contradicts positivity.
If j is a retained auxiliary, split b:
dummy -> (D); coded -> (CA); omitted auxiliary(block0,false) ->
if block0 equals block(j), axiom (B) gives false=true, impossible;
otherwise (AA) makes E(b,j)=false. Thus retained auxiliary is
impossible. Only a selected coding target remains.

The proof treats two members of one auxiliary block correctly:
whole-block retention is essential, and the inference to distinct
blocks is not true without axiom (B).

## Exact finite lemma 2

If b itself is a selected coded base (A independent) and
all distinct selected coding bases are nonadjacent, then b has
NO edge to any later proposed kept source base:
dummy -> (D); later selected coded -> A independence;
later auxiliary -> (CA).
This is the exact base-level reason a lower numerical generation
of a selected coding vertex has an empty positive selected cut-star.

## Explicit application boundary

At a genuine numerical H lower-real cut c=hPosition(k,b,g),
the existing verified physical generation lemma ensures every
eligible positive source original has later base j>b, higher m>g,
and E(b,j)=true. If the ACTUAL pre-cut stage V_c is shown to
have only the proposed retained roles (selected coding TOP,
kept whole auxiliary blocks, and the isolated dummy cap), lemma 1
proves such a name must be a selected coded TOP original. Lemma 2
strengthens the selected-coded lower-generation case to empty star.

The role-carrier hypothesis is precisely the remaining DESCENDING
induction obligation; it is not established here. In particular,
the still-unproved possibility of additional selected auxiliary
microevents is NOT silently ruled out.

## Adversarial audit (14 checks)

1. Original bases and full numerical-H generations are DISTINCT.
2. The lemma is about the ordinary Q edge E, not auxiliary E+.
3. Edge symmetry is used to deal with a later dummy target.
4. Same-block auxiliary vertices may be adjacent; (AA) is only
   about DIFFERENT blocks, not all auxiliary pairs.
5. Same-block retained flag coherence (B) must be explicit.
6. Chronological coded->aux nonedges require coded base earlier.
7. Earlier aux to later coding may be positive and is allowed.
8. The target selected coding case is NOT incorrectly excluded
   for an omitted NONSELECTED coding base or omitted aux base.
9. A selected coding base has no selected-coded neighbours only
   because A is independent.
10. The dummy cap may be chosen later; its zero L column is used,
    not an assumption about unrelated E+ parameters.
11. Stage source carrier is Run.I(c+1), never guessed from R.I 0.
12. A Kpt full closure source may have meets; role classification
    of representing original names must be proved separately.
13. No full no-I1/no-I2, chosen marked corrected-B3, or global
    bounded resolved-copy assertion follows from these role axioms.
14. The K4 cut-10 and cut-22 genuine I3 regressions remain.

This lemma proves the previously only handwaved BASE-graph
combinatorics in a transparent finite interface. The next Lean
task is to connect the actual Run.I(c+1) stage carrier to these
role predicates by descending induction without circularity.
