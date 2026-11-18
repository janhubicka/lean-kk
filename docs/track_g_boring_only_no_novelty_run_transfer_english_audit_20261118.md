# Track G — only OLD-BORING cuts need no-novelty for whole-run transfer

18 November 2026. English proof FIRST; hostile audit before Lean.

## Setting

Fix a normalized Kpt forbidden family, genuine seed sets X⊆Y in
the SAME normalized Kpt successor-tree H, one common finite top t,
and ONE actual AlgorithmRun RX on X. Do NOT assume a run on Y.
For each cut i<t set

  ZX(i) = closure(S, RX.I(i+1), X),
  ZY(i) = closure(S, RX.I(i+1), Y).

Monotonicity of Kpt meet/parameter closure in the seed argument
gives ZX(i) ⊆ ZY(i) with IDENTICAL selected level set I.
The two closures are full dependent L+/E Kpt source sets, not
ordinary selected-front graph ages.

## Lemma 1: actual source interestingness is monotone

For ANY successor-tree SMTree H and sets C⊆D of actual source
nodes, IsInterestingAt(H,C,i) ⇒ IsInterestingAt(H,D,i).

Proof. An I1 witness in C remains in D. An I2 compatible meet
witness in C remains in D. For I3, if no skipping MMap satisfies
all ancestor constraints on C, then no skipping MMap can satisfy
the stronger constraints on D: restricting a hypothetical
whole-D witness to C gives a contradiction.

The contrapositive says BORING(D) ⇒ BORING(C). It does NOT say
BORING(C) ⇒ BORING(D), and the genuine K4 cuts 10/22 are
precisely a warning against the latter inference.

## Lemma 2: no novelty is exactly equality of full local
## terminal/crossing profiles under source inclusion

Fix complete actual Kpt node sets Z⊆W and one aligned cut i.
The verified `NewRootNoNoveltyAtCut family Z W i` means:
(a) every W terminal of level i has an old Z terminal, and
(b) the entire complete paired old/upper L+/E crossing relation
    of W is included in that of Z.

Source inclusion Z⊆W automatically gives the REVERSE
inclusions of terminal-existence and complete physical crossing
relations. Consequently no novelty is EQUIVALENT to

  KptI1AtCut(Z,i) ↔ KptI1AtCut(W,i),
  FullPhysicalClosureCrossing(Z,i)=
      FullPhysicalClosureCrossing(W,i).

No source-node bijection or no-I2 hypothesis is needed. The
unpaired marginal upper spectra are NOT sufficient.

## Main theorem: transporting a genuine whole run

Assume ONLY the following for each OLD-BORING cut i<t:

  ¬ IsInterestingAt(H, ZX(i), i)
    ⇒ NewRootNoNoveltyAtCut(family, ZX(i), ZY(i), i).

Then the EXACT SAME RX.I and RX.F define a genuine AlgorithmRun
RY on Y; in particular RY.I=RX.I and RY.F=RX.F as total functions.

**Proof.** Build RY using the exact record components
  I=RX.I, F=RX.F, topI=RX.topI, topF=RX.topF.
At each cut i, consider the TRUE Y interestingness predicate
on ZY(i).

* If Y is interesting, then X must also be interesting:
  otherwise X boring invokes the no-novelty premise, Lemma 2
  gives equality of the full profiles, and verified G347 gives
  equality of I1/I2/I3 interestingness — contradiction.
  The genuine RX.interesting_step equations for BOTH I and F
  can therefore be used unchanged.

* If Y is boring, X is also boring: otherwise Lemma 1's
  monotonicity would make Y interesting. Invoke the genuine
  RX.noninteresting_step, yielding one actual skip-only monoid
  D_i, its crossing law on EVERY old full source node, and
  the exact I,F step equations. The old-boring no-novelty
  premise applies; by Lemma 2 the complete paired crossing
  relations agree. Verified G347 transfers the SAME D_i
  crossing equation to every new source node in ZY(i).
  The map is still skip-only and the I/F equations are identical.

This supplies all genuine AlgorithmRun step fields, not
an informal fake run or independent monoid maps at each cut.
All the original total F values survive unchanged by construction.

## Finite exact-index corollary

Let nodeX:Fin P→Kpt and nodeY:Fin Q→Kpt be independently
EXACT full-source finite indices at every cut, with masks
liveX/liveY computed for the full closures ZX(i),ZY(i) on
the ORIGINAL RX.I tails. Assume only when the old i is
genuinely boring that `KptIndexedQuietAtCut` holds for
these two indices. The verified E54 theorem
`kptIndexedQuietAtCut_iff_physical` converts this into
`NewRootNoNoveltyAtCut` on the actual pre-cut sources.
Apply the main theorem: an actual same-I same-F Y-run EXISTS.
Equal finite index sizes or name bijections are not premises.

## Adversarial checklist

1. Use SAME top and SAME source coordinate system; no
   chronological reindexing across unrelated diaries.
2. Literal X⊆Y is indispensable for old-to-new closure
   inclusion and monotonicity; unrelated sources require G353.
3. At each cut, use closure(S,RX.I(i+1),X/Y), NOT the
   unknown Y-run selected sets.
4. Quietness is required only at OLD-BORING cuts, not all cuts.
5. Adding source constraints may create extra interesting
   cuts; no-novelty rules them out exactly where old was boring.
6. The proof at old-interesting cuts does NOT assume profiles
   agree; these events may acquire additional new parameters.
7. A new terminal is invisible to paired crossing profiles;
   the terminal test remains independently necessary.
8. The full crossing set records SAME-NODE paired dependent
   old/upper types, auxiliary E, and negative ordinary L.
9. No functionality assumption; genuine competing I2 forks
   are retained in the complete relation.
10. A selected ordinary L graph-age shadow cannot certify
    the required physical quietness.
11. At old-boring cuts the SAME actual skip-only D_i from
    RX works on Y by G347's per-MMap crossing law transfer.
12. RY.F=RX.F is EXISTENTIAL synchronization; arbitrary
    separately chosen Y runs may have different total F.
13. The even/odd and K4 auxiliary genuine cuts 10 and 22
    are not deleted: if newly interesting, old-boring
    no-novelty must fail at that source cut.
14. No actual Y-run is assumed as input, and no E1 is used.
15. This gives no reverse map Y→X for new-only Kpt nodes.
16. Finite index masks must exactly enumerate full closure
    at all cuts; indexability alone is not a diary-uniform bound.
17. Whether a refined diary enforces old-boring quietness
    over UNBOUNDED physical growth is still unproved.
18. No uniform bound on the number of novelty intervals
    or their lengths follows.
19. No common labelled inverse-source monoid orbit,
    complete chronological cut-coordinate transport, or
    corrected B3 relative-continuation result follows.
20. No global resolved copy / sharp Kk-free BRD theorem follows.

## Lean acceptance and explicit targets

Import the checked G347 full profile/skip-law module,
G353 whole-run transport, the genuine `NewRootNoNoveltyAtCut`
and E54 `KptIndexedQuietAtCut` interfaces. Formalize:
(A) generic IsInterestingAt monotonicity under C⊆D,
(B) no-novelty ↔ full terminal/crossing equality for Z⊆W,
(C) genuine same-I/F Y-run transport from quietness only
    at old-boring cuts,
(D) exact finite-index old-boring quietness corollary.
Run standalone direct Lake build, strict 4-name standard
axiom parser gate and independent full CI. Keep global
manuscript statements pending and do not edit frozen black.
