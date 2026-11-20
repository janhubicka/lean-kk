# Track B: exact free split, including a maximal parent

## English proof before Lean

For any raw integer-clique bound B, support S, and natural number n, imposing
the extra bound n on S commutes with replacing B by its canonicalization:

    G_(lowerAt(B,S,n)) = G_(lowerAt(G_B,S,n)).

Here lowerAt replaces B(S) by min(B(S),n) and leaves all other raw coordinates
unchanged. A normalized vector respects lowerAt(B,S,n) exactly when it respects
B on every support and its S-mass is at most n. The already verified full
clique-vector equivalence says that respecting B is equivalent to respecting
G_B. Thus both sides maximize over exactly the same normalized vectors.
There is no monotonicity, positivity or genuine-age assumption on B.

Now use the actual free-pivot construction from the preceding audit. Let its
new positive daughter be u and let pi be any parent map. A nonempty support
has all pivot bits positive exactly when it is the singleton {u}. Therefore
the complete new physical raw age is lowerAt(B^pi,{u},ell-2). Canonical
transport gives G_(B^pi)=F^pi, where F is the actual old canonical age. The
displayed extra-bound identity proves the exact full age formula

    G_new = G_(lowerAt(F^pi,{u},ell-2)).

This holds for every parent, including F({pi(u)})=ell-1; there is no safety-cap
hypothesis. For a nonmaximal parent the restriction is redundant, recovering
the preceding free-split preservation theorem. For a maximal parent, this
formula retains every consequence of canonicalization on mixed supports;
it does not assert that only the daughter's singleton canonical value changes.

The zero-neighbour pivot and its complete finite numerical stage exist under
the same forbidden-family and one-point left-density assumptions as before.
Their construction does not require any target-age positivity or safety cap,
because the universal future realizes precisely all compatible raw profiles.
The new formula identifies its actual canonical age. For ell=2 the positive
daughter may have zero capacity; no nonempty daughter is claimed in that case.

## Independent adversarial audit

The arbitrary-map proof referee checked the exact feasible-set argument before
implementation. It requires constraints on every support; an inequality only
at S would not establish the equal feasible sets. The raw bounds outside S
remain exactly B, rather than being silently replaced by a numerical cap.
The proof allows empty feasible maxima and zero raw bounds, and does not use
a greatest-positive-age characterization where positivity may fail.

The physical argument keeps every protected original below b with its entire
column. The pivot is newly constructed, and every newly skipped gap row is
explicitly zero. This is the ordinary-L age component of a free split. It does
not provide the auxiliary Kpt source, full corrected B3 or labelled orbit.

## Hosted integration verification: 20 November 2026

The full hosted integration gate in [PR #414](https://github.com/janhubicka/lean-kk/pull/414),
[run 44781646067](https://github.com/janhubicka/lean-kk/actions/runs/44781646067),
passed for head `4a275de622617da97a132ab8b8adf17cbb989c7b`. CI actually
checked merge `0792d8f297325eb5c80f807c2010a702789f77ac` over the newer
main `ddf60ae5ddba9fbc846dd3072dabc44fdc829ea5`. The complete
**9,727-job build**, parser self-test, and **955 exact named transitive-axiom
reports** passed, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
No `sorryAx` or custom axiom is accepted; all 23 scoped Track B names occur
in the actual successful audit log.

All five new proof modules are byte-for-byte unchanged from the original
verified head `a433ad84f3881da535ee3e7164ff32e3337d2c3c`, which remains a
valid manuscript proof pin. Its earlier [run 44778772393](https://github.com/janhubicka/lean-kk/actions/runs/44778772393)
(9,709 build jobs and 953 reports) is the **historical proof checkpoint**.
The integration updated the central imports and registry, preserving all
932 names from the newer main and adding exactly the same 23 Track B names
(17 new endpoints and six restored protected-pivot checks). Every main
import and report name is retained in its original order.

The [dated evidence record](audits/2026-11-20-track-b-canonical-splits.json)
preserves the original checkpoint hashes and separately records the successful
integration, its actual CI checkout, and current source hashes. This is
hosted verification: the optional local cold build was stopped after hosted
success, and **no completed local full gate is claimed**. The finite scope
above is unchanged; selected-pivot coding, full Kpt/source synchronization,
the prescribed infinite diary, and global BRD conclusions remain open.
