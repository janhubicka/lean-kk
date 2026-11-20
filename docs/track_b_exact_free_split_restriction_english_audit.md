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

## Verification completed: 20 November 2026

The exact sources of `Kk/CanonicalAgeExtraBound.lean` and
`Kk/PhysicalFreeSplitRestriction.lean` passed the full hosted gate in
[PR #414](https://github.com/janhubicka/lean-kk/pull/414),
[run 44778772393](https://github.com/janhubicka/lean-kk/actions/runs/44778772393),
at head `a433ad84f3881da535ee3e7164ff32e3337d2c3c`: the complete
**9,709-job build**, parser self-test, and **953 exact named transitive-axiom
reports** all passed. Only `propext`, `Classical.choice`, and `Quot.sound`
are permitted; no `sorryAx` or custom axiom is accepted. The proof, imports,
and audit scripts are unchanged from that tested snapshot.

The [dated evidence record](audits/2026-11-20-track-b-canonical-splits.json)
lists hashes and endpoint names. This is hosted verification; the optional
local cold build was stopped after hosted success and is not claimed as a
completed local full gate. The theorem is an exact finite ordinary-L split
step; the selected-pivot coding and full Kpt/orbit obligations remain open.
