# Independent review: concrete retained chunk matrices

24 November 2026. Reviewer: generation-zero validation agent.

Reviewed proposal: `docs/retained_chunk_matrix_english_20261124.md`.
Reviewed SHA-256:
`140c850d68badf94e9664318cdafc508dff06edf12a97a6c3546ae4664bd9eb4`.

## Verdict and scope

The finite matrix calculation is correct under the stated hypotheses. It
supplies complete literal ordinary, unary, diagonal, and auxiliary-E tables
for a common ordered retained slot set. It does not assume the desired
compressed source equality. Implementation may proceed at numerical height
four, or at arbitrary positive height as in the English statement.

This is an independent mathematical review of the English proof, not a
claim that a new Lean implementation has compiled. Record-to-member
extraction, exact actual Plan selection, finite cap bounds, and identification
of the actual level maps remain separate application obligations.

## Checks of the actual coordinate calculation

1. **Slot identity and order.** The anchor, free, and real constructors are
   disjoint. Retained member indices remain distinct even when their flags or
   visible incidence profiles repeat. Positivity of every physical retained
   base and the gap `b(i)+2 <= b(j)` place the anchor first and the whole earlier
   chunk before the whole later chunk. Inside one chunk the free slots precede
   all real slots. The TOP free level is `p(b-1,k)+1`, not the lower-generation
   formula. The slot count is consequently `1+(2*k+1)*A+2*n`.

2. **Ordinary table.** Odd free slots have zero ordinary columns in both
   directions. The anchor is the real original `p(0,0)`; its zero ordinary
   incidences require the stated isolated-zero hypothesis and do not follow
   from parity. Same-base real pairs are zero by the strict crossing rule and
   bounded address injectivity. For distinct members the reverse orientation
   uses `D(i,j)` for the actual ordered tuple, together with the reversed
   generation inequality. It does not silently replace this value by
   `D(j,i)`. Both displayed formulas now put the TOP tie inside parentheses,
   so the tie does not bypass the required base edge.

3. **Complete incoming E columns.** At positive height, generation zero has
   no generated incoming E edge, including at the real-zero anchor. An odd
   target likewise has no incoming E. Their actual free levels therefore
   equal zero. A positive real target has the exact strict initial incoming
   segment below its stated free coordinate. All earlier chunks and the
   anchor lie in this segment. Within the same chunk, precisely free slots
   with tag `r<g` lie in it; equality is the first missing coordinate. This
   strict comparison remains correct at TOP. Same-chunk real slots and all
   later chunks lie outside. Odd slots can have outgoing E, and the proposal
   correctly retains those entries in the full table.

4. **Finite restriction and all tables.** Requiring every used coordinate
   to lie in the actual finite carrier avoids hidden target-clipping cases.
   The unary and diagonal tables have the stated constant values. Together
   with the directed ordinary and E calculations this proves literal
   `FinitePartialCode.reindex` equality, not merely equality of ordinary
   graphs or local ages. The same argument restricts to any common initial
   slot segment, including the segment through a selected TOP.

## Boundaries and application limits

The cap is not the anchor. A positive dummy cap can have a positive odd free
level and a nonempty incoming E column even though its ordinary column is
zero. The proposal does not erase that distinguished type or its actual
root role.

The empty member list leaves the one anchor slot, provided coordinate zero
is in the finite carrier. To add a distinct cap endpoint and claim one more
planned level, the cap end must lie strictly beyond every slot. If the cap
end is zero, the endpoint and anchor coincide, so the positive-size source
and `M+1` cardinality claim are unavailable. This exception is stated
explicitly. Repeated event templates do not merge ordered member slots,
and an occurrence cannot be selected from an empty record fibre.

The informal record discussion is consistent with the matrix theorem, but
the theorem alone does not prove that a particular resolved-Q construction
has the required retained member list and directed table, that all desired
real coordinates lie before its cap, or that AlgorithmRun selects exactly
these coordinates and their free levels. Those are correctly retained as
separate duties rather than hidden in a table-equality premise.
