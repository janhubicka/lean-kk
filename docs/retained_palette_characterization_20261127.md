# Retained envelopes and the characterization target (2026-11-27)

## Status distinction

The unbounded accepted nonedge-history type was counted in PR #504:
its cardinality is 24, with split-rank subtotals 16, 6, 2. That proof
and its semantic bridge were checked on the earlier branch. The six
Lean modules and their supporting audit are now copied byte-for-byte
from 728f6b744f8f971e4a098c05378cb3a464ab82ab. The integration head requires its own build/audit.
Neither the enumeration nor the conditional semantic theorem is an
unconditional characterization of the graph big Ramsey degree.

## English proof of the new palette bridge

Let F be a shape-preserving map with level range I union all levels
above top, where I is finite. If F(y) is at or below top, the images
of levels 0 through lev(y) all lie in I. The level map is strictly
increasing, so lev(y)+1 <= |I|.

If b is covered by F, a is an ancestor of b, and lev(a) is in the
level range, take a preimage u of b and the unique source level j
mapping to lev(a). Monotonicity implies j <= lev(u). The j-ancestor
of u maps to an ancestor of b at lev(a), hence to a itself. Thus
covering a cap also covers its ancestors at all retained levels.

For an actual G+ representing pair P with a covered upper endpoint
of level <= top and a lower endpoint at a retained level, both
endpoints now have preimages below |I|. The existing successor-tree
bounded-pair lift supplies a source representing pair. For a finite
tuple of such pairs, use the same F for all coordinates, enlarge
the bound from |I| to b, and restrict F to its finite approximation
through level b. Agreement on the complete bounded source tuple is
the existing G+ action lemma. No minimal-run hypothesis is used.

## Adversarial checks and remaining obligations

- Finite I is a set, not a list with repeated levels. Strict monotonicity
  is essential for the cardinal bound.
- The bound concerns the source level, not the possibly huge ambient
  address of the target.
- The ancestor conclusion requires both a covered upper endpoint and
  the lower level in the range; retained levels alone do not cover
  arbitrary nodes.
- A single F acts on the entire tuple; independently chosen maps
  would not give a common finite approximation.
- The finite palette is coarse. Its cardinality need not be 24.
- Still needed: represent each actual selected prefix by a pair with
  the actual retained cap and retained lower endpoint; obtain the
  uniform coarse palette bound; identify precisely the legal diary
  histories and prove equality of complete compressed labeled source
  codes for equal histories; establish unavoidability inside every
  induced copy. Only then apply the already checked count and semantic
  interface to obtain the exact nonedge BRD.
- The general K_k application must not be inferred from the K4
  construction without its own resolved-graph/retention argument.

## Validation status

The preceding head of PR #518 failed a single rewrite in the raw-age
neutrality application. The patch supplies the actual retained-front
function explicitly and applies congruence of canonicalization to the
raw equality. The new bridge and the integrated count have not yet
been checked together by Lean. No new axioms or sorry are intended.
