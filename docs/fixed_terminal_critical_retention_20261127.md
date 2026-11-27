# Uniform coarse retained-level bound for the actual K4 envelope

## English proof and scope (27 November 2026)

This continues PR #517, using the actual chosen event schedule and actual
original addresses, not an assumed legal projected diary. Let S be the
requested finite original indices, T = S plus the constructed cap, and
m = |T| = |S|+1. Write A for the set of padded original addresses of T.
Use the *one fixed graph* E = oneGapEdge (resolvedFairEventEdge s0).
Its old prefix at c is [0,c). The fixed set A can contain originals
already coded: this is allowed for the following purely numerical
witness calculation. We never interpret the full set A as a live front
at cuts where that would be false.

### 1. Fixed terminal witnesses

For c, record two finite sets:
- ordered pairs (u,v) in A x A with a disagreement E(p,u) != E(p,v)
  for some p<c;
- (U,j) in powerset(A) x {0,1,2} for which the directed clique capacity
  of the common old neighbours of U in [0,c) is at least j+1.

Both sets are increasing because old prefixes increase, and the graph
and terminal addresses are fixed. Their total cardinality r(c) is a
nondecreasing natural number bounded by m*m + 3*2^m. In particular it
has at most that many strict increases r(c)<r(c+1) below any finite cap.
The count allows ordered pairs and the empty support on purpose:
extra witnesses are harmless for this coarse bound.

If r(c)=r(c+1), each witness set is unchanged (monotone finite inclusion,
equal total cardinality). Equal old columns of two selected terminals
then have equal next bits, since otherwise a new disagreement pair
appears. For any U subset A, the three threshold bits determine
3 - capacity(U), with truncated natural subtraction. Thus that raw
bound is also unchanged, regardless of the possible capacity of U.
For an actual front list f : Fin d -> Nat in A, the common-old-neighbour
pool of a typed support L is exactly the pool of f(L). This does not
require f injective or any identification of two dependent front types.
Hence the entire raw selected age agrees and therefore its canonical
age agrees. This argument uses full ambient prefixes, not compressed
prefixes, exactly as required by the existing local envelope theorem.

### 2. Selection of whole events

Let C be the strict rank increases below the padded coding cap. Map
each c in C to its event index (using the existing one-gap inverse and
chronological schedule). Keep every auxiliary event in that finite
image; leave the selected coding flags exactly as in PR #517.
It is harmless if an extra dummy cut or a coding cut maps to an event;
the actual meaningful-cut proof uses the exact address inverse.

Every selected original in T is retained independently of the aux
flags. The actual eligible retained coding front is a subset of A by
the existing range theorem. At an omitted meaningful cut:
- If it is a code event, its coordinate is the actual original address,
  and all entries in the eligible front are strictly later original
  indices. The already proved coding-event neutrality and no-split
  apply unchanged for arbitrary auxiliary flags.
- Otherwise it is an auxiliary event, and a strict rank increase at
  its coordinate would have forced the entire occurrence to be kept.
  Thus its rank is unchanged and section 1 proves both premises.

Dummy cuts are handled by the existing zero-cut theorem. The full
retained-pool, endpoint, nonselected-zero and positive-source
conditions are already proved for arbitrary whole-event flags.
Full original seeds for S plus cap satisfy the remaining hypotheses
independently of the auxiliary flags. Apply the actual finite
selection envelope theorem, with the exact prescribed level range.

### 3. Uniform size

All kept events belong to the union of the m selected coding-event
indices and the image of C. Its cardinality is bounded by
B(m) = m + m*m + 3*2^m. A marker or code certificate has singleton
block; a cover has Q.card + futureAge(T) < 4, so its size is at most 3.
Each retained ordinary vertex has an injective tag (event, local
offset), with offset in {0,1,2}. Thus there are at most 3*B(m) retained
ordinary positions. The retained levels are the anchor and the
gap/vertex pair for each kept position. Their cardinality is at most
1 + 6*B(m), independent of selected indices and of the input graph.

### Adversarial checks and limits

- The fixed set is never claimed to remain live after a coding event.
  Only the actual moving subfront is used in the application.
- A capacity can be zero or exceed the three counted thresholds;
  truncated subtraction, not raw capacity equality, is the conclusion.
- Raw neutrality suffices for canonical neutrality; the converse is
  not used and need not hold.
- Retaining only the critical vertex of a multi-vertex auxiliary event
  could break block convexity. We retain the whole occurrence and
  charge at most three vertices per occurrence.
- The finite retained-role pool may include arbitrarily many dummy
  names, even when the retained levels are uniformly bounded. We do
  not bound that pool or silently replace it by the retained levels.
- The cap is counted, including S empty. The bound is deliberately
  coarse, not the exact number of legal diaries and not itself a
  proof of a big Ramsey degree. A common complete labelled inverse
  source and the transfer to a finite record still have to be checked;
  legal diary comparison and sharp lower bounds remain separate.
- The generic fixed-rank lemmas do not need K4-freeness, but the actual
  event construction used in the application remains K4-specific.

## Verification status

Lean candidates are submitted for hosted checking. This session did
not have the previous local checkout/toolchain, and container DNS
could not resolve github.com. No local compilation is claimed.
No manuscript validation marker should be promoted on the basis of
this candidate until the relevant checks and statement audit pass.
