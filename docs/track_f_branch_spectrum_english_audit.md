# Track F — positive-symbol initial-segment invariant of diary branches

**English proof and adversarial audit before Lean, 14 November 2026.** The omission of this invariant makes the claimed equality between the concrete word predicate `E` and the abstract passing-bit set **false**: K4 one-letter words `x=(1), j=(2)` have passing bit 1 but literal E false. The genuine diary must enforce a positive initial segment on each active branch, not merely a value of its canonical graph age.

## Definition

A finite chronological word history is a list of columns `cols : List (Fin d → Nat)`. Let

`Seen(cols,i,n)` mean `there exists c in cols with c(i)=n`.

The **positive spectrum** of active branch i is an initial segment of height a iff for every positive n,

`Seen(cols,i,n) ↔ n≤a`.

This assertion rules out all positive letters greater than a and includes every letter from 1 through a. At the root the empty list has height a=0. If the history uses the valid K_ell alphabet {0,...,ell−2}, then a≤ell−2.

### General append-column lemma

If branch i currently has initial positive spectrum of height a and the newly appended letter q satisfies `q≤a+1`, then after appending this column its new height is exactly `max(a,q)`. Proof: for any positive n, the new history sees n iff the old one already did or n=q, i.e. iff n≤a or n=q. For q≤a the new symbol was already seen and max(a,q)=a. For q=a+1 it adds precisely the next missing positive symbol, giving max(a,q)=a+1. For q=0 it introduces no positive symbol. This equivalence is valid for arbitrary Nat letters; no unsound compactness or Ramsey assumption enters.

## The concrete age-change event and the exact singleton heights

Let ell≥3, let F',F be **genuine** integer-witness K_ell graph ages on d active sorts with F' an immediate predecessor of F, and T the unique inclusion-minimal changed support. The associated valid concrete age-change column appends

`q_i = ell−1−F'(T)` on each branch i∈T, and 0 outside T.

Assume the old literal words have positive initial spectra of heights

`a_i = ell−1−F({i})`,

where the singleton capacities are actual canonical ages (the equality with the raw singleton word bounds is separately verified under raw support monotonicity). Then after the column, branch i has positive initial spectrum of height

`a'_i = ell−1−F'({i})`.

The complete case analysis is:

1. **i∉T:** If singleton {i} changed, the already verified cover theorem `trackFCover_essential_contained_in_changed` would force T⊆{i}, contradicting i∉T and nonemptiness of T. So F'({i})=F({i}), q_i=0, and a'_i=a_i=max(a_i,q_i).
2. **i∈T, T={i}:** The one-step cover theorem gives F({i})=F'({i})+1. Hence q_i=ell−1−F'({i})=a_i+1 and a'_i=a_i+1=max(a_i,q_i).
3. **i∈T, T≠{i}:** Singleton {i} is a proper admissible subset of the inclusion-minimal changed T, so F'({i})=F({i}). Monotonicity of the genuine lower age gives F'({i})≤F'(T), and hence q_i=ell−1−F'(T)≤ell−1−F'({i})=a_i. Thus q_i is **already in the old positive spectrum**, and a'_i=a_i=max(a_i,q_i).

In all cases q_i≤a_i+1 and `max(a_i,q_i)=a'_i`. Apply the general append-column lemma to every branch. The initial-segment invariant and its synchronization with singleton ages are preserved by **every valid cover-based age-change step**, for arbitrary ell≥3.

### Splitting and coding

- At a splitting step, surviving old branches append 0, the new right child appends 1 to a copy of its parent prefix. Every existing initial spectrum stays an initial segment after appending either 0 or 1. The new right child's positive spectrum stays an initial segment because 1≤a+1 for any a≥0. Its **singleton age synchronization**, including the non-free right-child exception when the parent has maximal singleton age, remains to be checked with the actual split age operation.
- At a coding step, the coded branch becomes terminal and all surviving branches append either 0 or 1; the positive spectra of survivors stay initial segments. Again, full age synchronization requires the separately verified safe coding canonical-age preservation theorem and the **concrete E/passing-bit equality**; proving the latter is the next independent target.

The root is empty and has maximal singleton age ell−1, so its spectrum is the initial segment of height zero. Inductively, once the splitting singleton-age rules and coding-node removal are matched, the general valid-diary spectrum invariant follows.

## Hostile scope guards

- **Do not derive initial segments from the canonical age alone.** Arbitrary word histories can skip a letter (e.g. word (2) without 1), giving the same singleton age as a valid history but a false E/passing-bit equality. The induction uses *actual events and chronological columns*.
- **Multi-support covers require the essential-support theorem.** A common positive symbol n written on a multi-sort T may already be present separately on every branch. It should NOT be treated as a singleton age decrease. In fact the singleton age does not change at any proper subset of T; this is what rules out skipped letters.
- **One-step cover is essential** when T is a singleton. Without it, q_i could jump more than one position and destroy the initial segment.
- **Every changed support need not equal T.** Only the unique inclusion-minimal changed T determines the actual new column. A proof that chooses a nonminimal changed support has no valid event inverse.
- **The new maximum is not determined by raw-cap labels unless actual age synchronization is proved.** State the lemma conditionally on the synchronized singleton-age heights and verify the synchronization inductively, rather than implicitly assuming it.
- **Not the full diary bijection.** Terminal labels, non-free split ages, full minimal-pre-age coding, and the chronology-respecting inverse remain separate. No new infinite BRD lower bound follows.

## Lean acceptance steps

1. Define `trackFSeenSymbol`, `trackFBranchInitial`, and prove `trackFBranchInitial_append` under q≤a+1, with an explicit identity for appended seen-symbols.
2. Introduce the actual K_ell singleton support and word-spectrum/age synchronization predicate.
3. Prove the full **age-cover column** synchronization using the already verified `trackFCover_essential_contained_in_changed`, `trackFCover_drop_one_at_changed`, `integerGraphAge_monotone`.
4. Only then incorporate splitting and coding into a typed full diary transition invariant.
5. Require exact-head Lean module compilation and named standard-only axiom checks. Do not promote the full correspondence or unavoidability marker.
