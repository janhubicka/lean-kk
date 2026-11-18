# Track C — exact live-image criterion for coherent physical source transport

17 November 2026. English-first adversarial proof audit. **Not yet Lean-verified**. This note extends the *verified* forward CoherentKptIndex interface in `Kk/CoherentKptIndexComposition.lean` and the negative reverse-map theorems in merged PR #308; it makes no new claim of a physical root-stage theorem.

## Setup and precisely stated claim

Fix one cut c below the horizon of a coherent injection f : Fin P → Fin Q. Write A = {i : Fin P | oldLive c i = true} and B = {j : Fin Q | newLive c j = true}. By the verified `live_forward` field, f(A) ⊆ B.

**Criterion.** The following are equivalent:
(1) f(A) = B;
(2) (a) no newly live target index lies outside the image of f, and (b) no old-source index that was inactive at c becomes active at f(i) in the new stage.

In formulas:
(a) ∀ j, newLive c j = true → ∃ i, f i = j;
(b) ∀ i, newLive c (f i) = true → oldLive c i = true.

**Proof, (1)→(2).** Each j∈B has j=f(i) for some i∈A, giving (a). If f(i)∈B, then f(i)∈f(A) by (1), say f(i)=f(i') with i'∈A. Injectivity gives i=i', hence (b).

**Proof, (2)→(1).** Forward inclusion follows from `live_forward`. Conversely, for j∈B, (a) gives j=f(i); (b) gives i∈A, so j∈f(A). This proves equality.

Observe that source node identity and full dependent old/upper L+/E type preservation come free for *transported old indices* from `same_node`; they do not establish (a) or (b). This is equality of indexed live-name sets, not equality of entire finite source universes, and is cut-by-cut.

## Two independent counterexamples (both satisfy coherent forward transport)

**Fresh live target outside the image.** P=1, Q=2, f(0)=0, both old index 0 and new index 0 denote the same node and are live at c; new index 1 is also live. A={0}, B={0,1}, so (a) fails. A coherent index requires an admissible Kpt node assignment for index 1 but imposes no restriction on its new live bit. Choose any admissible node, even a duplicate if distinct source enumeration is not separately stipulated. This is an **interface countermodel**, not a claim that every physical construction admits duplicated source names.

**New activation of an existing node.** P=Q=1, f=id, the same literal node is indexed at both stages; oldLive c 0=false and newLive c 0=true. The coherent `live_forward` implication is vacuous and all other fields hold, yet A=∅, B={0}, so (b) fails. Thus even a bijective identity source-name map does NOT imply equal live masks.

Neither counterexample invalidates the physically constructed forward invariant: it demonstrates why the invariant cannot, on its own, yield a reverse live-set equivalence.

## Legitimate restricted inverse

For an injective map f, the restriction f : Fin P ≃ range(f) is a bijection of *names onto the old image*. On the image, source node labels are literally equal by `same_node`. At a cut c, the inverse transport of **live status** is exact only if (b) is supplied. This image-restricted inverse does not assign an old name to fresh target nodes, and therefore avoids PR #308's genuine reverse-source obstruction. Under (a)+(b), it gives a cut-local bijection of live source sets; it is NOT a reverse `CoherentKptIndex` on all Q names.

## Hostile scope checks

1. Forward activity preservation is one implication, not equivalence; a false→true activation is allowed.
2. Injectivity only identifies preimages; it never ensures all new live names are old.
3. Source-node equality transfers the full Kpt node and all its L+/E data, not the external stage-dependent live-mask bit.
4. At a different cut d, assumptions (a) and (b) must be reproved; equality at c does not propagate automatically.
5. Equality of cardinals |A|=|B| with f(A)⊆B implies equality of finite live sets, but equal cardinalities of *whole index types* do not.
6. Source indexing may have duplicate nodes unless explicit exhaustiveness/uniqueness premises eliminate duplicates. Do not infer physical freshness from Q>P alone.
7. For a chain of stages, one can compose forward f maps and retain old active names below the minimum horizon. Equal live-image sets require (a)+(b) for **each** link and cut.
8. A cut-local bijection of names is not the common labelled inverse successor-monoid orbit across two arbitrary diary occurrences.
9. Ordinary selected graph-age equality does not imply (a), (b), or equality of full dependent Kpt L+/E sources.
10. K4 auxiliary q2 witnesses/cuts 10 and 22 must not be projected away when testing (a).
11. The global BRD upper/lower equality remains pending; this note only isolates the exact finite comparison obligation.
12. Do not add a new GREEN manuscript mark for an English-only lemma; initially record as an audit target.

## Next formalization step

Prove the iff criterion in a small standalone Lean file, parameterized by the existing `CoherentKptIndex` and `cut < horizon`. For instance use `Set.image h.map {i | oldLive cut i = true} = {j | newLive cut j = true}`; keep the two hypotheses exactly as (a) and (b). Also formalize the one-index activation countermodel. Run an exact-head build, a named `#print axioms` audit, and a full repository build before promoting any manuscript validation mark. Apply the resulting criterion only when the physical construction supplies (a) and (b), rather than assuming it from forward coherence.

**Editorial scope:** no black text changes, no replacement of previous validation markers, no obsolete reverse-map argument reinstated.


## 18 November continuation: two classes of untransported live *indices*

Let (f:P\to Q) be the coherent OLD→NEW name injection. For a new live
index (j\in B_c\setminus f(A_c)), classical finite case analysis gives
exactly the following **alternative at the level of old index images**:

- **Activation:** (j=f(i)) for some old *inactive* index (i\notin A_c).
- **Outside image:** (j\notin f(P)), so no old name represents this new index.

**Proof.** Decide whether (j\in f(P)). If not, the second alternative holds.
If yes, choose (i) with (f(i)=j). The hypothesis (j\notin f(A_c))
implies (i\notin A_c), establishing activation. The alternatives are disjoint
because (j\notin f(P)) excludes all preimages. The proof does **not**
assume a reversed live implication, global index surjectivity, or equality of
successor-tree monoid orbits.

This refines the earlier two-condition criterion: live-image equality holds
iff **neither** residual class occurs at cut (c). Indeed coverage rules
out outside-image names, while reflection rules out newly activated
old-image names. Conversely, if neither class occurs, the forward
live-preserving map covers all new live names.

**Crucial audit limitation.** An outside-image *index* is not by itself a
genuinely novel *Kpt node* unless the finite indexing is injective and
old-node enumeration is exhaustive. A new index may duplicate an old
literal node. The verified fresh-node obstruction in PR #308 is a
stronger statement about actual Kpt nodes, and cannot be inferred from
the pure indexing disjunction. Similarly the activation case may be a
change of cutoff membership rather than a new node at the final source.
No claim is made that the residual classes are uniformly bounded,
canonically diary-encoded, or eliminated by the physical construction.

### New Lean endpoints

The branch adds `new_live_untransported_is_activation_or_outside` and
`transported_of_coverage_and_no_activation`, with direct named axiom
reports. These theorem *sources* are committed but still await exact-head
Lean compilation; there is no current Actions run for the latest SHA.
Do not register a new GREEN or BLUE manuscript validation mark yet.
