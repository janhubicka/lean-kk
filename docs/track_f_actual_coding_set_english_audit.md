# Track F — actual passing-one set and exact coding successor age

**English proof and hostile audit before Lean (14 November 2026).** This integrates the *two distinct facts* already proved or submitted on Track F branches: (i) the literal chronological word predicate E is exactly the abstract pairwise passing-bit test at any active level with valid synchronized initial spectra; (ii) after deleting the coded branch, the literal 1/0 column preserves exactly the canonical graph age when every nonempty admissible support inside its passing-one set is safe. This is a proper step toward the concrete–abstract diary dictionary, not the full diary correspondence.

## Explicit two definitions on surviving coordinates

Fix ell≥3, d+1 active word branches indexed by Fin(d+1), a proposed coded branch j, and actual chronological columns C. Let F=G_(phi_C) be the *genuine* integer-witness graph age. Suppose the positive-symbol spectrum on every branch is the exact initial segment synchronized with its singleton age, and F({j})=1.

Let f=Fin.succAboveEmb j : Fin d ↪ Fin(d+1) be the actual order-preserving injection of the surviving coordinates.

Define the **literal concrete passing set**

`X_E = {i: Fin d | E(C,f(i),j)}.`

Define separately the **abstract controlled-coding passing set**

`X_F = {i: Fin d | F({j,f(i)})=F({f(i)})+1}.`

The formal definition of X_F uses `trackFMapSupport (trackFSelectPair (f i) j ...) (trackFPairBoth ell ...)` and its first singleton, which are verified literal supports; it is not defined in terms of E or the desired theorem.

## Passing-set equality

For each surviving i, f(i)≠j by `Fin.succAbove_ne`. The arbitrary-active-level theorem `trackFConcreteEdgeAt_iff_abstractPassing` from stacked PR #167 therefore gives exactly

`E(C,f(i),j) ↔ F({j,f(i)})=F({f(i)})+1.`

Extensionality for finite sets proves `X_E=X_F`, without counting automorphisms, arguing from examples, or assuming the desired equality as a definition. The singleton condition and synchronized positive spectra are **essential**.

## Exact successor age using ACTUAL concrete E

Assume the controlled-coding all-subsets safety condition

`for every nonempty admissible U⊆X_E: F(f(U))≤ell−2.`

The previously merged, standard-only checked `trackFWordRaw_coding_after_delete_exact` applies to precisely the literal column `trackFNewColumn X_E 1`, after restricting old columns by f (deleting coded j). It yields equality of the *entire* new canonical graph-age function with `F∘f_*` on every surviving nonempty admissible support, with no silent raw-bound canonicality assumption.

Since `X_E=X_F`, this exactly matches the passing-number labels and *age-profile effect* of the abstract controlled-coding transition.

**Important:** this is conditional on the **other** controlled-coding constraints. The abstract definition also requires a **minimal-pre-age** identity for all supports; the pairwise bit test and safe cap alone do **not** prove it. Similarly, terminal labels/graph preservation across further levels and the non-free splitting rule remain independent.

## Hostile checks

- **E must be literal, not defined from F.** Both X_E and X_F are independent constructions; the theorem is their equality.
- **Use actual surviving indices:** the embedding f skips j in order, and is injective. Do not merge two branches or alter their lexicographic/ordered labels.
- **No arbitrary raw deletion:** the earlier counterexample B({0})=B({1})=3, B({0,1})=1 in K4 refutes canonical deletion for nonmonotone raw B. The merged theorem uses actual word raw monotonicity and true witness zero extension.
- **Positive-initial-segment invariant not optional:** K4 words x=(1),j=(2) violate it and give E false, abstract passing true. The merged age-cover spectrum theorem and 0/1 coding-spectrum lemma supply parts of its induction; the special splitting step remains to be tied to the actual abstract age rules.
- **Full controlled coding not automatic:** even after X_E=X_F and the safe-cap theorem, the published *minimal-pre-age* condition must still be checked in general.
- **No full diary inverse or lower bound:** neither finite local coding equality nor finite dictionary counts prove the infinite persistence needed for independently optimal big Ramsey degrees.

## Proposed Lean endpoints and guard

`Kk/TrackFActualCodingSet.lean`: `trackFConcretePassingSet`, `trackFAbstractPassingSet`, `trackFConcretePassingSet_eq_abstract`, `trackFWordRaw_coding_by_literal_E_exact`. Require the actual `Kk.TrackFWordEdgeAny` theorem (after its exact-head verification), and the merged `Kk.TrackFSurvivorCanonical` coding-age theorem. Compile explicitly and inspect transitive `#print axioms` for only standard Lean axioms. No global validation marker until the complete diary bijection is verified.
