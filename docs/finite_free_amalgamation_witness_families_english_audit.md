# Free amalgamation of finite K_ell-free continuation witnesses over a common old graph

**11 November 2026. English proof and adversarial audit committed before Lean.** This is a finite Boolean-L graph lemma, not a claim of a full resolved Kpt diary.

## Why it matters

A fixed future finite graph W does *not* realize every normalized integer vector; the one-sort empty-pool counterexample is formalized in the preceding witness-conversion branch. Nevertheless, if for every desired feasible vector we can separately construct an admissible finite **extension of the same old graph P** realizing that vector, the extensions can be combined by *free amalgamation* over P. This creates one finite graph realizing all of them simultaneously. The crucial condition is **no edges between fresh vertices belonging to different components**. It is not a consequence of ordinary graph-age canonicalization or auxiliary E closure.

## Two-component lemma in the actual directed-Boolean language

Let E : Nat → Nat → Bool be an arbitrary directed edge table and P,Q,R finite subsets of Nat. Assume
[

eg K_ell(Pcup Q),qquad 
eg K_ell(Pcup R)
]
using the existing exact `finitePoolCliqueCheck`. Also suppose that
[
	ag{cross}orall qin Q,orall rin R, q
e r
Rightarrow E(q,r)=mathrm{false}.
]
Here the ordinary graph relation E is the **binary L bit**, not the auxiliary Kpt E-incidence.

Then
[
oxed{
eg K_ell(Pcup Qcup R).}
]
In fact, under (cross), the exact iff holds:
[

eg K_ell(Pcup Qcup R)
iff 
eg K_ell(Pcup Q) land 
eg K_ell(Pcup R).
]

**Proof:** Let s be any directed clique of size ell inside P∪Q∪R. If s⊆P∪Q, it contradicts the first assumption. Otherwise choose r∈s\(P∪Q). Then r∈R. No q∈s∩Q can occur: q≠r, and a directed clique requires E(q,r)=true, contradicting (cross). Every member of s is therefore in P or R, so s⊆P∪R, contradicting the second assumption. The converse uses ordinary subset monotonicity of clique capacity. Note that we only used the Q→R direction of missing atoms because the directed-clique predicate checks *every* ordered pair.

**No unnecessary disjointness hypothesis:** the mathematical classification does not require Q, R, or P to be pairwise disjoint. If q=r lies in both fresh pools, it cannot be used as two distinct clique vertices. The practical free-amalgamation *construction* will nevertheless choose fresh disjoint copies to avoid identification of different witness vertices.

## Finite-family lemma

Fix a finite index set I, a finite base P and finite fresh pools W_i. Assume:
- base P is K_ell-free (needed for I=∅);
- for every i∈I, P∪W_i is K_ell-free;
- for every distinct i,j∈I and q∈W_i, r∈W_j with q≠r, E(q,r)=false.

Then
[

eg K_elligl(Pcupigcup_{iin I} W_iigr).
]
Proof by induction over I. The empty family is P. At the induction step use the two-component lemma with Q=the union of the old indexed pools and R=W_i; the cross nonedge requirement follows by taking a witnessing index j for each q∈Q and using i≠j. The base P is unchanged throughout. No clique size or graph symmetry assumption beyond the displayed hypotheses is smuggled into the induction.

The converse direction follows by subset monotonicity: if the full amalgam is K_ell-free, then each P∪W_i and P alone are K_ell-free.

## Consequence for universal finite integer-witness realization

For ell>0, every normalized `IntegerCliqueWeights d ell` has total weight at most ell−1. For a given vector w, form a finite complete clique component with exactly w_j vertices of sort j, using distinct fresh labels. It is K_ell-free. The disjoint union over **all feasible** normalized vectors (there are finitely many) is K_ell-free by the finite-family lemma over empty P, and the complete component for w realizes the exact vector w. Every clique of the union is contained in a component (or is empty), so it has a coordinatewise subvector of one of the feasible vectors. Therefore all its support counts satisfy any nonnegative upper bound B respected by the component's vector.

This is a genuine finite combinatorial **rich witness family**; it repairs the empty-pool obstacle by changing W. But it does not yet solve the Henson manuscript's *relative* problem: each separate vector witness must be an actual extension with exactly the prescribed old-to-future, reserve-to-future, gap-to-future, and auxiliary E/parameter columns. Free amalgamation cannot create an individual extension that does not exist. Nor can it silently add cross-witness edges needed by some auxiliary source type.

## Adversarial checks

1. **One missing directed orientation is enough** only because `IsDirectedCliqueOn` quantifies over *all ordered pairs*. Replacing it with one-direction upward adjacency invalidates that simplification.
2. **Cross nonedges are essential.** If Q and R each contain one new vertex adjacent to an (ell−2)-clique in P, adding a Q–R edge creates an ell-clique although both original extensions were free.
3. **Each individual extension must be free.** No family gluing condition can repair a forbidden clique already present in P∪W_i.
4. **Empty family:** must assume P itself is K_ell-free; the per-component hypotheses are then vacuous.
5. **No hidden pairwise-disjointness:** the *logical* graph lemma needs only cross-nonedges for distinct vertices; the *construction* of independent distinct witness copies should choose disjoint new labels.
6. **Cross edges to old P are allowed** and must agree with the prescribed old table. They are contained in each individual P∪W_i test.
7. **Symmetry is not assumed** in the Boolean-graph lemma. Directed clique freeness follows from one forbidden ordered cross atom. Specializing to undirected Henson graphs requires checking both orientations for the constructed E.
8. **Normalized size:** complete witness components of size ≤ell−1 are K_ell-free even if their sort multiplicities are repeated. They are not constrained to one vertex per sort.
9. **Coordinatewise downward closure:** every subclique of a complete component has counts ≤w_j. This preserves all monotone upper bounds `sum_T w_j ≤ B(T)`, not arbitrary lower-bound requirements.
10. **No mixed-source theorem:** ordinary free amalgamation does not establish parameter-closed Kpt/E source preservation, chronological AlgorithmRun levels or common labelled inverse source.
11. **Graph vs source carrier:** a new finite graph can be later embedded into the universal Henson graph over a compatible finite base, but the fixed numerical-H copy's selected/front enumeration may not inherit the desired diary source labels automatically.
12. **Preserve the entire past:** in later applications, P must include every previously fixed old/marked/gap datum to which each new witness may be adjacent, not merely a projection onto currently active selected vertices.

## Lean implementation and validation

First formalize the two-pool exact freeness iff with the *existing* `Kk.IsDirectedCliqueOn` and `Kk.finitePoolCliqueCheck`, retaining the one-way cross-zero hypothesis and no artificial disjointness. Then formalize the finite-family inductive version over `Finset.biUnion`. A local mathlib proof may use an exact replica of the checker for testing, but the final library must import the **actual checked** definitions and pass full `lake build` plus exact named transitive-axiom reports. Only afterward attempt the more delicate finite universal typed-witness realization and the relative Henson extension interface.

No manuscript black text or green validation marker is changed here.
