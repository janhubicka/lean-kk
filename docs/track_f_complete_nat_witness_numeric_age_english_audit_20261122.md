# Track F — from finite sorted-graph class equivalence to equality of canonical numeric ages

22 November 2026. English proof and hostile audit before Lean. The main remaining bridge after verified K4 tuple synchronization (#410), survivor resynchronization (#433), genuine pre-code front (#470), endpoint sandwich (#472), and physical deletion/reindexing (PR #475). This note is not a claim that the statement has yet been Lean-compiled.

## The precise theorem

Fix d finite labelled sorts and two genuine normalized integer graph ages A,C on the nonempty support domain IntegerGraphSupport(d,4). Suppose that for EVERY finite n, EVERY symmetric Boolean graph table B on Nat whose restriction to [0,n) is K4-free, and EVERY possibly noninjective sort map sigma:Nat→Fin(d), the COMPLETE canonical finite-clique acceptance tests agree:

  (forall Q subset [0,n), directed-clique_B(Q), forall admissible T,
      card{q in Q : sigma(q) in T} <= A(T))
    iff
  (forall Q subset [0,n), directed-clique_B(Q), forall admissible T,
      card{q in Q : sigma(q) in T} <= C(T)).

Then A=C numerically, on EVERY nonempty support, including mixed triple supports. The theorem remains true for ell>=2 with the corresponding clique threshold, but K4 is enough for the current Track F application.

The statement is STRONGER than equivalence for one chosen finite graph or one support; its universal quantification over all finite B and all label maps is essential. It identifies CANONICAL age values, not generally raw redundant bounds.

## Construct a complete Nat witness for any normalized multiplicity vector

Fix any normalized integer clique witness w:IntegerCliqueWeights(d,4). Its total weight n=sum_j w_j.val is at most 3. Define the genuine finite typed clique vertex type

  X_w = Sigma(j : Fin d), Fin(w_j.val),

with n vertices and EXACTLY w_j vertices of sort j. The verified complete integer-witness component theorem already proves these cardinalities for every selected support T and proves n<4.

If d=0, there are no nonempty admissible supports, and A=C trivially. For d>0 fix an arbitrary default sort j0. Choose the finite-type enumeration equivalence iota:Fin(n) ≃ X_w, available constructively up to finite choice. Define a total Nat label map

  sigma(k) = firstCoordinate(iota(⟨k,k<n⟩)) if k<n, and j0 otherwise.

Let B(k,l)=decide(k≠l), the complete irreflexive symmetric graph on Nat. The actual finite vertex pool [0,n) has no K4 because n<=3, independently of adjacency outside that pool.

The map iota gives a BIJECTION from the selected Nat vertices of sorts T to the selected X_w vertices of sorts T. Therefore the exact filter count is

  card{0<=k<n : sigma(k) in T} = sum_{j in T} w_j.val
                                  = integerCliqueOnSupport(w,T).

The left count is a literal finite-set cardinality, NOT an assumed interpretation of a normalized witness. This finite enumeration lemma is the one nontrivial encoding obligation in the Lean proof.

## Complete-graph acceptance is EXACT witness feasibility

For any candidate age function F (not necessarily genuine), the finite complete B above has EVERY subset Q⊆[0,n) a directed clique. The full acceptance test for B,sigma is equivalent to WitnessRespects(integerCliqueOnSupport,F,w):

* If the full finite test holds, take Q=[0,n); the exact filter-count equality gives all support inequalities for w.
* Conversely, if w respects every F(T), then the number of Q vertices whose sorts lie in T is at most that of the full pool [0,n), which is w's T-mass and at most F(T). This proves the test for every clique Q, without losing any mixed support.

Thus the universal finite-class equivalence for A and C implies

  forall w : IntegerCliqueWeights(d,4),
      WitnessRespects(A,w) iff WitnessRespects(C,w).

The already kernel-checked theorem integerGraphAge_eq_of_same_feasible_vectors (module ExtensionProfileAge) now yields A=C because both are GENUINE ages. It recovers each value from its supremum among all feasible full normalized clique vectors.

## Application to actual synchronized source and target types

The verified Track F theorem k4_sync_complete_tuple_canonical_class (#410), and its survivor variant #433, return equivalence of precisely the full finite canonical acceptance tests, uniformly for all n, symmetric K4-free B and sigma, with SOURCE/TARGET OLD common-prefix raw functions canonically closed.

Each actual Henson type tuple produces a GENUINE normalized canonical age by the verified #436 theorem. Therefore apply the numeric-age extraction theorem just described to deduce equality of the source and target canonical AGE FUNCTIONS pointwise. This is the needed endpoint numerical equality, not equality of their redundant raw tables.

Finally the exact survivor deletion/reindexing theorem #475 identifies a survivor age on Fin(d) with the corresponding supports in a full old pre-code age on Fin(d+1). With this genuine endpoint equality, the verified full precode sandwich (#472) can conclude the true pre-code age equals the prescribed F provided the legal zero-code law holds. This would close the numerical-age part of a physical code event, but NOT automatically prove all chronological meets or the full history lower bound.

## Hostile audit

1. A single graph B cannot determine the complete age: universal quantification over ALL finite B and sigma is necessary.
2. The witness graph MUST be the complete K4-free graph on at most 3 vertices, with loops false. The all-Nat definition B(k,l)=decide(k≠l) is symmetric and the finite prefix remains K4-free.
3. w is normalized with TOTAL weight<=3, not just coordinatewise weights<4; without total normalization the finite complete witness could contain a forbidden K4.
4. Multiple distinct vertices can have the SAME sort. The Sigma witness X_w realizes correct multiplicities; sigma is not assumed injective.
5. The exact count for EVERY support T must be derived from the finite enumeration equivalence and verified fibrewise count theorem. Treating Definition 3.1 or a published diary characterization as a source of this equality would be circular.
6. At d=0, there are no supports and no default Fin(0) label; handle the case separately, without fabricated sorts.
7. The witness total n can be zero; the equivalence Fin(0)≃X_w and the complete graph prefix are then empty, and every support mass vanishes.
8. To establish actual test iff witness feasibility, the "only if" direction must use Q=range n and prove it is a clique. The "if" direction must use monotonicity of FILTERED CARDINALITIES for every Q⊆range n, not just for maximal cliques.
9. The class-equivalence theorem is for *symmetric* graph B. The explicit complete B is symmetric by ne_comm, no hidden old source graph symmetry assumption.
10. Genuine K4-free test on the finite B pool is separate from normalized K4-freeness of the actual Henson source and target.
11. The numeric equality follows only for complete CANONICAL age functions, or for genuine ages with witness saturation. Arbitrary pointwise RAW age tables can define equal feasible classes while differing on redundant support values.
12. Use the independently checked integerGraphAge_eq_of_same_feasible_vectors and actual-front genuine-age positivity, not a new axiom of "age determined by graph class".
13. The finite-type enumeration map need not be chronological. It is only an abstract finite witness graph B. Neither source-to-target e nor source lex order is used in this encoding.
14. For K4, all witness components have size at most 3, but their sort support can be 1, 2 or 3; the construction handles all.
15. This age equality does not identify an actual selected code vertex, split, cover, unrecorded diary event, Kpt E/parameter history or upper Ramsey proof. Those are separate.
16. Once the age equality bridge is proved, check that old/source and new/target survivor sort indices are identified by the EXACT order-preserving survivor map Fin.succAboveEmb j. A source/target lex-order mismatch is NOT automatically resolved.
17. No frozen black manuscript text should be changed; only add validation markers for genuinely checked statements after Lean CI, keeping full-history and BRD lower-bound markers pending.

## Lean implementation plan

1. Implement Nat encoding of a normalized typed complete clique: choose a finite equivalence Fin(n) ≃ IntegerWitnessVertex w, define sigma on [0,n), prove exact filter-cardinality identity for every support using the already checked integerWitnessVertex_support_eq_integerCliqueOnSupport. Prove n<4, symmetry and the actual finitePoolCliqueCheck=false.
2. Prove finite complete clique acceptance iff normalized witness feasibility for ANY bound function F.
3. Prove universal finite canonical test equivalence implies equality of full normalized witness-feasibility predicates.
4. Invoke integerGraphAge_eq_of_same_feasible_vectors for genuine ages A,C; then specialize to the already verified k4CanonicalSortedFiniteTest equivalence of real source/target tuples.
5. Compose numeric endpoint equality with physical deletion/reindexing #475 and precode age sandwich #472 in a separate later proof, maintaining the distinction between geometric construction and history event realization.

The first nontrivial Lean task is the exact finite Nat↔Sigma encoding; write it with a complete finite equivalence rather than hard-coding 24 independent-triple orbit counts. No sorry or extra axioms.
