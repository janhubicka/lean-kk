# Track D: normalize one physically labelled forbidden clique into genuine integer multiplicity weights
14 November 2026 — English mathematical proof and adversarial audit, BEFORE Lean.

## Purpose and exact limit

The hard remaining bridge is from a physical full corrected-B3
forbidden clique witness to a normalized labelled clique vector
for the selected-front graph-age state. The earlier exact physical
clique theorem supplies a finite forbidden K_ell containing the tested
cut, with at most ell-1 upper clique vertices, each carrying a
genuine full physical original name and complete next-cut L type.

But a labelled vector needs a SORT MAP. We cannot silently assume
that a full auxiliary Kpt parameter type has a selected active
macrodiary branch sort: the literal K4 q2/x counterexample
makes precisely that step false for selected-only data.

We therefore isolate and prove the correct PURE COMBINATORIAL
normalization under an EXPLICIT sort map for clique indices:

For ell,d,cut in Nat, any map e:Fin ell -> Nat identifying one
clique vertex with the cut (there exists a0 with e(a0)=cut),
and ANY explicit sort map tau:Fin ell -> Fin d, there exists
a normalized genuine IntegerCliqueWeights(d,ell) vector w with

  integerCliqueOnSupport(w,T)
    = card{a:Fin ell | cut < e(a) AND tau(a) in T}

for EVERY admissible support T. In particular its full total
size is exactly the number of future clique vertices and at
most ell-1. No injectivity of tau is assumed: distinct upper
clique vertices may have the SAME sort, creating multiplicity 2,
3, etc, which is essential to the Henson K4 q2,x,x example.

## English proof

Choose a0:Fin ell with e(a0)=cut. Put
Upper={a:Fin ell | cut<e(a)}. Since a0 is not in Upper,
Upper is a subset of Finset.univ.erase(a0). Thus
|Upper|<=ell-1 and 0<ell. For each sort j:Fin d set

  n_j = card{a in Upper | tau(a)=j}.

Each n_j<=|Upper|<=ell-1<ell, so it defines an actual
Fin ell coordinate. Form w=(j|->n_j), and verify its total
bound using disjoint-fibre counting:

  sum_j n_j=|Upper| <= ell-1.

For an arbitrary support T, the SAME finite fibre-partition
identity gives

  sum_{j in T} n_j
    = card{a in Upper | tau(a) in T}.

The left side is the literal integerCliqueOnSupport(w,T),
with no canonicalization or age hypothesis. Therefore w is
normalized and has ALL support multiplicities simultaneously.
This proof is elementary and uniformly valid at ell=1 as
well; at ell=0 the hypothesis e(a0)=cut is impossible.

## 14 hostile checks

1. The sort map tau is an EXPLICIT INPUT; this theorem does NOT
   construct one from a selected macrodiary or Kpt closure.
2. Do not conflate the ambient physical original-name map with tau.
3. Cut itself is excluded from Upper via e(a0)=cut; counting it
   would violate total <=ell-1.
4. Upper is indexed by Fin ell, not by distinct numerical e-images;
   the forbidden induced clique map is StrictMono in actual use,
   but this abstract counting lemma only requires a0.
5. No injectivity of tau: two future clique vertices can share a sort.
6. Every integerCliqueWeights coordinate is an actual Fin ell,
   so prove n_j<ell, not merely n_j<=ell.
7. Show sum over ALL sorts <=ell-1, not only separate component bounds.
8. Every admissible support T is handled simultaneously by one
   w; do not choose different vectors for different supports.
9. Empty support is not part of IntegerGraphSupport; its
   restriction is still correct if generalized to arbitrary T.
10. No graph-age F, raw support bound B, or selected diary
    interpretation is assumed or inferred.
11. The theorem does NOT assert w is feasible for F_before,
    let alone that it violates F_after. Those are substantive
    source-relative geometric obligations.
12. Future--future L edges in the physical bad-core continuation
    need not be actual edges of the named original vertices.
13. The literal K4 q2,x,x certificate can be recorded if tau is
    chosen on the full source including the q2 auxiliary sort;
    dropping q2 from the chosen sort domain is invalid.
14. Require exact-head Lean compilation and strict standard-only
    named transitive-axiom report before calling this normalization
    kernel-validated. Keep all manuscript global markers pending.

## Next application obligation

Construct a labelled sort map for EVERY upper vertex of each
physically certified full-closure forbidden clique, preserving
its COMPLETE next-cut L type and full source/parameter records.
Only then may the normalized vector w be tested against the
selected relative before/after graph ages. The current theorem
supplies the combinatorial normalization, NOT that missing
physical-to-selected sort assignment.
