# Track A — one reserved support budget equals the ideal canonical cover constraint

**13 November 2026. English proof and hostile audit before Lean.**
Independent module based on verified `FiniteCliqueSupportWitness`,
`IntegerAgeUniversalProperties` and `CanonicalCoverBlock`.
This is a finite ordinary graph L statement, not a physical
existence theorem or an auxiliary H+ Kpt E/B3 statement.

## Exact finite-witness theorem

Fix d, ell, an arbitrary finite directed graph-L table E, a finite
future pool W with a sort map tau:W→Fin d, an arbitrary raw support
bound family F, a designated **admissible nonempty support**
T∈IntegerGraphSupport(d,ell), and a reserve clique capacity a<ell.
No assumption that W is a clique or that tau is injective.

Let `C_F(W)` mean that **every** directed clique s⊆W respects
`|s_U|≤F(U)` for EVERY allowed nonempty support U.
Let `budget_T(W)` mean
`a+cap_E(W.filter(tau∈T))<ell`.
Let `R=rawCliqueBlockBound ell a F T` from the existing
canonical cover-block construction:

```text
R(U)=if U=T then min(F(U),ell−1−a) else F(U).
```

Then

```text
C_F(W) and budget_T(W) iff C_R(W).
```

Proof: the verified
`finiteCliqueSupportCapacity_iff_all_witnesses` converts
the capacity budget into
`∀ directed cliques s⊆W, a+|s_T|<ell`.
As a<ell, this is equivalent to
`∀s, |s_T|≤ell−1−a`. Conjoining with
`|s_T|≤F(T)` yields the minimum bound at T. All other
support inequalities remain identical. The reverse direction
requires the guard a<ell; otherwise the truncated bound
ell−1−a=0 does NOT imply a+|s_T|<ell, even for s=empty.

This is a logical equality of WHOLE feasible clique systems.
It emphatically does not claim pointwise equality between the
literal raw common-neighbour age of an expanded old prefix and R:
adding a reserved block joined to sorts T can also lower raw
pointwise bounds on proper U⊊T. Such extra inequalities are
redundant when the T-inequality is imposed on every clique.

## Canonical consequence

For a K_ell-free W, apply the already checked
`finiteClique_all_constraints_integerCanonical_iff`.
It proves

```text
C_F(W) and budget_T(W)
iff
C_{G_R}(W),
```

where G_R=integerGraphAgeCanonical(d,ell,R).
No pointwise identity F=G_F is required, and raw R need not
itself be an integer graph age.

If lower ⋖ upper is a genuine cover in the integer graph-age
poset, with ell=lower(T)+r+1 and upper(T)=lower(T)+1,
then the already checked
`integerGraphAge_canonical_cover_block` gives
G_R=upper at capacities a<r and G_R=lower at a=r,
for a≤r. Therefore the abstract finite continuation pattern
has exactly the intended cover/no-cover effect at those
capacity values, **provided** the pre-block finite age is
the upper graph age and the all-support typed constraints
are already the correct reference semantics.

The physical Track A all-prefix gluing theorem supplies the
additional capacity budget only under complete original
columns, old/reserve isolation, gap zeros and safe past;
the present theorem supplies the **canonical age arithmetic**
without hiding those geometric hypotheses.

## Adversarial checks

1. **a<ell is essential.** For W=empty and a≥ell,
   raw block constraint at T may be vacuous while
   a+cap(W_T)<ell is false.
2. **ALL supports required.** A single distinguished maximum
   F(T) does not determine the full joint age, and raw
   canonicalization can lower other coordinates indirectly.
3. **No pointwise raw equality claim.** A real isolated block
   joined to T changes common-neighbour capacities for
   U⊆T; the single T-constraint nevertheless dominates
   the additional bounds on smaller U at the clique-profile level.
4. **Nonclique W:** cap_E(W_T) is the actual max clique
   cardinality in its induced graph, not the number of
   selected top names.
5. **Multiplicity:** tau can map many future vertices to
   the same sort. The filter counts all of them.
6. **W K_free only for canonical comparison:** the first
   raw equivalence needs no ambient K-free hypothesis;
   the second uses W K_free for normalization to genuine
   IntegerCliqueWeights.
7. **No false chronology:** a is *reserved numerical-H
   clique capacity*, not an original index, and its actual
   formula a or a+1 at pivot is a separate ordered-prefix
   theorem.
8. **No global graph-age identification:** the old+future
   reference F is still to be computed from P and the typed
   old columns. PR #113 supplies a conditional exact
   reference age via common-neighbour capacities.
9. **No B3 shortcut:** the numerical-H auxiliary E and
   full source orbit are outside this proof.
10. **Finite paper consistency:** the cover arithmetic needs
    the exact `hEll`, `hAt`, `AgeCover`, and a≤r
    assumptions from the existing proof. Do not drop
    them when specializing to a diary.

## Lean deliverables

New module `Kk/FiniteSupportCoverProfile.lean`:
- finiteClique_full_constraints_raw_block_iff;
- finiteClique_full_constraints_canonical_block_iff;
- finiteClique_full_constraints_cover_step_iff.

Compile at exact head, strict named standard-only transitive
axiom audit and full `lake build`. No new global validation mark,
and no edits to existing protected text or aggregator.
