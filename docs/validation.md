# Verification plan

This project checks the manuscript proof of optimal big Ramsey degrees of
the universal \(K_k\)-free graph. Statements in the present document are
not claims of completed kernel verification unless the corresponding CI
job has passed.

## Verified on 20 October 2026

The finite simultaneous-refinement theorem
`Kk.finite_family_type_respecting_ramsey` compiled in [GitHub Actions run 39346781161](https://github.com/janhubicka/lean-kk/actions/runs/39346781161), against pinned successor library commit `a74c10761303a18649053f2af3a1a1697f032e13`.
The transitive axiom report is exactly
`[propext, Classical.choice, Quot.sound]`.
This establishes the Ramsey-composition step, **not** the labelled carrier,
occurrence factorisation, or optimality theorem.

## Validated labelled-diary transfer (20 October 2026)

[CI run 39371584207](https://github.com/janhubicka/lean-kk/actions/runs/39371584207)
compiled and checked `Kk.diary_colouring_constant` and
`Kk.diary_colouring_factors`. Their transitive axiom lists are exactly
`[propext, Classical.choice, Quot.sound]`.

These results prove that the colour of the transformed selected embeddings
factors through their labelled successor diaries **provided that**
(a) each selected embedding has a representation by the finite carrier
of its diary, and (b) the representation commutes with the induced action.
Neither hypothesis is concealed as an axiom. Their eventual discharge
requires the geometric diary construction.

`Kk/RepresentedVertices.lean` is the next geometric interface:
represented auxiliary vertices, independence of the representing pair,
and the action on their complete atomic relations. The CI verdict for this
file is tracked separately from the already verified transfer result.

## Imported mathematical theorem

The dependency is pinned to
`janhubicka/lean-successors@a74c10761303a18649053f2af3a1a1697f032e13`
and imports `SuccessorTree.Library.TypeRespecting`.
The theorem
`SuccessorTree.V10.normalizedKpt_typeRespectingRamsey` concerns all
intrinsic finite type-respecting maps on the admissible partial types over
a finite partial structure, including the auxiliary relation E. These are
the objects that must be coloured.

## Validation order

1. **Finite simultaneous refinement**: prove
   `Kk.finite_family_type_respecting_ramsey`, allowing the finite partial
   base to vary with the diary. Use the exact monoid composition identity.
2. **Represented graph vertices**: define the pair representation
   \(v(S^+,T^+)\), its equivalence relation and the induced action
   compatible with Observation 6.45 of the successor draft.
3. **Finite labelled carrier**: for each labelled diary, construct one
   finite partial structure and a labelled copy represented by restrictions
   of one top type as in Definition 6.46.
4. **Equivariance**: check that the finite action commutes with the
   induced action on the auxiliary graph, including both directions of
   every binary relation and non-relations.
5. **Occurrence factorisation**: show that every labelled occurrence of
   that diary in the bounded resolved copy comes from the fixed finite
   carrier. This is not implied by an unlabelled envelope isomorphism.
6. **Upper bound**: pull back an arbitrary colouring, apply the finite
   simultaneous refinement, and push back via the two ordered embeddings.
7. **Exactness**: verify the comparison of concrete, abstract and
   successor diaries; import or independently formalise the lower-bound
   unavoidability theorem of the published paper.

## Adversarial checks

- The chosen top type cannot be assumed to be present in a minimal
  envelope: use the finite ambient cap construction.
- The action on the auxiliary graph is conjugated by the fixed
  enumeration isomorphism; it is not literally the action on the
  unenumerated graph.
- The finite carriers must retain the labelled vertices. The bounds
  count labelled diaries, not merely unlabelled shapes.
- The finite Ramsey theorem alone does not prove the lower bound.
  That direction presently uses published diary unavoidability.

The companion TeX and reviewed mathematical exposition live in
`janhubicka/Counting-big-Ramsey-degrees-of-K_k-free-graphs`.
