# Track F — target-prefix distinctness for arbitrary compatible finite tuples

20 November 2026. English proof and adversarial audit before Lean. Independent of the simultaneous private-front construction PR #403.

## Statement A: real source separation

Let u_i be distinct *genuine* Henson one-types over one actual source graph with the same old level m. Then for any i≠j, there exists an old source original a<m at which their complete positive-neighbour bits differ.

Proof: if the bits coincide for all a<m, their neighbour sets coincide, since every neighbour of either finite one-type belongs to [0,m). They also have the same level by hypothesis. The only remaining fields of a Henson one-type are proofs of boundedness and safety, hence equal by proof irrelevance. So the types coincide, contradiction.

## Statement B: target-prefix distinction

Fix arbitrary source old roots u_i, refined source roots w_i≥u_i, and target types t_i at a common target level H. Let e be an injective induced graph embedding (no chronological order preservation). Assume that for every i, the ACTUAL source coding-node fibre of t_i is rank(w_i)-large above w_i. Assume that for each distinct i,j there is an old source separator a<m between u_i,u_j, and that e(a)<H for every a<m.

For i≠j, take one true coding witness x_i in the large fibre t_i above w_i, and similarly x_j. These witness the actual source columns of the ORIGINAL u_i and u_j, since u_i≤w_i≤x_i and u_j≤w_j≤x_j. The induced map transports the different old source bits at a to the target old bit at e(a). Since e(a)<H, the two target-prefix types cannot coincide: the verified `target_prefix_types_distinct_of_source_old_bit` theorem (#325) gives t_i≠t_j. The result is `Function.Injective t`.

This works even when the SOURCE refined positive markers have target images beyond H. The separator is drawn from the ORIGINAL old prefix, not from the new markers.

## Choice of H

For a fixed old source prefix m, choose H > max{e(a):a<m}. The set is finite irrespective of whether e respects enumeration order. The target-prefix distinction then follows for every pair, without selecting separate pairwise image cutoffs.

## Audit

1. A genuine original type is defined by `level`, `neighbours`, and two proof fields. Same level+neighbour set implies type equality by proof irrelevance; hypothetical types with additional hidden data would invalidate this shortcut, but HensonOneType has no such fields.
2. Source roots must share the SAME old level m for the simple root-injectivity→old-bit-separation proof. A theorem using an explicitly given separator need not assume equal levels.
3. Actual source coding-node membership is essential. Nonempty abstract type cones alone do not supply the actual old L-columns.
4. `RankLargeness.large_has_member` is used at the genuine rank of each REFINED source root; no assumption of rank(uOld)=rank(uNew) is needed for this distinction proof.
5. Each source old root must extend to its corresponding chosen coding witness through the refined root; full old-bit equality, including 0 bits, is needed.
6. e is only injective and induced on off-diagonal source edges; target source index order may be arbitrary.
7. The target types t_i must all have level H, while individual target ranks may vary. The contradiction uses a single target cutoff containing e(a).
8. The source separator a is strictly below BOTH original type levels; this avoids diagonal e(a)=e(x.level).
9. The theorem does NOT show the target family has any prescribed lexicographic order. Source labels must be reindexed by true target order before constructing diary histories.
10. If d=0 or d=1, pairwise distinctness is automatic; the proof should not require an arbitrary Fin(0) element.
11. This statement does NOT construct the common compatible front. That is the independent task in PR #403.
12. It does NOT compare raw/canonical graph-age profiles or prove a global BRD.

## Lean acceptance

Formalize a field-extensionality lemma for genuine one-types, the pairwise root-separation theorem, and target distinctness for an explicit separator family. Apply the verified actual coding-witness extraction and old-bit transport theorem #325. Run exact-head build and strict named transitive-axiom gates.