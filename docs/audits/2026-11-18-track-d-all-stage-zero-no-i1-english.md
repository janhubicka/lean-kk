# Track D — exclude even-real Kpt I1 endpoints using ALL stage originals
18 November 2026. English-first proof and adversarial audit before Lean.

## Stronger premise required

A zero ordinary cut-star on ONLY the full cut-crossing Kpt source
does NOT exclude an I1 endpoint: a terminal node may stop at the
cut and represent no strictly crossing source.

For the actual numerical-H cut c=hPosition(k,i,g), stronger
information is available in dummy and selected-coded lower-generation
cases: every actual stage original address v whose free E-level
strictly exceeds c has ordinary L(c,v)=false. This is a property of
the FULL physical original stage pool V_c, even if its original
type is not represented by a currently crossing Kpt source.
It follows from the genuine physical lower-real generator gate
plus (i) isolated dummy original base, or (ii) the descending
Plan stage-role classification and independence of selected codes.

## Exact conditional theorem

Fix one actual finite numerical H+ structure A, true source seed
set X subset the ambient root original-prefix pool, and a genuine
stage selected level set J. Put
 Z = closure(admissibleKptSTree, J, X)
 V = ambientStagePool(A,U,J).
Take an EVEN real cut c=hPosition(k,i,g), 0<c<N, g<k.
Assume:
 (S) no seed x in X has LevelTree.lev x=c;
 (R) no original v in V has canonical free E-level exactly c;
 (0) every original v in V with cut+1 <= freeLevel(v) has
     L_A(c,v)=false (ordinary L, not auxiliary E);
 (Sym) the ordinary L of A is symmetric.

Conclusion: Z has no node z with level c (no full I1).

For genuine numerical H: (R) is automatic at every even real
level for selected positive generation originals because the
positive free E-levels are odd, and holds for the isolated top
cap original as well. (Sym) is the separately formalized genuine
numerical-H symmetry theorem. The source no-seed-at-cut (S)
still needs the actual resolved-diagram seed schedule, not an
unjustified selected-age shadow.

## English proof, no black box for the difficult meet

Let z in Z have level c. By (S), z is not an initial seed.
The verified finiteNumericH_even_real_level_nonseed_is_original_meet
now supplies ACTUAL stage originals v,w in V whose complete
admissible original types O(v),O(w) share a component and
  z = meet(O(v),O(w)).
This is an exact closure normal form, not an invented
representation by selected TOP branches.

Because z has level c, each O(v),O(w) has level at least c,
by LevelTree.meet_le_left/right and monotonicity of levels.
Hypothesis (R) excludes equality, so both are strictly ABOVE c.
The common meet at level c gives equality of their complete
cut-level ancestors. We must show their next ancestors differ:
if the (c+1)-ancestors were equal, that common prefix of length
c+1 would lie below BOTH O(v) and O(w), hence below their meet,
forcing c+1 <= level(meet)=c. Contradiction.

By the verified actual kptBelowOriginal_ancestor_raw theorem,
both old and next ancestor values are EXACT full dependent
A.partialTypeAt(c,v/w) and A.partialTypeAt(c+1,v/w) records,
including all ordinary L and auxiliary E atoms.
Hence their old types coincide, but their next types differ.

Both originals are physically eligible beyond c and have
L(c,v)=L(c,w)=false by (0). Apply the separately verified
full_zero_ordinary_cut_column_determines_next_type (ordinary
L-symmetry + exact E free-cut orientation) to the two names.
Their full next L+/E types must be EQUAL, a contradiction.

Therefore no such meet z exists, and Z has no level-c
terminal I1 node.

## Consequence when combined with already verified no-fork / B3

The actual stage zero-star gives no strict full Kpt fork.
Once no-I1 is established above, exact fork classification
gives no-I2, and the verified empty-full-star theorem gives
corrected B3. Hence the true AlgorithmRun does NOT select c
in those physical cut families.

The EMPTY-FULL-STAR theorem alone does not justify the stronger
ALL-stage-original (0); the dummy base does, whereas the
selected-coded lower case requires the descending role induction.

## Adversarial audit (20)

1. Stage V comes from actual selected HIGHER cuts J, not Run.I 0.
2. Source is closure(J,X), not graph-age selected shadow.
3. Normal form includes arbitrary iterations of meets and E parameters.
4. A seed at c is an independent I1 obstruction; hypothesis (S).
5. Positive parameter originals have ODD free levels.
6. Original root cap free level must be checked separately for (R).
7. The physical cut c is an EVEN real coordinate, not an odd fake cut.
8. An original with freeLevel below c cannot participate in a meet at c.
9. An original with freeLevel equal c is excluded explicitly.
10. Meet property uses actual same-component O(v),O(w).
11. Meet level c forces old ancestor equality.
12. Equality of next ancestors would yield a common prefix above c.
13. All complete L+/E raw partial type atoms are retained.
14. Ordinary L reverse orientation uses genuine symmetry of A.L.
15. Auxiliary E(c,v) is TRUE for each eligible original.
16. Auxiliary E(v,c) is FALSE by physical spacing.
17. Zero ordinary cut L(c,v) is required for ALL stage originals
    with freeLevel>c, not just closure-selected names.
18. K4 auxiliary I3 cuts 10 and 22 remain real counter-regressions
    against selected-shadow-only hypotheses.
19. No globally uniform diary carrier or inverse source follows.
20. No arbitrary nonselected/auxiliary omitted cut B3 test is solved.

## Formalization tasks (in order)

A. Abstract meet contradiction for two actual eligible source
   originals with the same old full dependent types and zero
   ordinary cut bits.
B. Transport its premise from a meet of original Kpt types using
   the real ancestor/raw correspondence and cut-level meet geometry.
C. Instantiate the verified stage closure normal form at a real
   even numerical cut, under explicit (S),(R),(0).
D. Only after B/C build the no-I1/no-I2/no-I3 physical cut result,
   preserving all descending Plan and seed assumptions.

This note is a candidate proof, NOT a Lean validation marker. Any
unresolved technical premise must remain stated rather than
silently discharged in the manuscript.
