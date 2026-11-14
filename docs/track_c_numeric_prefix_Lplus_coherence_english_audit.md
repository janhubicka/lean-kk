# Track C — physical finite numerical H+ prefix coherence in the COMPLETE L+ language

**14 November 2026 — English proof + adversarial audit, COMMITTED BEFORE Lean.**
Parent: exact main `b93d5fe1c5cd421a9202b3b0607683308587e426`, which includes Track C PRs #128/#131/#133/#135 merged. The fixed numerical generation parameter k, base age model K and forbidden family are unchanged; the only varying parameter is the finite carrier bound `N≤M`.

## Motivation: a genuine geometric bridge, not a source-name wrapper

The bounded resolved-copy proof (manuscript `kk.tex`, Section 6 proof of Lemma `Lem:Kk_Resolved_Copy`) reserves genuinely new original vertices in an ever-longer finite numerical H+ scaffold. The already checked one-stage pool theorem `finiteNumericH_multiRoot_nextSeed_pool_preserved` stays **inside one fixed ambient finite H+**. To iterate it through growing carrier bounds, we must check the old genuine Kpt sources and ALL their auxiliary E data survive the extension `finiteNumericH K k N → finiteNumericH K k M`.

The point is not automatic: the `finiteNumericHE` constructor **clips by the E TARGET** `y<N`, whereas its L-reduct binary/unary/diagonal atoms are independent of N. A careless claim of equality for arbitrary cut types is false: a larger cut can include a new E target `w∈[N,M)`. The correct theorem preserves complete types at old cuts `cut≤N` around original vertices `v<N`.

## C27: exact E restriction on old targets, even from arbitrary E sources

Fix K and k, and `N≤M`. For every u∈Nat and v<N,

`(finiteNumericH K k N).E u v = (finiteNumericH K k M).E u v`.

**Proof.** Both are literally `finiteNumericHE k _ u v`. Because the SAME target v is in both finite carriers, both guards are true; both values are the unchanged exact generator `exactHEBool k u v`. There is no restriction on u (E source), a stronger result than old-old table equality.

Hostile test: if v≥N, the old finite structure has `E u v=false`; the new one can have `E u v=true`, so the `v<N` guard is genuinely necessary.

## C28: exact canonical E free-cut stability of old originals

Under the same `v<N≤M`, the canonical free levels are **equal**:

`(finiteNumericH K k N).freeLevel v = (finiteNumericH K k M).freeLevel v`.

**Proof.** The first finite model's unique free cut c obeys
`IsFreeCut E_N v c`, including **all** lower positive E atoms and the
first false atom. C27 transports the entire incoming column to E_M,
so c is also a free cut there. The verified `freeCut_unique`
identifies c with the larger model's canonical cut. We do NOT
infer free-cut equality merely from agreement of L-adjacency.

## C29: complete old partial L+ types survive enlargement

For EVERY `cut≤N` and `v<N`, the full dependent types agree:

`(finiteNumericH K k N).partialTypeAt cut v =
  (finiteNumericH K k M).partialTypeAt cut v`.

**Proof.** The L-reduct is literal, unchanged
`hNumericBinary K.binary k` and `hNumericSingleton` unary/diagonal
for BOTH cardinal bounds. Every `Option(Fin cut)` coordinate has
physical target either an old numeric socle index `u<cut≤N` or the
same type vertex `v<N`. Thus all E targets lie below N.
C27 gives equality for ALL directed auxiliary E pairs. Apply
`PartialTypeWithE.eq_of_atoms` and
`RelationalPrefixType.eq_of_atoms`, preserving every positive and
negative binary L atom, both tuple directions, every unary and
diagonal atom, and every directed auxiliary E bit.

**Adversarial guard.** We must not remove the `cut≤N` restriction.
For `cut>N`, the old structure's `E` is zero on a new target
`w≥N`, while `E_M` may have an incoming positive predecessor.
The theorem is about *complete old Kpt source records*, not arbitrary
unbounded pseudo-types on a cutoff past the old carrier.

## C30: the FULL old Kpt original is identical across prefix extension

For v<N, C28 and C29 with cut=`freeLevel_N(v)≤v<N` imply equality of the raw original full L+ nodes `rawTypeAtFree v` in both finite models. With actual forbidden avoidance witnesses `hAvoidN` and `hAvoidM`, the admissible Kpt original subtypes themselves are EQUAL, not merely their ordinary-L reducts:

`(finiteNumericH K k N).kptOriginal family hAvoidN v =
  (finiteNumericH K k M).kptOriginal family hAvoidM (Fin.castLE v)`.

Subtype proof irrelevance removes dependence on the different finite-model admissibility certificates. This is the precise physical source preservation needed for parameter-closed Kpt geometry.

If both witnesses are derived from a single base K by the existing
`finiteNumericH_avoids_family` theorem, no extra arbitrary
avoidance axiom is introduced.

## C31: old seed prefix pools and selected-positive stage pools transport

Let U⊆Fin N and X be arbitrary actual Kpt seed nodes such that
`X⊆ambientPrefixPool family A_N hAvoidN U`.

Define `lift U : Set(Fin M)` as the image of U by the physical
address inclusion `Fin.castLE (N≤M)`.

**Claim.** `X⊆ambientPrefixPool family A_M hAvoidM (lift U)`.
For each represented old seed z, choose its genuine old
original v∈U and use C30 to replace the old original Kpt node by
the larger model's **equal** original node; no new choice of E
columns, Kpt source or parameter is needed.

Moreover for any stage selected set I⊆Nat, membership in the
old `ambientStagePool A_N U I` transports to membership in
`ambientStagePool A_M (lift U) I`. Old selected-positive parameter
originals keep precisely their free cuts by C28. New extra selected
parameters in the larger model are permitted, but we do NOT claim
the two stage pools are equal unless all selected physical
addresses are still below N.

Consequently the actual complete Kpt meet-and-parameter closure
of the **same** X and I (whose node type is independent of N) is
represented in the larger physical model's genuine original pool,
via the successor-tree closure invariant. This does not
assume a cross-presentation monoid isomorphism.

## Hostile tests / explicit nonclaims

1. Fixed K and fixed k are essential. Changing k changes `hPosition`, the generation gate in L, and the E columns. The theorem is NOT a k→k+1 induction.
2. Only the carrier bound N increases. In particular new reserved originals belong to M, but their exact backward columns still require separate Henson left-density realization.
3. Incoming E is clipped by its target, not its source. C27 holds for all u once v<N; do not assume u<N.
4. For an E target v≥N, C27 generally fails; do not assert equality for all target coordinates.
5. Full partial-type preservation requires old socle cuts `cut≤N`; drop this and E on the new socle may differ.
6. v must be in the old carrier. The new partial type may use an original which did not exist before, which has no old source counterpart.
7. Canonical free levels are unique E cuts and their equality uses all directed E atoms, not selected-front adjacency.
8. The raw Kpt original is at its **E free level**, not at numeric coordinate v itself; using v for the level would be wrong.
9. Every negative L and E bit remains literal in the complete source, including fake odd E-predecessor coordinates below the old cut.
10. Equality of admissible Kpt original subtypes must use proof irrelevance for the two different ambient avoidance witnesses, not identify those witnesses as propositions in different finite models.
11. Old seed prefix representation requires actual old Kpt originals; an arbitrary raw type over N does not automatically belong to their prefix pool.
12. The lifted root image is injective, but image equality across stages is not asserted without an explicit root-set identification.
13. A selected positive original v<N survives enlargement; additional selected addresses in [N,M) enlarge the stage pool. Never claim old=large pool.
14. The K4 cuts 10 and 22 can still be genuine auxiliary I3 events. Prefix stability alone does not render them boring.
15. A growing finite prefix does NOT by itself construct the unbounded resolved-copy schedule, verify negative clique neighbourhood certificates for new selected originals, or establish the exact labelled event sequence.
16. No cross-occurrence full source-orbit comparison, uniform envelope bound, or exact big Ramsey degree follows from this geometric prefix lemma.

## Validation gate and ownership

Formalize in an independent Track C module
`Kk/NumericHPrefixLPlusCoherence.lean` with eight scoped theorem
endpoints: exact E, free cut, full L+ partial types, raw full
originals, Kpt originals, root and stage-pool transport.
Use an English-first committed proof and independent exact-head
isolated `lake build`, every theorem's named standard-only
axiom report, plus a matching full-project CI run. Do not
modify `Kk.lean`, shared axiom registry, manuscript
`kk.tex` or existing validation marks (owned by Track G).
