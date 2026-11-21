# Track B: finite target-age normalization and a late coding pivot

## Status and scope

English proof written before Lean on 21 November 2026 and committed at
[`69dafd21dfbeb2923d204a106d860e2c2910657a`](https://github.com/janhubicka/lean-kk/commit/69dafd21dfbeb2923d204a106d860e2c2910657a).
Three independent reviews accepted the finite normalization argument; two separately checked
the late-pivot neighbourhood and chronology argument before implementation.
This note addresses finite ordinary graph ages over the entire protected
original prefix.

**Verification status: complete hosted gate passed.**
[Run 44920690130](https://github.com/janhubicka/lean-kk/actions/runs/44920690130),
[job 136895846770](https://github.com/janhubicka/lean-kk/actions/runs/44920690130/job/136895846770),
passed the 9,738-job Lean build, parser self-test, and **990 exact named
transitive-axiom reports**, with seven axiom-free reports and all other axioms
drawn from `propext`, `Classical.choice`, and `Quot.sound`. The immutable source
is `69983310fc1acd65a31c9d99cbc6f56ffb796532`; the actual tested merge is
`147bd10c6372839c77bc0df52ffeb0583dea3b90`. Their trees differ because of newer
main additions, but all Track B proof files and pinned dependencies are
identical. The source's 989 report names remain in order; one independent main
endpoint gives the tested total of 990. The
[evidence record](audits/2026-11-21-track-b-controlled-preage.json) records the
exact trees, changed integration files, dependencies and all reports.

The three modules
`FiniteTargetAgeNormalization`, `LateControlledPivot`, and
`FiniteControlledNormalization` register nine endpoints: actual support-block
normalization, a complete-neighborhood certificate, a later actual pivot,
and a shared finite coding stage. The companion
[controlled-pre-age/prospective construction](track_b_controlled_preage_english_audit_20261121.md)
adds 19 endpoints and discharges the target construction and domination
premises for its computed prospective age. The combined addition therefore
has **28 new endpoints** beyond the previous 961-report checkpoint. The pure
constructor module passed a direct local check; no completed local
full-project gate is claimed.

The strongest final interfaces no longer require a supplied target `C`,
prepared-age equality, desired `C ≤ P`, pointed budget, or numerical pivot.
They compute the prospective survivor age, derive its controlled pre-age,
construct raw equality, and only then select the actual coding original.
The [independent finite referee](../scripts/verify_track_b_controlled_preage.py)
separately reports 4,330 actual graph normalizations and 12,744 complete raw
support equalities in its stated finite domains, including a specified
nonzero-edge, zero-column gap pattern. This is finite regression evidence,
not a replacement for the Lean gate.

No prescribed saturated-cover diary, full parameter-closed Kpt/auxiliary E
history, (I1)–(I3)/corrected-(B3) transport, common labelled inverse-source orbit,
or infinite construction is asserted. The earlier general residual-vector
operation remains English-only. The finite normalization may create extra
selected-front events; preserving the required history through those events
is still an open task.

The physical theorems explicitly assume the Boolean `OnePointLeftDense`
property. The adapter identifying that hypothesis with the manuscript's
abstract enumeration/density formulation is not established here.

The fixed Boolean graph E is a normalized K_ell-free Henson graph with the
explicit OnePointLeftDense property already used by the existing physical
stage theorems. Assume ell >= 2. Every currently committed selected, reserved,
and parameter original lies below the initial cutoff b. Future sorts are
symbolic: their complete prescribed columns on [0,b) are c(p,t).

## 1. Normalize to any genuine lower age by finitely many support cliques

Let C be a genuine positive integer graph age on the finite sort set D, and
suppose C <= B_b, where B_b is the raw common-neighbour bound of the complete
old column c on [0,b). This follows in particular from C <= P when
P = G_(B_b). There exist a finite cutoff F >= b and complete extended columns
c' such that c'(p,t)=c(p,t) for every p<b and every t, and

    B_F(c') = C.

Consequently G_(B_F(c'))=C, with every earlier prescribed column retained.
This is an exact RAW equality, stronger than canonical equality alone.

For each admissible nonempty support T, set r_T=ell-1-C(T). Choose a fresh
original clique Q_T of size r_T above the current cutoff and isolated from
the ENTIRE current original prefix. The existing Henson reserved-clique
theorem supplies it, including all original enumeration gaps. Set the column
of every q in Q_T to the indicator of T; keep all earlier columns; set all
new gap columns to zero. A block of size zero may be skipped.

The exact isolated-support raw update already proved in the repository is

    B_new(U) = min(B_old(U), C(T))  if U is a subset of T,
             = B_old(U)           otherwise.

Indeed the common-neighbour clique capacity is the maximum of the old
capacity and r_T when U is a subset of T. All old-to-new-block edges vanish,
so it is a maximum, not a sum. Since C(T)<=ell-1, subtracting this maximum
from ell-1 gives the displayed minimum, including natural subtraction.

Genuine graph ages are monotone under support inclusion. Hence C(U)<=C(T)
whenever U is a subset of T. Thus C<=B_new whenever C<=B_old. At U=T the
new raw value is exactly C(T). The raw update never increases a value, so
every previously attained equality B_old(U)=C(U) remains an equality.

Process the finite collection of all admissible supports. Induction gives
C<=B throughout and equality on every processed support. At the end all
raw values equal C. Every step retains all columns below its current cutoff,
so the final table retains the entire initial prefix and the columns of all
earlier blocks. No already chosen original or original graph edge moves.

Equivalently, in the final pool the raw bound is

    min(B_b(U), min_{T containing U} C(T)) = C(U),

because the list contains T=U. The sequential proof avoids interpreting a
minimum over an empty collection and handles the empty sort set uniformly.

This construction may contain redundant blocks and may cause intermediate
age drops that are not covers. It proves finite target-age normalization,
not the manuscript's exact requested saturated-cover event sequence. The
latter remains a separate refinement and history obligation.

## 2. Positive singleton age certifies the complete pivot neighbourhood

Let j be an active symbolic sort, and suppose the canonical age at a complete
prefix b has positive value on {j}. Let

    P_j = {p<b : c(p,j)=1}.

Canonicalization is below the raw bound, so

    1 <= G_(B_b)({j}) <= ell-1-rho_E(P_j).

Therefore rho_E(P_j)<ell-1. This excludes every K_(ell-1) in the COMPLETE
prescribed neighbourhood, including mixed cliques involving older parameters
or several historical roles. Neither small cardinality of P_j nor a
separate admissibility hypothesis is needed.

## 3. Choose the actual pivot after the finite preparation

Fix any requested lower cutoff N and put D=max(b,N). Extend every active
column by zero after b: c0(p,t)=c(p,t) for p<b and zero otherwise. A positive
neighbour under the proposed pivot column c0(p,j) necessarily lies below b.
Section 2 therefore proves that the one-point extension at D is K_ell-free.
The old prefix [0,D) is K_ell-free by the fixed Henson hypothesis.

Apply OnePointLeftDense once. It returns an actual v>=D with

    E(p,v)=E(v,p)=c0(p,j)  for every p<v.

This includes every zero in [b,v), not just zeros at selected gap names. The
existing neutral-column theorem gives exact raw and canonical equalities
between the b-prefix and v-prefix for all nonempty supports. Thus the
chronological pre-age at v is the intended age, rather than an independently
assumed history invariant.

If this age has the controlled cap and growth properties, the already
verified controlledCoding_next_prefix_canonical_eq applies at this SAME
chosen v. For an arbitrary parent map pi and passing bits beta whose positive
parents lie in the controlled passing set, the age at v+1 is exactly
U |-> C(pi[U]). All complete prepared columns are retained. The existing
finite Henson realization then supplies one later common future, embedding,
and numerical cutoff for all normalized profiles (when there is a nonempty
remaining sort set).

Combining Sections 1 and 3 first normalizes a genuine controlled C below the
initial raw bound, then chooses and codes the pivot. It does not choose a
numerical pivot before the support blocks.

## Adversarial checks

1. **Whole prefix.** The initial cutoff contains every committed original.
   Selected-front data alone is insufficient; a mixed old-parameter clique
   could invalidate the pivot. No protected old column is discarded.
2. **Previously fixed future vertices.** Zero extension is not allowed to
   overwrite positive columns of originals already fixed beyond b. Such
   originals must first be included in the protected prefix and target data.
3. **Same eventual pivot.** The late vertex is chosen once, after preparation,
   and that exact vertex is passed to the controlled-coding theorem.
4. **No chronology reversal.** This construction cannot insert a block before
   a numerical pivot that was already fixed. Its premise keeps the pivot
   symbolic until all finite blocks are constructed.
5. **Mixed old/block cliques.** Each block is isolated from the whole earlier
   prefix, not just other new blocks. Thus the capacity update is a maximum.
6. **All new zeros.** Every enumeration gap has zero columns for all active
   sorts. Arbitrary graph edges incident with gap originals cannot then put
   them in a nonempty common-neighbour pool.
7. **Subset side effects.** A support-T block changes all U subset T, not only
   T. Monotonicity C(U)<=C(T) is the reason it cannot destroy the target age.
8. **Integer subtraction.** C(T)<=ell-1 gives ell-1-r_T=C(T). Positivity makes
   r_T<=ell-2, so the required reserved clique is strictly smaller than ell.
9. **Zero-sized blocks.** When C(T)=ell-1, C<=B and B<=ell-1 already force the
   target equality. Skipping that block is legitimate.
10. **Empty sort set.** There are no admissible nonempty supports, so the
    normalization theorem is vacuous and needs no invented sort. A pivot
    theorem necessarily has a supplied j and hence a nonempty initial set.
11. **ell=2.** Every genuine age value equals one and all r_T vanish. A positive
    pivot singleton forces an empty old neighbourhood, as required.
12. **Finite versus prescribed diary.** Exact final raw age does not establish
    which intermediate levels are covers, boring, or carry the required
    dependent Kpt sources. The normalization theorem is not labelled as that
    stronger diary theorem.
13. **Source of C.** This note requires a genuine target age below the old raw
    bound; it does not assume that an unspecified future coding event supplies
    it. The separate controlled-pre-age constructor and prospective-event
    argument must establish this premise without circularity.
