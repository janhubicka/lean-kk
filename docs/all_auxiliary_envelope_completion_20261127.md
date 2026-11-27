# Actual finite envelopes retaining every auxiliary event — 27 November 2026

## Outcome

The actual finite-envelope application now has a specialization with no
caller-supplied age, no-split, seed-coverage, retained-seed-level or cap
choice. Its seeds are the full original types of a requested finite set
of original indices together with the explicitly constructed fresh cap.
Every auxiliary event is retained.

The strongest endpoint is
`Kk.resolvedInitialAllAuxFiniteSelection_envelope`. Its input is an
ordinary Boolean graph on Nat, with symmetry, looplessness and the
finite K4-free clique bound, and any finite original selection S. The
actual initial stage and its empty old pool are supplied by construction.

The theorem derives the two ordinary hypotheses that remained explicit
in the [previous finite-front batch](finite_selected_front_completion_20261127.md).
It also supplies the seed and pool data for the stated full-original seed
set. This is an actual finite envelope for these constructed data.

Retaining every auxiliary event may retain a number depending on the
selected indices. The proof gives no bound on the complete retained
record in terms of |S|. Controlled retention, a projected-diary parser,
common inverse sources and the sharp Ramsey characterization remain open.

## Completed local verification

| Gate | Result |
|---|---|
| Normal default `lake build` | **PASS**, exit 0, **4,134 jobs** |
| Normal target importing all five new modules | **PASS**, exit 0, **3,624 jobs** |
| Central Lean audit and strict named-report parser | **PASS**, **1,511 exact reports** |
| Three focused Lean audits and strict parsers | **PASS**, **41 reports**, all names and axiom sets agree with central |
| Axiom-parser self-test | **PASS** |
| Module-coverage parser tests | **PASS**, all three cases |
| Source/import audit and diff checks | **PASS** |

All 1,470 preceding names and their axiom sets are preserved. The entire
old central script remains a literal prefix. The 41 additions cover every
public theorem in the five new modules. Fourteen central reports are
axiom-free; the others use only `propext`, `Classical.choice` and
`Quot.sound`. No custom axiom or `sorryAx` is accepted. The theorem counts
measure audit coverage, not a percentage of the outstanding mathematics.

The [machine-readable evidence](audits/2026-11-27-all-auxiliary-envelope-completion.json)
records all 805 source/audit/configuration hashes, all 1,511 named axiom
reports, the fourteen final execution outcomes and log hashes, and the
resolved dependency pins. Its baseline is
`ce360818a01188c810d221c2271c9c61f294b235`.

Validation used Lean **4.35.0-rc3**. All eleven dependency pins are the
same as in the preceding batch, including successor tree
`a74c10761303a18649053f2af3a1a1697f032e13`, Ramsey space
`f471b640f11e6b35fbbc3ad74dfa93df5ec3eadc`, and Mathlib
`5bd58ac291422a21f412ae354c91e7d172255a2c`.

The default root reaches **555 of 733 Kk modules**, plus the root itself.
All five additions are included. The unchanged 178 standalone/audit
modules remain outside this normal-build claim. The coverage scan finds
no missing local imports or suspicious source tokens.

English arguments were independently reviewed before implementation.
Completed source, cross-module assembly and static integration reviews
passed. This report records local verification; the consolidated pull
request supplies subsequent hosted and merge evidence.

## Five modules and their contributions

| Module in Kk/ | Public theorems | Contribution |
|---|---:|---|
| `OneGapAgeTransport.lean` | 12 | Exact finite induced-image transport, removal of dummy rows, complete raw/canonical before-and-after age identities, and old-column/no-split transport. |
| `ResolvedFairCodingNeutrality.lean` | 8 | Actual chosen coding-event certificates, exact chronological old-pool images, canonical-age neutrality and no-split for arbitrary later original terminal lists. |
| `ResolvedFairAuxiliarySelection.lean` | 7 | Classification of omitted roles when all auxiliaries are kept, actual coding-address recovery, and original-index decoding/survival of the eligible selected front. |
| `ResolvedFairOriginalSeeds.lean` | 7 | Genuine full-original seed types, derived source-pool coverage, level bounds and retention, and the constructed augmented original pool. |
| `ResolvedFairAuxiliaryEnvelope.lean` | 7 | Padded coding results, derived neutrality/no-split for the actual retained front, and full envelopes for original seed pools and finite original selections. |

Existing Kk theorem files are unchanged. The root adds the final assembly
import, and the central audit adds the 41 named endpoints. The manuscript
and dependency pins are unchanged.

## Why retaining all auxiliaries closes the ordinary application

With coding selection S+, a dummy role is retained, a coding role is
retained exactly when its original index is selected, and every auxiliary
role is retained by the chosen constant-true flag. Consequently an
unretained role must be coded false. At an omitted meaningful cut below
the cap, the finite retained-level theorem gives precisely such a role.

The previously proved inverse coding correspondence identifies this cut
with the actual padded address a(n) of an unselected original n. Every
entry of its actual eligible selected front is a(m) for a selected
original m. Free-level eligibility puts a(m) strictly beyond the cut;
strict increase of the original-address map then gives n<m. Each front
terminal therefore survives the actual coding event of n.

The terminal list is the actual eligible front at that cut. It is not
replaced by all selected originals. The coding transport accepts any
finite list of later originals, including repeated indices and the empty
list, so the cut-dependent front causes no extra hypothesis.

## Actual chronological transport and the padding argument

The coding proof eliminates the certificate of the actual chosen event.
Its saturation, exact class labels and coding constancy belong to that
event's own preOld pool and edge relation. It does not choose another
existential round witness and identify the two without proof.

The chronological event-vertex map is injective under the explicit empty
initial old-pool condition. The exact prefix-image theorem identifies
range(p(n)) with the coding event's preOld pool. The singleton coding
block identifies range(p(n)+1) with postOld. Localized event agreement
supplies all old-old edges and old-terminal columns used in the two
finite ages. No agreement outside that actual domain is required.

Finite induced-image transport preserves each common-neighbour clique
capacity, hence the complete raw-bound function and its integer
canonicalization. The coding certificate then gives equality of the
two complete canonical ages. No raw coding-age neutrality is asserted.
The analogous complete-column transport and coding constancy give
no-split.

For padding, every dummy row has zero column against the meaningful
terminals. Every IntegerGraphSupport is nonempty, so no dummy row can be
a common neighbour of a support. The remaining common-neighbour pool is
exactly the address image of the unpadded pool, with the same directed
clique capacity. This proves equality of every raw support bound and
therefore the complete canonical-age function.

The exact cutoffs are range(a(p)) before the meaningful coordinate and
range(a(p)+1) afterwards. Their unpadded counterparts are range(p) and
range(p+1). In particular the argument does not replace a(p)+1 with
a(p+1). Complete old-column equality is also preserved because all
inserted dummy rows have two zero bits.

## Concrete original seeds and the assembled theorem

Let A be the actual finite prefix through the cap, and let U be any
subpool of its constructed retained-role pool V. Define

```text
X = image of U under A.kptOriginal.
```

A full original type belongs to its own ambient prefix pool. Its level
is exactly the original's actual free level, which is bounded by its
coordinate and hence by the cap. The retained-pool free-endpoint theorem
puts that level in I. These facts derive all seed inputs from U subset V.
This inference is specifically for full original types: a proper prefix
can lie at an omitted level.

For the final finite-selection specialization, U is constructed from
the typed addresses of S+ = S union {cap}. Every such address belongs to
V by the proved finite-selection membership theorem. The cap is included
even when S is empty. No external seed or pool choice remains.

The resulting F satisfies StageFullInvariant for this X and has exact
level range

```text
F.map.levelRange = {q | q belongs to I or top < q}.
```

The direct initial-graph endpoint supplies the actual stage from a
symmetric loopless K4-free E. Thus age, no-split, seed coverage, retained
seed levels and cap choice are conclusions for the constructed data.

## Remaining application obligations

1. **Controlled auxiliary retention and a legal projected diary.** Prove
   a uniform complete-record bound, parser legality, and neutrality/seed
   compatibility for the reduced retention choices. The all-auxiliary
   envelope proved here does not supply that uniform bound.
2. **Common full labelled inverse sources and upper transfer.** Equal
   macrodiaries must determine the complete retained ordinary tables,
   auxiliary atoms, marked positions and cap under genuine Kpt maps.
3. **Direct history occurrence, unavoidability and matching lower bounds.**
   The exact copy-degree targets 24 and 120,487 remain open.
4. **The actual general-K_ell construction.** The generic padding lemmas
   work for arbitrary ordinary tables; the fair graph constructor and
   final application here remain K4-specific.

## Proof notes and focused audit inputs

The English proofs are in
[all-auxiliary assembly and original seeds](all_auxiliary_envelope_english_20261127.md),
[chronological coding neutrality](resolved_fair_coding_neutrality_english_20261127.md),
and [one-gap age transport](one_gap_age_transport_english_20261127.md).

The three focused scripts partition all 41 additions:
`check_axioms_one_gap_age_transport.lean` (12),
`check_axioms_resolved_fair_coding_neutrality.lean` (8), and
`check_axioms_all_auxiliary_envelope.lean` (21).
