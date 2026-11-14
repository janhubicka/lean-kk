# KK-free Track E — construct both *physical* growing-height runs and a finite extra-cut witness

**14 November 2026.** English mathematics and adversarial audit committed **before** the Lean module.

**Base:** independently exact-head verified Track E [PR #203](https://github.com/janhubicka/lean-kk/pull/203) (head `6e8b19c51e47f7de54f2abcd7951dc267b5844d9`, seven strict standard-only reports, full build passed). This new branch is stacked on #203. The source below uses genuine physical Track C new-root theorems already merged to main; do not edit the protected KK manuscript or central Lean imports.

## 1. What is newly discharged

Previous E cross-height novelty needs two true AlgorithmRuns `RunOld : AlgorithmRun H X oldTop` and `RunNew : AlgorithmRun H Y newTop`, genuine old top seed, `oldTop ≤ newTop`, and a true complete **finite** physical index of the new run.

Track C already constructs all this geometry on the new side from an actual finite numerical H+ new-root stage. Here we **compose the actual physical constructor with the cross-height source-witness theorem** and derive the previously unproved old-top height inequality rather than assuming it.

Let the physical old/new numerical H+ structures be

`A=finiteNumericH K k N`, `B=finiteNumericH L k M`,

where `N≤M`, `N≤hPosition k b 0`, k>0, j>0 and `hPosition k j k<M`. Assume the actual old base K and new base L have identical directed binary/unary/diagonal columns below b and both genuine numerical H+ ordinary reducts avoid the same normalized forbidden family. Assume the true old Kpt seeds X are contained in the prefix pool of actual old Kpt originals indexed by U⊆Fin N.

Let `oldTop` be the old run's actual top and assume `HasPhysicalExhaustiveKptRun family X oldTop`. This supplies a **genuine old AlgorithmRun** and a **real old-top seed x∈X** of Kpt level oldTop. It also supplies a separate finite old source index, although the present theorem does not need to compare the two index universes.

Finally assume the real chronology inequality

`N ≤ newTop := hPosition k (j-1) k+1`.

Take the actual newly inserted physical original `w : Fin M := ⟨hPosition k j k, hTarget⟩` and the **corrected original-only seed family**

`Y := closure_{RunOld.I0}(X) ∪ {B.kptOriginal(w)}.`

No prefix of the new original is pre-inserted as a separate initial seed: the entire prefix pool is only a *representation cover*, not an initial seed set. This respects Track C's verified full-prefix-saturation counterexample.

### Height lemma — oldTop≤N≤newTop

Choose the REAL old top seed x∈X with lev(x)=oldTop. From the old physical prefix-pool representation choose actual original v∈Fin N with x≤A.kptOriginal(v). The Kpt level order and the verified exact physical free-level inequality give

`oldTop = lev(x) ≤ A.freeLevel(v) ≤ v.val < N`.

Hence `oldTop≤N≤newTop`. In particular there is **no extra cross-height monotonicity assumption**: the chronological N≤newTop and the genuine old-top seed discharge it. No inference of an old-top bound from the formal topI marker alone is allowed.

### Actual new-run and finite-source construction

Track C's verified `finiteNumericH_baseExtension_actual_top_root_run_bounded` constructs, for this exact Y:
- a **real canonical Kpt AlgorithmRun** `RunNew` with scan top newTop and an actual new-top seed;
- one finite set `params` of **all** final true Kpt closure nodes (including old meets, new meets, dependent parameters, auxiliary E);
- a Boolean cutwise activity mask `live(c,j)` which exactly represents every actual pre-cut closure;
- a genuine bounding certificate `Y⊆levelLe(newTop)`.

The old run is obtained from its *physical exhaustive* witness, not invented. The new run, source index and live mask are obtained from the real physical root constructor, not assumed.

### Main exact theorem

Construct `RunOld`, `RunNew`, `params`, `live`, `Y⊆levelLe newTop`, and exact final index coverage, such that for EVERY cut `c<oldTop`:

If the actual new run selects c but the old run skips it, then there is a **LIVE index** `i:Fin params.card` witnessing either

1. `node(i)∈Znew(c)\Zold(c)` with `lev(node(i))=c`, or
2. a full old/upper L+ type pair `(T,U)` from that SAME live Kpt node, missing from the old full physical crossing relation of `Zold(c)`.

This is exactly `IndexedNewSourceCutWitness` on the genuine new physical finite node index. The proof uses `X⊆Y`, `oldTop≤newTop`, the genuine old top seed and the **kernel-checked cross-height indexed-novelty theorem** from E PR #203. The actual source index at c is the one obtained from Track C's verified `hCover c`; its coverage is not only of selected originals or a guessed diary front. Multiple I2 forks and all E atoms are retained.

The theorem **does not assume** the real new run or its finite index exists. It does assume the physically legitimate old-run witness and the real K/L column agreement and forbidden avoidance needed to construct a true numerical H+ new-root stage.

## 2. Optional bare-source refinement at one old cut

At a particular `c<oldTop`, let `I=RunOld.I(c+1)` (note: this now makes Y dependent on c). The corrected physical root constructor still builds the true new run on `Y_c=closure_I X∪{new original}`. The genuine cross-height monotonicity gives `I⊆RunNew.I(c+1)`, so Track C's least-closure absorption proves

`closure_{RunNew.I(c+1)} Y_c = closure_{RunNew.I(c+1)}(X∪{new original}).`

Consequently any novel full source pair/terminal event below oldTop is already generated by **bare old+new ORIGINALS**, not by bookkeeping preinsertion. This is the precise stage-level attribution intended for a diary extension; however, `Y_c` depends on c, and it is invalid to claim ONE global Y has this property at every cut without the appropriate generating-level restriction.

The optional refinement can be formalized separately after the main constructed physical run lemma compiles; keep the two mathematical scopes distinct.

## 3. Hostile audit

1. **Real old top seed:** without a genuine x∈X of lev oldTop, a taller run can skip the purely formal oldTop marker. `HasPhysicalExhaustiveKptRun` explicitly provides it.
2. **Chronological inequality:** no accidental inference `oldTop≤newTop` from `oldTop≤M`. The proof goes through old seed → old physical original prefix → old carrier bound N → actual new free cut newTop.
3. **Exact original-only new seeds:** do **not** use `ambientPrefixPool B {w}` itself as initial new seeds; that false construction forces every lower I1 level.
4. **New physical column safety remains assumed:** `hAvoidL` and the old K/L column equalities are real conditions, not automatically generated by any arbitrary graph extension.
5. **Both runs real:** old run is destructed from `HasPhysicalExhaustiveKptRun`; new run/index come from Track C's actual bounded new-root theorem. Never select arbitrary shape maps.
6. **No false alignment across unrelated generations:** one fixed numerical generation k and one normalized Kpt tree are used; genuine comparisons of different k remain open.
7. **Only cuts c<oldTop:** at/above oldTop, the old descending AlgorithmRun does not have the required actual interesting_step. A taller run may select many levels above oldTop.
8. **Complete full L+ source:** the activity mask covers ALL real Kpt meets/dependent parameters, and each crossing pair's old and upper Options belong to the SAME node. Auxiliary E/fake predecessors are included.
9. **Forks allowed:** no functional prescribed-B3 assumption and no artificial choice of one upper type at an actual I2 fork.
10. **Not a no-novelty theorem:** physical new roots can and often do create new I1/I2/I3 cuts. The conclusion identifies finite concrete witnesses, not that all extra cuts are intended diary events.
11. **No uniform finite carrier:** params.card may depend on M and ambient roots; this is a FINITE run certificate, not a uniform bound for all embeddings.
12. **No common fully labelled orbit:** a selected-level comparison or novel-event index does NOT identify all selected vertex labels and dependent parameter nodes under genuine common outgoing monoid maps.
13. **True source rank:** K4 q2 auxiliary cuts 10/22 remain possible; the theorem does not compress away unplanned cuts.
14. **Inherited parameter closure:** the whole old closure is retained, but it can generate new events at lower levels until actual old-level retention and bare absorption are proved at those cuts.
15. **History vs rerun:** the old run is a supplied real physical witness, not automatically identical to a previous run at a different physical top; this is why we use oldTop actual Kpt source data rather than raw topI.
16. **No global BRD assertion:** the main `Kk_Diary_Determines_Envelope`, uniform finite-carrier and upper bound remain PENDING; no protected manuscript green mark.

**Verification plan:** `Kk/PhysicalCrossHeightConstructedWitness.lean`, standalone `Kk/TrackEPhysicalCrossHeightAxiomAudit.lean`, isolated exact-head full module compile and strict named standard-only `#print axioms` report, plus independent ordinary `lake build`. Keep the PR DRAFT, stacked on verified E #203; don't alter central `Kk.lean`/scripts or black `kk.tex`.
