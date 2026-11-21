# Track B: arbitrarily many finite physical canonical-age covers

## English proof, before Lean

**Scope.** Work in one unchanged normalized, left-dense \(K_\ell\)-free original
graph \(E\), with \(\ell\ge2\) and a fixed positive number \(d\) of future
sorts. Let \(A_i\) (\(0\le i\le m\)) be given normalized integer graph ages.
For each \(i<m\), assume an actual *cover*
\(A_{i+1}\lessdot A_i\), a nonempty critical support \(T_i\), and a natural
number \(r_i\) satisfying
\[
 A_i(T_i)=A_{i+1}(T_i)+1,\qquad
 \ell=A_{i+1}(T_i)+r_i+1.
\]
In particular, \(r_i>0\): otherwise the old value would be \(\ell\), contrary
to the graph-age range \([1,\ell-1]\).

Suppose the complete original typed columns \(c_0(p,t)\), for **every**
\(p<b_0\), have canonical age \(A_0\). Fix any finite sequence of generation
parameters \(k_i\).

**Finite final-stage theorem.** There are \(b_m\ge b_0\) and complete columns
\(c_m\) over *all actual originals* below \(b_m\) with
\[
c_m(p,t)=c_0(p,t)\quad(p<b_0),\qquad
G_{B(E,[0,b_m),c_m)}=A_m.
\]
The construction is made by \(m\) consecutive genuine physical reserved-clique
stages in the **same** original graph, not by declaring abstract raw bounds.
At each stage, the existing one-cover theorem constructs a real clique
\(Q_i\subseteq[b_i,b_{i+1})\), with \(|Q_i|=r_i\), nonadjacent to the complete
earlier original prefix (in both directions), and sets:
- every \(p<b_i\): retain the complete old column \(c_i(p,t)\);
- every \(q\in Q_i\): make its future column positive precisely on \(T_i\);
- every other genuine original in \([b_i,b_{i+1})\): give it the zero column.

The verified one-cover theorem gives the exact full-prefix canonical equality
\(G_{B(E,[0,b_{i+1}),c_{i+1})}=A_{i+1}\), not merely an equality of selected
shadows. This equality is exactly the hypothesis required to apply the theorem
at the next cover. Induct on \(m\). Every earlier reserved block lies inside
the new protected old prefix and keeps its full future column. The first
\(b_0\) complete columns are therefore unchanged by composition.

The same one-stage theorem separately supplies one numerical-H tagged future
realizing **all** normalized feasible clique profiles at stage \(i\). These
stage witnesses may differ with \(i\): no one common embedding of all earlier
tagged futures is constructed. The proposed Lean interface records the final
cutoff, full initial-prefix column preservation and exact final canonical age;
its proof calls the physical one-stage theorem at every index.

## Adversarial audit (17 checks)

1. Every intermediate \(A_i\) is a genuine age: this is contained in the
   age-cover data, not inferred from a pointwise decreasing numerical table.
2. The input is an explicit finite *saturated cover chain*. Existence of a
   particular chain required by a resolved diary is not asserted.
3. \(r_i>0\) follows from both the strict one-unit drop and the upper age bound;
   an empty block cannot be used to infer a later cutoff.
4. The actual \(K_\ell\)-freeness and one-point left density of the unchanged
   graph are inherited at every stage; no fresh ambient graph is substituted.
5. The support \(T_i\) is nonempty and admissible by its support type.
6. The raw effect of \(Q_i\) may affect **all** subsets of \(T_i\), not solely
   \(T_i\). The verified canonical cover theorem, not false pointwise raw
   equality, proves the exact age update.
7. All real enumeration gaps are present in \([0,b_{i+1})\) and have zero
   columns. None is silently discarded.
8. Genuine previous reserved vertices belong to the next protected prefix.
   Their columns remain as they were; the old prefix is not reset to zero.
9. Each new \(Q_i\) is anticomplete to earlier original vertices, in *both*
   directed orientations.
10. Distinct \(Q_i\) blocks are consequently mutually anticomplete, although
    each internal \(Q_i\) is a clique.
11. The same future sort domain \(d\) is used throughout this theorem.
    Splits, deletions or controlled coding require explicit sort transports.
12. The generation \(k_i\) is stage-local. Numerically equal \(k_i\) does not
    identify the tagged top futures between different stages.
13. The proof does not preserve previously chosen *top future witnesses*
    (whose physical original addresses may lie beyond \(b_i\)). This is the
    exact obstruction to using the result as an infinite diary realization.
14. Even preserving full ordinary columns does not preserve auxiliary
    \(Kpt/L^+/E\), parameter closure, selected levels or corrected B3.
15. The proof does not assert no (I1), no (I2), or no (I3) between block cuts.
16. A final age equality alone is not evidence that the intended cover order
    is the **only** interesting-level history of an actual successor run.
17. The new induction uses no compactness or infinitary fusion. Every
    existence choice is finite, made by an already kernel-checked physical
    one-cover stage.

## Boundary and next obligation

The formerly isolated two-cover composition generalizes formally to any
**supplied finite cover chain**, without fresh combinatorial assumptions.
This should not be promoted to the resolved-copy or BRD theorem.

The next genuinely new lemma must retain finite *selected tagged witnesses*
through subsequent original cutoffs, rather than only preserve earlier
original columns. It must prove that the full canonical age stays unchanged
when the cutoff is enlarged to include those witnesses with their required
positive bits. The old critical-count/anchored-neutrality conditions are
sufficient, not yet established for a prescribed diary. After that, one must
synchronize the complete parameter-closed Kpt history and a common labelled
inverse-source record.
