# A single physical numerical-H canonical age change need not be a cover

17 November 2026. English proof, hostile audit and independent literal
numerical-H regression. This is a counterexample to a *cover shortcut*,
not to the verified age theorems. Companion to
\`docs/k4_raw_event_canonical_redundancy_english_audit.md\`.

## A five-vertex \(K_4\)-free source

Let \(E\) be the **tree** on original names \(0,1,2,3,4\), with
exactly the four undirected edges

\[
  02,\qquad 12,\qquad 13,\qquad 14.
\]

It is triangle-free, hence \(K_4\)-free. Fix forbidden-clique
parameter \(\ell=4\), numerical-H height \(k=4\), current original
\(b=1\), and three **distinct later top-original names**

\[
  j(0)=2,\qquad j(1)=3,\qquad j(2)=4.
\]

Compare the literal old numerical-H prefixes before generation \(0\)
and generation \(1\) of original \(1\), i.e., \(g=0\) and \(g=1\).
Since \(\iota_4(i,q)=2(5i+q)\), they are the numbered intervals
\([0,10)\) and \([0,12)\). Both contain *all* intervening odd
dummy coordinates; the only new real copy is \(\iota_4(1,0)=10\).

## Exact physical raw and canonical ages

All nonempty admissible supports of the three future sorts occur,
since \(\ell-1=3\). Before the current original appears, only
original \(0\) is old. It is adjacent to future original \(2\),
but not to \(3\) or \(4\). The original-index common-neighbour
clique capacities are therefore \(1\) at \(U=\{0\}\) and \(0\)
at all six other nonempty supports.

The newly admitted current-original copy at generation \(0\) is
adjacent in the **actual** numerical-H binary \(L\) to all three
later top-generation copies because the original edges \(12\),
\(13\) and \(14\) are positive. It is not adjacent to any
earlier original copy in the old prefix: the strict
earlier-to-nontop generation gate would require \(q<0\).
Thus the capacity at support \(\{0\}\) remains \(1\), and
the capacities at the six other supports rise from \(0\) to \(1\).

Using the support order

\[
  \bigl(\{0\},\{1\},\{2\},\{0,1\},\{0,2\},
  \{1,2\},\{0,1,2\}\bigr),
\]

the **raw AND canonical** integer graph ages at the two cuts are

\[
  F_{\mathrm{old}}=(2,3,3,3,3,3,3),\qquad
  F_{\mathrm{new}}=(2,2,2,2,2,2,2).
\]

The independent verifier checks every physical old coordinate,
every numerical-H generation gate, all seven support common pools,
all normalized clique vectors of total weight at most \(3\),
and both canonical suprema.

## A strict genuine intermediate integer age

Define

\[
  H=(2,2,2,2,2,2,3).
\]

It lies strictly between the two endpoint ages in the pointwise
order: \(F_{\mathrm{new}}<H<F_{\mathrm{old}}\).

It is also a **genuine** normalized integer-witness graph age.
The following vectors attain every support value of \(H\) while
respecting **all** support inequalities simultaneously:

| Support | \(H(U)\) | Feasible attaining weight vector \(w\) |
|---|---:|---|
| \(\{0\}\) | 2 | \((2,0,0)\) |
| \(\{1\}\) | 2 | \((0,2,0)\) |
| \(\{2\}\) | 2 | \((0,0,2)\) |
| \(\{0,1\}\) | 2 | \((1,1,0)\) |
| \(\{0,2\}\) | 2 | \((1,0,1)\) |
| \(\{1,2\}\) | 2 | \((0,1,1)\) |
| \(\{0,1,2\}\) | 3 | \((1,1,1)\) |

Each weight vector has total multiplicity at most \(3=\ell-1\).
All singleton bounds are \(2\), all pair bounds are \(2\),
and the three-sort bound is \(3\); the displayed witnesses
obey these jointly. Equivalently,
\(\operatorname{integerGraphAgeCanonical}(H)=H\).

**Conclusion.** A physical partial-cut change of the actual
ordinary-\(L\) canonical numerical-H age need NOT be a cover
in the poset of genuine integer graph ages. The five-vertex
example has a strict intermediate genuine age \(H\).

## Exact scope of the obstruction

This is a genuine finite \(K_4\)-free original source,
\(k=\ell=4\), with **three distinct** later future original
names. It does not rely on loops, repeated selected names,
omitted odd dummies, an abstract selected-shadow pool or a
counterfactual generation gate.

The example is not claimed to occur with exactly these ordinal
labels in a preselected left-dense Henson enumeration or in
the specially prescribed resolved-copy stage schedule. It
refutes the **unconditional deduction** that every physical
numerical-H canonical-age change is one graph-age cover.

A global construction claiming one selected-front cover per
intended event must separately enforce a suitable original
column schedule or split a simultaneous family of constraints
into verified cover steps. In addition, a full parameter-closed
Kpt \(E\)/(I1)--(I3)/(B3) event may have unrelated auxiliary
causes; this finite example does not settle those.

The executable finite referee
\`scripts/check_k4_physical_canonical_noncover.py\`
tests the actual two-direction binary generator, physical old
pools, \(K_4\)-freeness, endpoint raw/canonical ages, strict
intermediate age and seven globally feasible attaining witnesses.
It is an **independent finite check**, not a new Lean formal proof.
