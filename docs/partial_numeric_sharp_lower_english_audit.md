# Track A — unconditional sharp LOWER capacity at a physical partial numerical-H cut

16 November 2026. English proof and independent adversarial audit BEFORE Lean.

## Crucial scope correction

The exact target is

    cap_L(N_U) =
      max(cap_E(P_U),
          if eligible(U) then min(g,1+cap_E(S_U)) else 0).

One must **NOT** omit the eligibility condition in an equality.
If b is NOT adjacent to every selected future type in U, NONE
of its partial-generation copies belongs to N_U. Yet
min(g,1+cap_E(S_U)) can strictly exceed cap_E(P_U).

Small K4-free counterexample: original vertices 0,1,2,
edges {0,1} and {0,2}, but NOT {1,2}. Take k=2,
current original b=1, cut g=2, selected later top original
j=2, and U the unique future sort.
P_U={0}, S_U={0}; cap_E(P_U)=cap_E(S_U)=1.
Current b is ineligible: E(1,2)=false. Therefore the true
old U-common-neighbour pool contains only complete real
copies of original 0, with capacity 1. The unconditional
naive RHS would be max(1,min(2,2))=2, which is FALSE.
The *conditional* expression above has value 1.

## Genuine lower bound in the eligible case

Fix an arbitrary symmetric original E, numerical-H height k,
current original b and cut g<=k, finite carrier M, given
later top-original family j(t)>b, and a nonempty admissible
future support U. Define

  P_U={i<b : E(i,j(t))=true for every t∈U},
  S_U={i∈P_U : E(i,b)=true},
  eligible(U) iff E(b,j(t))=true for every t∈U,
  N_U={z<hPosition(k,b,g): each actual numerical-H L crossing
       from z to the later top originals is positive on U}.

Suppose eligible(U). We prove

  max(cap_E(P_U),min(g,1+cap_E(S_U))) <= cap_L(N_U).

The first term follows immediately from the established physical
capacity sandwich: the full real-generation copies of every
earlier U-neighbour remain in the old prefix and induce exactly
the original graph capacity.

For the second term, if g=0, it is min(0,anything)=0 and
there is nothing to prove.

Otherwise let c=cap_E(S_U) and
  a=min(c,g-1).
Then a<=c and a<g, while natural arithmetic gives
  a+1 = min(g,1+c).
This also holds when a=0 or c=0.

The independent sorted-clique extraction lemma #250 produces
an actual increasing list of original names q(0),...,q(a)=b,
with all previous q(i) in S_U⊆P_U, all forward original
E atoms between q(i),q(j) positive, and strict original index
order. It uses a *capacity-attaining actual clique* in S_U;
no guessed or invented original vertex is introduced.

The conditional physical staircase lemma #241 then gives a true
numeric L-clique of size a+1 in the **entire** actual
U-common-neighbourhood N_U, by embedding the already verified
nonconsecutive original reserved-prefix staircase. Consequently
  min(g,1+cap_E(S_U))=a+1 <= cap_L(N_U).

Taking the maximum with the first bound yields the desired
eligible-case lower inequality.

If eligible(U) is false, the previously verified conditional
ineligible exact capacity theorem proves cap_L(N_U)=cap_E(P_U).
Therefore the full conditional lower inequality also holds
when b is ineligible.

## Equality once the upper gate passes

The sharp upper inequality from PR #238 (stated for all U, with
an unconditional extra max-term) is valid but weaker than equality.
In the eligible case it exactly matches the lower bound above,
so equality follows. In the ineligible case use the stronger
ineligible exact-capacity theorem directly, not the unconditional
upper bound. This yields the correct conditional formula
displayed at the start, for every g<=k and every nonempty U.

At g=0 the formula specializes to cap_E(P_U) independently
of eligibility, as required by the previously checked completed
old-block age theorem.

## Adversarial checks

1. Eligibility cannot be omitted from an EXACT formula; the
   explicit 3-vertex K4-free counterexample above refutes it.
2. The upper inequality without eligibility remains true
   (merely potentially nonsharp).
3. The current b is not yet in the old prefix at g=0.
4. The current b TOP copy is excluded at every g<=k.
5. k=0 entails g=0; the lower is the full earlier pool only.
6. The source old common neighbourhood includes every numbered
   odd dummy, which is eliminated by NONEMPTY support U.
7. Original E symmetry is used for true numerical-H
   two-orientation columns and the reserved staircase theorem;
   sorted original-clique extraction itself needs only directed E.
8. Capacity means maximum E clique SIZE in S_U, not the
   cardinality of S_U.
9. The capacity-attaining original clique can have holes/gaps.
   Its natural-number order is used in q; no re-enumerated
   ambient E graph is substituted.
10. q is a total Nat→Nat map with index-limited properties.
11. The special a=0 case provides exactly the current b
    generation-0 singleton whenever g>0 and eligible.
12. The original staircase R is a subset of the entire physical
    U-common-neighbourhood, not equal to it.
13. The lower staircase witness needs 0<=a<g<=k.
14. The equality is one finite ordinary binary-L age result.
    It does not construct the given later original top names
    with prescribed recursive schedule.
15. The proof does not identify selected graph-age changes
    with full parameter-closed (I1)/(I2)/(I3)/(B3) events.
16. Nor does it produce cross-occurrence labelled inverse
    source orbits or full big Ramsey degrees.
17. The numerical H Boolean binary relation is total on Nat;
    interpreting all coordinates as a literal finite carrier
    still needs the separate old/top cutoff inequalities.

## Lean acceptance

Implement independent Kk/PartialNumericSharpLower.lean importing:
- Kk.OrderedCliquePrefixWitness (independent #250);
- Kk.PartialNumericStaircaseLower (stacked #241);
- Kk.PartialNumericCapacityBounds (stacked #232).

Prove the eligible-case max lower inequality and then a
separate exact conditional full sharp-capacity theorem by
combining with Kk.PartialNumericSharpUpper (#238) and the
ineligible capacity-equality theorem.

Use exact-head explicit module build, strict fully qualified
named standard-only axioms and full repository Lake build;
run the independent 26,880-case numerical model test plus
an explicit ineligible three-original counter-regression.
DO NOT mark either global resolved-copy or full Kpt source
green from this finite ordinary-L theorem. Retain DRAFT
until every source dependency is kernel-certified.
