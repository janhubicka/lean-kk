# Finite selections for one-gap compression

## Proof before implementation

The compression lemma is stated for a strictly increasing map on all
natural numbers, although its finite code reads only the first n values.
For a strictly increasing finite selection f:Fin n -> Nat, let M be the
maximum of its finite range, with M=0 if n=0. Define its explicit extension
F(k)=f(k) for k<n, and F(k)=M+1+(k-n) for k>=n.

For two positions inside the finite part, strict increase is the hypothesis
on f. For two positions in the tail it follows from the displayed formula.
Across the boundary the old value is at most M and the new value is at
least M+1. Thus F is strictly increasing and extends f, including the
empty selection case. No infinite extension hypothesis or choice of
extension is needed.

Define the finite retained code using this extension and the existing
one-gap code constructor. If two selected finite ordinary tables agree,
the full retained codes agree by the compression theorem, since the
extensions agree with their finite selections at every inspected index.
An extension-independence theorem shows that any other strictly increasing
extension gives the identical retained code.

## Audit and boundary

The proof is valid for n=0: the finite code consists only of the anchor,
and the linear tail is irrelevant. The ordinary edge tables need not be
symmetric or loop-free. Equality includes the complete auxiliary table.
The finite table hypothesis includes i=j, so it also preserves the
normalized diagonal channel, which records the actual self-edge bit.

This removes an unnecessary infinite premise from finite compression.
It does not establish that a macrodiary determines its selected ordinary
table, or that a concrete envelope inverse source has the prescribed
retained coordinates. Those are separate application theorems.

The parent was sent the explicit maximum-and-tail construction before
the Lean implementation. It uses only finite order and the actual
maximum of the finite selected range.

## Local validation

The isolated normal Lake target `Kk.OneGapFiniteSelection` passed with
Lean 4.35.0-rc3, including all eight theorem declarations and the real
compiled compression dependency. The project-wide build and consolidated
transitive-axiom gate are recorded separately by the integration audit.
