# Complete retained-pool prescription (26 November 2026)

## Scope

This step constructs the actual one-level prescription from a finite ambient
retained pool and verifies every crossing of the parameter-closed envelope.
It does not construct the global countable resolution or identify inverse
source codes across different occurrences of a diary.

Fix a forbidden-free enumerated partial structure `A`, a cut `c`, and a set
`V` of actual vertices of `A`. The ambient prefix pool consists of all Kpt
prefixes of originals named by `V`. At the cut, retain as eligible exactly
those names `v` for which `c+1 <= freeLevel(v)`. The index universe is
`Fin A.size`, so no arbitrary enumeration of the pool is needed.

## English proof

1. Use the existing eligible ambient-pool constructor with eligibility
   `v in V and c+1 <= freeLevel(v)`. It chooses one representative for each
   complete old partial type. Both B1 and B2 are established by that
   constructor, including every ordinary and auxiliary atom. Every output
   is the complete next type of the same eligible representative.
2. Assume complete next-type fibre agreement: two eligible retained names
   with equal complete types at `c` have equal complete types at `c+1`.
   Then the chosen output equals the actual next type of *every* eligible
   representative of that old type. The assumption can separately be
   established from ordinary no-fork by the theorem in
   `OneGapFullClosure`; no no-I2 or crossing-cover conclusion is assumed.
3. Let `z` be any node of the actual closure with `c < level(z)`. The proved
   ambient-pool containment gives a name `v in V` with
   `z <= kptOriginal(v)`. Its free level is at least `level(z)`, hence it
   is eligible. The exact ambient-ancestor theorem identifies both
   consecutive ancestors of `z` with the complete types of that same
   name. Step 2 identifies the chosen output, proving that the
   prescription covers every closure crossing.
4. A target is admissible because it is a prefix, through its genuine free
   cut, of an original in the forbidden-free ambient structure. The
   arbitrary value of the total target function outside its source is
   never used.
5. Suppose every eligible retained name positive to `c` is a selected
   terminal. Extracting the representative of an actual source verifies
   the exact representation premise of `oneGap_correctedB3_of_equal_selected_age`.
   Thus equality of the full canonical selected age before and after `c`
   proves corrected B3 for this *constructed* prescription. This first
   version has the explicit hypothesis `0 < d`; the extension below
   removes it. Repeated upper labels remain allowed.
6. At a positive cut, the already verified prescribed boring-extension
   theorem supplies a one-gap Kpt monoid map agreeing with every closure
   crossing. For a planned closure, its ambient-pool containment is
   derived from the exact closure normal form and the retained-parameter
   condition, rather than assumed as an abstract source property.

## Adversarial checks

- All retained auxiliary originals and the cap may occur in `V`; the source
  is not restricted to selected graph vertices.
- Endpoints below the next cut are excluded from eligibility, never
  promoted to non-existent Kpt types.
- Equal old types alone are insufficient. The complete next-type fibre
  hypothesis is necessary and explicit.
- Choice only resolves duplicate old records; fibre agreement proves that
  this choice cannot omit a required next record.
- The B3 conclusion does not follow from selected age equality alone. The
  positive-source classification for this full retained pool is also
  required, so the old numerical-H counterexamples are unaffected.
- This theorem gives a possibly larger prescribed source than the exact
  crossing source. That is intentional and sound: corrected B3 is proved
  for the larger source, and every required crossing is covered. No
  assertion of equality with the minimal algorithm's source is made.
- No countable graph, finite macrodiary, common labelled inverse source,
  or big Ramsey bound is assumed under a different name or concluded.

The proof plan was sent to the integrating agent and adversarially reviewed
before implementation. Local kernel and axiom-audit results are recorded by
the integrating validation report after compilation.

## Empty selected front: additional proof before implementation

The nonempty-front hypothesis can be removed. Suppose first that every
represented next type has a false ordinary bit from the cut. A hypothetical
new forbidden clique must contain the cut, since deletion avoids it, and
must contain an upper vertex: a copy wholly at or below the cut transfers
through the complete common initial socle to the forbidden-free ambient
structure. Its cut-to-upper edge is true, contradicting the false bit
transferred by the complete represented upper type. The existing complete
type asymmetry argument excludes both forbidden asymmetric pairs. A loop
at the cut contradicts ambient diagonal avoidance; any other loop survives
deletion and is therefore impossible.

This proves corrected B3 with no selected front and no selected-age
hypothesis whenever all represented next types are nonpositive at the cut.
For a general front of size `d`, split into `0 < d` (the earlier proof) and
`d = 0`. In the latter case the positive-source classification would assign
a true represented bit a label in `Fin 0`, an impossibility. Thus all such
bits are false and the preceding argument applies. The final `*_all`
interfaces permit every `d`, including zero. Their old nonempty-front
variants are kept as named special cases.

This extension handles empty selected labels even when the full retained
pool and its source are nonempty, for example when a cap still crosses.
It does not assume that an empty selected front makes the full Kpt source
empty, or that arbitrary upper-upper edges of an age witness are neutral.

## Local module validation

The normal target `lake build Kk.OneGapPrescribedPool` completed
successfully with Lean 4.35.0-rc3. The log reports a successful dependency
build of 9,407 jobs, including all eleven theorem declarations in this
module. Its only module-specific warning concerns the existing legacy
import style for `Mathlib.Tactic`; there are no proof errors or admitted
declarations. The exact output is recorded in
`proof-audit/serial-build/Kk.OneGapPrescribedPool.log`.

The eleven focused transitive-axiom reports are listed in
`scripts/check_axioms_one_gap_prescribed_pool.lean`. Their executed gate,
the combined integration gate, and any whole-project build are recorded
separately by the integrating validation report. A successful build of
this module does not establish the remaining countable resolution or
the final big Ramsey characterization.
