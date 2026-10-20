# lean-kk

Lean 4 development for counting big Ramsey degrees of the universal $K_k$-free graphs, using the independently verified type-respecting Ramsey theorem from [`lean-successors`](https://github.com/janhubicka/lean-successors) as a library.

The first formal target is the finite-family type-respecting Ramsey step in the successor-tree upper bound. Subsequent targets are the finite labelled diary carrier, compatibility with the induced action on the auxiliary graph, labelled occurrence factorisation, and the published diary unavoidability lower bound.

The normalised binary-language library model is used directly. No replacement Ramsey axiom is introduced. Proof obligations and the correspondence to the paper are tracked in `docs/validation.md`.

Run `lake update`, `lake exe cache get`, `lake build`, then `lake env lean scripts/check_axioms.lean`. The toolchain and dependency revision are pinned; see `lakefile.toml`.
