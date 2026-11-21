# A sparse quartic for the original scalar's marked genus-one cover

The [exact reduction and back-map](ct-original-scalar-mestre-sparse-quartic-r1/LITERAL-GAMMA-SPARSE-QUARTIC-AND-BOUNDED-CRT.md) replace the same marked genus-one cover by one binary quartic with fixed coefficients and the unchanged scalar squareclass. Any rational point of that quartic yields a PointPair at this scalar with both ordinates nonzero.

The [independently reviewed reconstruction](rc-literal-gamma-sparse-quartic-cold-r1/INDEPENDENT-LITERAL-GAMMA-SPARSE-QUARTIC-REVIEW.md) excludes every primitive balanced chart of normalized height at most 4218366392 on this cover: four already known odd-depth primes give the complete CRT roster; thirteen literal source residue tests reject all 6110 candidates. It does not exclude points at greater height, settle unseen support, or say that no other PointPair exists. It does not compute a rank or claim a Lean proof.

Replay from this folder: python3 -B ct-original-scalar-mestre-sparse-quartic-r1/replay_sparse_quartic.py | cmp - ct-original-scalar-mestre-sparse-quartic-r1/EXACT-SPARSE-CRT-CONTROLS.json
