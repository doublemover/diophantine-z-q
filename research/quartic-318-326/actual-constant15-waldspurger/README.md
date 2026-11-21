# A fixed-level rank-zero test for the same literal receiver

The exact marked receiver on a twist of the conductor-15
curve now has a published Waldspurger reduction to one
signed integer coefficient at level 180. The formula genuinely
covers the original scalar's ramification at 5. The exact
replay verifies both integer lattice descriptions, all signed
published control values, and the auxiliary twist's positive
central value independently.

A certified nonzero coefficient at the literal twist would
exclude this constant-conductor receiver by analytic rank zero.
No coefficient at that literal twist is computed. A zero
coefficient would not produce a point, and this test does not
exclude other constructions of the original PointPair.

- [Proof, explicit weights and finite controls](rc-native-helper-20261120/ct-original-constant15-waldspurger-r1/FIXED-LEVEL-WALDSPURGER-FOR-THE-LITERAL-CONSTANT15-RECEIVER.md)
- [Signed independent review](independent-review-nov20/rc-constant15-waldspurger-cold-r1/INDEPENDENT-CONSTANT15-WALDSPURGER-REVIEW.md)

    sha256sum -c SHA256SUMS
    (cd rc-native-helper-20261120/ct-original-constant15-waldspurger-r1 && \
      python3 -B replay_weighted_ternary.py | cmp - EXACT-WALDSPURGER-CONTROLS.json)
