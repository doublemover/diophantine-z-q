# Exact denominator obstructions for the original slot190 square contact

These independently reviewed paper results use the literal unscaled slot190, one unchanged original guarded h, and primitive square contact t=(r/d)^2>2. They are necessary, not sufficient, and neither constructs a PointPair nor proves a Lean theorem.

- [Universal 2399 obstruction](linked-detector-square-den2399-r1/ACTUAL-SQUARE-CONTACT-REQUIRES-2399-DENOMINATOR.md): every such square contact admitting the literal PointPair requires 2399 dividing d. It uses no Pythagorean condition. With d a unit, negative odd contact fails by the parity fold; positive odd contact fails both exact elliptic orientations at the actual split prime 2399.
- [Pythagorean 407 obstruction](linked-detector-pythagorean-contact-obstruction-r1/ACTUAL-PYTHAGOREAN-SQUARE-CONTACT-OBSTRUCTIONS.md): if additionally r²+d² is a square, then both 11 and 37 divide d. That parametrization clears the first two moving factors' inert support, but the other two polynomials do not give a generic joint norm identity. An exact example with 407 saturated still has an inert obstruction at 35533.
- [Combined independent review](joined-square-denominator-cold-r1/INDEPENDENT-REVIEW.md) checks both statements, including literal midpoint and parity scopes. The exact earlier source-paper guards and split/CRT criterion are included under prior-proofs. The additional exact sixteen-leaf threshold is a local valuation test only; it does not construct a compatible global h,t.

Run sh replay.sh with Python 3 and sha256sum. Both bounded replays are offline, require only their bundled inputs, and check the exact printed data. The separate all-split example and its orientation failure are not included.
