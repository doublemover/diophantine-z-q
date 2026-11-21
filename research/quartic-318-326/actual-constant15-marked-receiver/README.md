# A constant-conductor marked receiver and a uniform index constraint

A single explicit genus-one quartic reduces the two same-pole marked
points to one exact rational x-squareclass on a twist of a
conductor-15 elliptic curve. Its rational-point back-map gives both
literal cubic equations, including the same nonzero scale, and is
everywhere locally soluble at the original scalar with input zero.
It need not preserve the old selected twist congruence.

An exact cyclic calculation at 29 rules out the simpler fixed
multiplier for *every* defined alternate index of that same
zero-input scalar source. The full receiver instead allows the
required positive multiplier depth; the calculation does not
obstruct it. No rational point on the actual receiver, rank
calculation, or completed original PointPair is claimed.

- [Exact proof, literal source gate, and arithmetic control](rc-native-helper-20261120/ct-original-constant15-marked-receiver-r1/CONSTANT-15-MARK-AND-UNIFORM-29-SOURCE-GATE.md)
- [Signed independent review](independent-review-nov20/rc-constant15-marked-receiver-cold-r1/INDEPENDENT-CONSTANT15-MARKED-RECEIVER-REVIEW.md)

    sha256sum -c SHA256SUMS
    (cd rc-native-helper-20261120/ct-original-constant15-marked-receiver-r1 && \
      python3 -B replay_constant15.py | cmp - EXACT-CONSTANT15-CONTROLS.json)
