# Exact ordinary seventh-moment receiver

Read the [exact proof and controls](source/original-detectors-ordinary-seventh-moment-r1/EXACT-ORDINARY-SEVENTH-MOMENT.md)
and the [signed independent review](independent-review/INDEPENDENT-ORDINARY-SEVENTH-MOMENT-REVIEW.md).
Run `sh verify.sh` for the exact byte replay.

For an odd-degree ordinary reference, just three coefficients of an
authenticated reciprocal Weber genus-slice jet suffice: the exact bit
is e7 + e2 e5. The executable consumes seven-term jets without storing
the full polynomial. It does not authenticate externally supplied jets.

The independent finite constructor verifies the complete actual CM roster
at D = -119, where the bit is 1, and both complete genuine genus slices at
D = -22967, where both bits are 0. Including all three cube branches
incorrectly gives zero even on the positive control. Neither discriminant
is a literal six-prime detector reference. The ambient finite-field
constructor does not scale to the required discriminants; the exact
production Weber jet, its bit, and both ranks are still missing.

Scope is the seventh-moment receiver and controls only. The later quotient
traversal and ramified level-48 divisibility are not included.
