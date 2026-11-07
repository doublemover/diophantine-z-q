# Actual Weierstrass invariant differential overlap

This packet proves the actual relative differential identity on the actual Weierstrass Jacobian charts, over every commutative base ring. All maps and differentials are genuine localization algebra maps and Mathlib universal Kähler differentials.

The finite chart is y²=x³+Ax+B, localized at 2y. The infinity chart is z−u³−Auz²−Bz³=0, localized at J=1−2Auz−3Bz². Their comparison uses x=u/z and y=1/z, then the actual common localization inverting J·(2/z). Differentiating the actual relation gives J dz=(3u²+Az²)du. The relation also gives zJ−u(3u²+Az²)=−2z. Genuine Leibniz differentiation of z·z⁻¹=1 yields J d(u/z)=−(2/z)du. Thus dx/(2y)=−du/J, with the required minus sign.

`InvariantChartForms318.invariant_overlap` identifies pullbacks of the actual source-chart forms under the actual chart-to-common algebra homomorphisms, rather than only symbolic expressions in a field. `InvariantFormFrames318` proves both forms generate their entire actual relative differential modules, using the previously constructed Jacobian Kähler frames. No rank, basis, denominator-unit, or derivative-identity premise is supplied.

The generic arbitrary-algebra-map differential pullback is constructed from the actual universal differential map with the algebra structure induced by the given homomorphism. Its derivative and semilinear scalar formulas are proved.

## Exact boundary

This is the relative elliptic-family differential line, not the canonical/bicanonical line of the compact modular or PEL base. The packet does not claim identification with that base line, global Hodge pushforward, or global overlap gluing. The second finite Jacobian chart at −3x²−A and its differential compatibility are not included. The earlier actual tilde-sheaf packet supplies affine sheaves, but actual sheaf restriction/base-change comparison on these overlaps is still a separate step. Trivial localizations are allowed over arbitrary base rings, so generation does not assert nontriviality of every chart.

## Replay

Run `bash verify.sh` from this directory. Each source is strictly rebuilt with `debug.skipKernelTC=false`; the final audit recursively rejects every nonstandard axiom, including sorryAx. External packet receipts and direct source files are bound in receipt.json. No repository or Git changes are made.
