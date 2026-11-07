# Independent review of global energy to local Wronskian

Accepted at the stated scope. Three copied source modules and their exhaustive recursive audit were freshly rebuilt with strict kernel checking. All 14 declarations passed, with only propext, Classical.choice and Quot.sound. All copied Lean files match the frozen author sources byte-for-byte. No author file was changed.

## Mathematical checks

- The real determinant of complex scalar multiplication is exactly the square of the complex norm. Restricting the actual complex derivative to real scalars supplies the derivative in Mathlib's finite-dimensional real Jacobian theorem. The coefficient is exactly f(F(z))*F'(z), rather than f(F(z)) alone.
- The image integral and integrability equivalence use an injective map on the open source. This is the correct hypothesis that excludes covering multiplicities. No nonzero-derivative or inverse differentiability premise is smuggled into the interface. The actual Jacobian theorem accommodates the derivative as stated.
- The energy density is the square of the ordinary complex norm with respect to ordinary complex Lebesgue area. The norm-squared real determinant introduces no factor two or pi. The conversion to a global differential pairing is deliberately not claimed here.
- Restriction of nonnegative global energy to a chart image has the correct inequality direction. Integrability is genuinely transported, rather than inferred from the totalized real integral's numerical bound.
- Evaluating the actual pushforward-density measure equality on the whole target gives local lintegral equal to mu(U). The argument uses measurable pushforward, the restricted measure, and actual withDensity. Global mass at most one then proves finite integrability and the real integral bound using nonnegativity; it does not treat a nonintegrable real integral as evidence of finite energy.
- The final theorem derives the coefficient measurability from holomorphicity on an open chart domain. It composes both the norm-one local energy and actual factorial-normalized derivatives into the already independently reviewed Wronskian packet. One common injective chart is used for all differential coefficients.

## Precise remaining geometry

The final theorem receives actual global nonnegative measures of mass at most one and exact chart-density identities. Constructing those measures on the actual compact curve, identifying their mass with the global (i/2) differential pairing, and constructing the holomorphic chart remain geometric inputs. The density identity is an explicit normalization/coordinate interpretation, not a proved Riemann-surface theorem in this packet. It is exactly where an incorrectly normalized geometric measure or chart multiplicity would have to be ruled out by the geometric application.

No actual global curve is constructed here, no nonvanishing Wronskian point is asserted, and FiveContact49Height is not concluded. The packet genuinely removes the real/complex Jacobian, local energy restriction, integrability transport, and local analytic Wronskian composition from those remaining inputs.

## Evidence

`run.sh` replays the copied packet against the frozen Wronskian dependencies. The original Mathlib Jacobian theorem and its integrability companion were reread at their exact applications. Receipt and hashes bind copies, logs, audit, producer note and author/dependency receipts.
