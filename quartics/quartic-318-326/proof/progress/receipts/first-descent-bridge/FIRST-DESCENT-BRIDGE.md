# Exact first-descent eight-squareclass bridge

`GlobalFirstDescent318.first_descent_classes` proves the exact proposition `GlobalNormCoset318.FirstDescentClasses` for the actual K = Q(sqrt(2)) and E: y² = x³ - (3 - sqrt(2))²x.

For every actual nonsingular affine point with nonzero x, it constructs a nonzero r and one of the eight stored representatives such that x is that representative times r². The representatives are 1, -1, 1+sqrt(2), -(1+sqrt(2)), 3-sqrt(2), -(3-sqrt(2)), 1+2sqrt(2), and -(1+2sqrt(2)).

## Proof

- `UnitSquareclasses318` proves all four actual unit squareclasses in Z[sqrt(2)]. Norm-one units use the already-proved Pell result and the sign of their integer real coordinate. Norm-minus-one units are multiplied by the explicit inverse of 1+sqrt(2), reducing to norm one. No unit-group assertion is assumed.
- `FirstPrimeParity318` proves even valuation of x at every prime except delta = 3-sqrt(2), using the exact curve equation. Removing either no factor or one delta makes all prime valuations even. These are the actual prime-multiplicity valuations constructed from the proved Euclidean order, so no prime-place coverage theorem is assumed.
- `FirstFieldClasses318` applies the checked normalized-factorization argument to a reduced numerator and denominator. It obtains a square times an actual unit, then one of the four unit squareclasses.
- `GlobalFirstDescent318` identifies the resulting eight classes with the project's exact stored representatives, including delta*(1+sqrt(2)) = 1+2sqrt(2).

## Verification and scope

`run.sh` freshly rebuilds all four modules with kernel typechecking enabled and runs a recursive declaration/axiom audit. `receipt.json` and `SHA256SUMS` bind source and log hashes. The eleven-module dependency packet is separately rebuilt/audited in `../dual-square-bridge`.

This closes first-descent squareclass coverage. The global generator theorem still needs its other independently tracked height and finite-enumeration inputs. No sourceArithmetic or full-generator conclusion is asserted here. No repository files were changed and no PR was opened.
