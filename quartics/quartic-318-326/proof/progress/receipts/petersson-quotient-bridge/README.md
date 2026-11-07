# Actual quadratic-differential action and quotient Petersson norm

The acting group is Mathlib's actual GL2+(R), not an abstract group supplied with a cocycle. `DerivativeCocycle318.derivative` is bound exactly to the complex derivative of its genuine upper-half-plane action. Its nonvanishing, identity value and chain-rule cocycle are proved using the actual matrix determinant and denominator identities.

`QuadraticFiber318.Fiber` consists of an actual upper-half-plane point and a complex quadratic-differential coefficient. The induced action is
  g*(z,q)=(g*z,q/(g'(z))²).
This inverse derivative-squared direction is essential. Coordinate pullback multiplies the coefficient by derivative squared; transport to the image point divides by it. The group-action laws and invariance of the actual norm|q|*(2Im z)² are proved.

For every actual subgroup H of GL2+(R), `PeterssonQuotient318` constructs its genuine orbit quotient of the base and total fibers, their projection, a zero section and a descended nonnegative norm. The norm vanishes exactly on the actual zero section. These statements include groups with stabilizers and do not assume freeness or compactness.

`ContinuousDescent318` equips the fiber space with its actual product-coordinate topology and the orbit space with the quotient topology. The norm on the resulting quotient is proved continuous. No norm-descent or continuity premise is supplied.

## Scope

This constructs an orbit space with projection, zero section and continuous invariant norm. It does not assert that a general subgroup quotient is a locally trivial line bundle, a manifold, a compact arithmetic curve or a Hausdorff space. Identifying the source arithmetic subgroup/stack, its atlas and actual global bicanonical/Petersson line remains explicit geometry. The existence of global source sections or the full FiveContact49Height theorem is not claimed.

All accepted modules are freshly rebuilt with debug.skipKernelTC=false and every declaration recursively checked against only propext, Classical.choice and Quot.sound. See receipt.json for counts, dependency and source hashes. Run `bash petersson-quotient-bridge/build-all.sh`. No repository or Git changes were made.
