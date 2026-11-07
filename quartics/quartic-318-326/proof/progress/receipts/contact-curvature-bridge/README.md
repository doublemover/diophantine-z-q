# Actual contact-distance curvature

Strict kernel PASS: six modules; all 101 declarations recursively audited with only propext, Classical.choice and Quot.sound. Every module was freshly rebuilt with debug.skipKernelTC=false.

The metric is the literal coefficient rho(z)=(1+sum_i |z-a_i|)/product_i |z-a_i| for the scaled source contacts a=[0,32,76832,-343]. Its local real chart at z is translation by x+iy. Curvature uses the ordinary conformal convention K=−Delta(log rho)/(2rho).

The packet proves, rather than assumes:
- actual first and second real derivatives of Euclidean distance, Delta distance=1/distance and Delta log distance=0 away from a contact;
- local C2 regularity and the actual finite-sum/log differentiation identities;
- the exact negative-curvature expression product(r_i)/(2U^3)*(U sum_i 1/r_i−|grad U|^2);
- the actual gradient bound |grad U|^2<=16, by writing each gradient as a unit complex number;
- the resulting lower bound for negative curvature by the triple-distance quotient;
- exact binding to the actual complex source distances and the frozen contact quotient estimate, giving K<=−1/12540153541944538512 at every off-contact point.

`LiteralCurvature318.literal_curvature_bound`, `literal_axisC2`, and `literal_positive` consume exactly `MetricPullback318.sourceCoefficient LiteralMetricExtension318.contacts` from the independently developed branch/infinity extension packet. No curvature identity, gradient bound, or coefficient-normalization hypothesis is retained. The constants and contacts are not rescaled in the final wrapper.

## Scope

The bound here is at off-contact points of the quotient coordinate. The branch/infinity packet proves actual smooth positive extensions and punctured pullback equalities. Transport of computed curvature through those ramified charts, continuity at their origins, and their realization as charts of the actual compact geometric curve are separate downstream obligations. This packet does not assert an abstract scalar curvature in place of the computed one, construct the global curve or its hyperbolic metric, or prove FiveContact49Height.

## Replay

Run `bash contact-curvature-bridge/build-all.sh` in the shared assistant workspace with the hash-bound dependency packets available. The module order, per-module successful logs, full replay and exhaustive recursive audit are included. No repository or Git changes were made.
