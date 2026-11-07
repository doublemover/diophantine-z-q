# Actual conformal curvature and compact metric comparison

Strict kernel PASS: two modules, eight public theorems and 11 recursively audited declarations. Only standard axiom roots occur.

`ConformalCurvature318.curvature rho` is the actual conformal curvature at the chart origin, defined as minus the ordinary two-real-coordinate Laplacian of log rho divided by 2*rho(0,0). It is not an independent opaque scalar.

The exact second derivative of log(f/(C*g)) is derived from local C² regularity and positivity at the center. Continuity supplies the neighborhoods where f,g remain positive; real-log multiplication/division is rewritten only there. Eventual equality is differentiated twice. Linearity of the second derivative is itself proved from actual derivative rules and local C² regularity.

Applying these facts to both coordinate axes proves the Laplacian difference identity. The conformal curvature formula and its hyperbolic curvature-minus-one specialization are then derived with the exact factor two. No curvature-identity premise is retained in this packet's final theorem.

`ActualMetricComparison318.metric_comparison` takes an actual compact topological space, continuous positive global metric ratio, continuous chart germs, actual local C² coefficient functions rho and h, positive coefficient values, actual rho curvature<=−1/C and actual h curvature=−1. The ratio need agree with rho/(C*h) only as a neighborhood germ. It proves rho(0,0)<=C*h(0,0) at every point. The actual curvature identity and the compact maximum principle are both derived, by composing with the independently reviewed maximum-principle packet.

## Remaining source interpretation

The actual complex curve, charts, smooth branch/infinity metric extensions, and identification of h as its hyperbolic metric remain geometric inputs. The literal source curvature calculation for rho=U/product distances remains a separate concrete producer; its output can be consumed as the actual curvature bound, not as a new arbitrary scalar. This packet does not construct a Shimura curve or establish the global GeometricRealization existence.

`AxisC2` asks for C² at zero along both real coordinate axes; actual smooth two-dimensional metric coefficients satisfy it. The chart maps may be extended arbitrarily away from their domain since the theorem consumes only their origin, continuity there, and the germ identity. No global preferred coordinate or chart-independent metric coefficient is asserted; only the ratio is global.

## Replay

Run `bash converse-work/conformal-curvature-bridge/verify.sh`. Both modules and the exhaustive axiom audit compile with `debug.skipKernelTC=false`. Frozen maximum-principle sources are not modified. No repository or Git changes were made.
