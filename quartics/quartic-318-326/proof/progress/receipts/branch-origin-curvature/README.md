# Actual source curvature at branch and infinity origins

This packet computes the remaining actual chart curvatures directly. It does not assume curvature invariance under holomorphic pullback or equate curvatures from different coordinates.

For every nonzero complex b, the actual quadratic-distance function |b+c z²| has zero first derivatives and zero ordinary two-axis Laplacian at z=0. This follows from the real second-derivative chain rule for f(a t²), with opposite signs on the two axes. The derivative of the underlying affine norm function need not be assigned an assumed value. The actual Laplacian of |z|² is four.

From these facts and the proved real-log differentiation rule, the exact coefficient
  4*(a+|z|²+sum |b_i+c_i z²|)/product |b_i+c_i z²|
has actual curvature at zero
  −product |b_i|/(2*(a+sum |b_i|)²).
Every local regularity, nonzero denominator and logarithm rewrite is justified by actual functions and neighborhoods.

`LiteralOriginCurvature318.branch_curvature` binds this formula to the exact completed finite-branch coefficient from MetricSmoothExtension318. Literal source contact separation and norm bounds give curvature at most −1/12540153541944538512 at each of the four branch origins. `infinity_curvature` proves the actual completed infinity curvature is exactly −1/32, hence has the same uniform upper bound.

`SourceMetricCharts318.Chart` collects the three chosen source-coordinate types: ordinary translated t-coordinate away from the four contacts, each finite branch coordinate, and the infinity coordinate. Every coefficient is the literal formula from the frozen source metric packets. Its actual smoothness, positivity and computed curvature bound are proved by cases. The final `metric_comparison` consumes the actual compact-space/chart/global-ratio/hyperbolic-metric interface and derives the source metric comparison without any source smoothness, positivity or curvature premise.

## Remaining scope

The actual compact algebraic/complex curve, realization of these chosen coordinate types as its charts, global positive continuous metric ratio and hyperbolic metric/chart interpretation remain explicit geometric data. No existence of that global realization is claimed. Ordinary t-charts can be chosen at every other point, so the direct origin computation supplies all selected chart curvatures without needing a separate general pullback-curvature theorem or branch limiting argument.

All accepted modules are freshly rebuilt with debug.skipKernelTC=false and recursively checked against only propext, Classical.choice and Quot.sound. See receipt.json for counts and dependency/source hashes. Run `bash branch-origin-curvature/build-all.sh`. No repository or Git changes were made.
