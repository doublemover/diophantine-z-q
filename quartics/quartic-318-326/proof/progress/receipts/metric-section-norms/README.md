# Actual all-chart bicanonical section norm bounds

This packet joins the literal bicanonical coefficients to the actual source metric and its derived compact comparison. It does not take an unexplained archimedean section-norm bound as input.

`SectionCoefficientBounds318` assigns the exact q0/q1 coefficients from BicanonicalCharts318 to every SourceMetricCharts318.Chart. Their complex norms are bounded by that chart's source metric coefficient at its origin. For ordinary coordinates this is 1<=U and |t|<=U, using the actual contact0. At a finite branch the same inequality is proved from the remaining distances; the contact0 case is separated correctly. At infinity the actual section values(0,4) are compared with the actual metric coefficient16. There is no undefined affine ratio or unproved continuity extension at infinity.

`PeterssonSectionNorm318.quadraticNorm` uses the actual cotangent-coordinate norm2/sqrt(h): |q|*(2/sqrt(h))². It proves the exact formula4|q|/h for positive h, keeps the bicanonical factor four, and proves multiplication/scaling. Source metric comparison rho<=C*h then yields both coefficient norms<=4C. Literal J² scaling gives precisely J²*(4C), with J=2765952000 and C=12540153541944538512.

`GlobalSectionNorm318.Data` retains actual compact-space/chart/global-ratio/hyperbolic data, but has no source curvature bound, source metric regularity premise or section-norm estimate. Its final `integral_section_norms` composes the actual computed source chart curvatures, compact maximum principle and exact coefficients to produce the required two archimedean bounds at every point.

## Scope

The actual compact geometric curve and chosen charts, the global continuous ratio, and the hyperbolic metric realization remain explicit. Interpreting the coordinate cotangent norm2/sqrt(h) as Yuan's Petersson metric and identifying the local coefficients with globally glued sections of the arithmetic bicanonical line remain geometric/frame identifications. Arithmetic vertical integrality is a separate producer. No actual global algebraic model or FiveContact49Height existence is asserted.

All modules and exhaustive recursive axiom audit are freshly replayed with debug.skipKernelTC=false. Only propext, Classical.choice and Quot.sound are accepted. See receipt.json for exact counts and hashes. Run `bash metric-section-norms/build-all.sh`. No repository or Git changes were made.
