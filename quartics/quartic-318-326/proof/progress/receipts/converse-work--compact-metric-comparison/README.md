# Actual compact maximum principle for the contact metric

The main theorem `CompactMetricComparison318.compact_metric_comparison` proves rho(x) <= C*h(x) on an actual compact topological space with continuous positive ratio. It uses actual chart maps and the ordinary two-real-coordinate Laplacian, defined with Mathlib derivatives. It does not assume a maximum-principle comparison or a Laplacian sign at a maximum.

## Checked analytic chain

1. `second_deriv_nonpos_of_localMax` proves that the actual second derivative of a continuous real function is nonpositive at a local maximum. If it were positive, Mathlib's second-derivative test would give a local minimum too. The function would be locally constant; differentiating the eventual equality twice contradicts the positive second derivative. This works with Mathlib's total derivative and does not smuggle in a second-derivative sign premise.
2. `laplacian_nonpos_of_localMax` restricts the actual coordinate function to the two coordinate axes, derives their local maxima by continuous composition, and adds the two nonpositive second derivatives.
3. `curvature_forces_positive_laplacian` checks the exact source arithmetic: for C,h>0 and ratio r>1, curvature k<=−1/C and L=−2k(C*h*r)−2h force L>0.
4. `compact_ratio_le_one` obtains an attained global maximum of the actual continuous ratio using compactness. Positivity makes its logarithm monotone, and the chart-origin identity gives a local maximum of the actual chart log-ratio. The preceding Laplacian contradiction proves every ratio value is at most one.
5. `compact_metric_comparison` specializes ratio=rho/(C*h) and derives the literal metric comparison rho<=C*h with the exact source curvature formula.

## Application to the source

X is the compact complex curve of the actual maximal discriminant-210 Shimura model. In each chosen complex chart, rho is the smoothly extended source metric U/product|t−a_i|, h is the curvature-minus-one hyperbolic metric, and C=Cmet. The ratio is independent of the chart. The arguments `rho x` and `h x` may be read as the two coefficient values in the chart chosen at x; only their invariant ratio is required to be globally continuous. No global preferred coordinate is asserted.

The actual chart inverse can be extended arbitrarily outside its domain: only continuity and its value at the origin are used in the maximum argument. No injectivity premise is needed for this step, although actual complex charts supply it. The metric's smooth positive branch and infinity extensions, the exact conformal curvature identity, and the curvature estimate −K_rho>=1/Cmet are supplied by the independently reviewed source calculation. Smoothness makes the formula valid across the removed branch points. Compact hyperbolic uniformization and those geometric/chart identifications are not constructed in Lean here.

Thus this packet removes the compact maximum-principle analytic implication from the retained source inputs. It does not claim a Lean construction of the Shimura curve, its hyperbolic metric, the source curvature calculation, or the global FiveContact49Height proposition.

## Replay

Run `bash converse-work/compact-metric-comparison/verify.sh`. All project declarations are recursively audited with strict kernel type checking; only standard roots are allowed. Mathlib's official DerivativeTest cache was fetched without modifying its source. No repository, Git, or frozen upstream source was changed.
