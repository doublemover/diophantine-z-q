# Independent original exponential restriction source review

## Observed frontier
Own hosted evidence records SplitReducedGauge passing (3.473s), then OriginalOpenExponentialNaturality failing at exp_restrict's generic unit_restrict rewrite. The exact displayed target uses the same presheaf Hom.hom restriction but rewrite cannot infer/match the generic producer pattern. No failure elsewhere in the module is promoted to a separate diagnosis.

## Exact application and orientation
The candidate unfolds the same two exp_original equations, then explicitly supplies unit_restrict with the original thickening R p, its actual epsilon, the original epsilon_square proof, the entire preimage inclusion (π.preimage_mono h), and exactly π.app V a. The producer restrict is exposed and is literally the displayed presheaf-map Hom.hom. Thus the first equality has precisely the original restricted exponential as left side and the unit of the restricted π.app V a as right side. Transitivity then uses the original naturality square in the same reversed orientation to identify π.app W of the original section restriction. No abstract alternative unit, arbitrary square-zero element or comparison is substituted.

## Whole-open domain and consumer
Arbitrary CommRing R and scheme X, p, both affine opens V,W and W≤V remain exactly as before. All whole thickened inverse-image opens are retained; no top-only, pointwise or smaller-open reduction is used. The original unit 1+epsilon*a and its inverse sign are unchanged, and no IsIntegral or new nonzero hypothesis is added. Other declarations (exp_neg, reduced_appLE) and resource options are unchanged.

OriginalTwoOpenGaugeLog uses this exact restriction equation on both open components to turn the actual reduced multiplicative gauge into the original additive coboundary, with its existing signs. OriginalOpenDualCoordinates.units_restrict uses it in the full-unit factorization with the actual coefficient/epsilon maps. These consumers and the native unit_restrict producer were inspected and remain unchanged. Explicit application is source-grounded, but concrete expected-type conversion must still pass hosted elaboration.

The companion manifest binds the exact reviewed source, contracts and evidence. No local Lean/Lake or user computer was used. Source review does not establish a candidate Lean/kernel pass, later consumer success or final mathematical acceptance. Successor propagation/metadata review remains separate.
