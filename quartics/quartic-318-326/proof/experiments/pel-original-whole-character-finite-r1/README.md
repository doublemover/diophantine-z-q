# Whole original finite-flat character maps and exact deck kernels

Seven connected modules extend the recovered chart-gluing construction without changing any predecessor Lean source.

1. The OLD finite source chart is schematically dense in the actual original integral FourRootGluedScheme. Relative equality into any separated target extends from that exact chart.
2. The projective affine transformation x ↦ (b−a)x+center restores the OLD original unshifted t coordinate. The global composite of the original whole character map with this target t-map equals the already constructed original projective projection, as an equality of Scheme morphisms.
3. IsFinite.of_comp applies to this literal finite original projection and separated target t-map, proving global finiteness of the same character morphisms. Proper finite-fiber descent proves finiteness of their actual target t-maps as well.
4. Global original deck invariance holds if and only if the original analytic label lies in the specified character kernel. The reverse direction restricts to the finite chart, cancels the target open immersion, and uses Spec faithfulness and the previously proved whole-cubic ring kernel. No replacement action is used.
5. Existing rational bivariate-integrality and Weierstrass-Dedekind arguments are extended over a general field, retaining actual polynomial algebra structures. At infinity, use z as polynomial base and the monic cubic in x; there is no extra A≠0 or B≠0 assumption.
6. Applying DedekindAffineFlat318 to both entire actual target charts proves global flatness of the same finite dominant original morphisms, including every branch and infinity point.

This packet does not prove the native generic-stalk degree8, constant Scheme rank8, categorical quotient property, four numerical j equalities, rational descent, represented Jacobian or PEL family identification. It uses the actual uncomputed complex branch coordinates, not the manuscript constants. The source remains genus five, not elliptic.

Historical attribution: the schematic equality, projective affine transform, finite-factorization, proper-fiber-descent and Dedekind-flatness routes already occur for the separate published rational completion in baseline modules. This packet constructs the connecting argument for the original complex-analytic branch model and preserves all transition maps and object identities. It does not call those old methods new.

No local Lean compilation or profiling. Static closure and independent source review are separate from hosted Lean acceptance. Hosted verification pending.
