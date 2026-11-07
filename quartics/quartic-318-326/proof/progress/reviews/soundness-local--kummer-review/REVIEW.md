# Independent source/Kummer boundary review

Copied and independently kernel-rebuilt seven modules: KummerAlgebra318, RootPointAlgebra318, RawRootPoints318, RawScalarKummer318, KummerGroup318, RawScalarOrientation318 and RawGroupAnchor318. Full recursive audit passes 41 declarations with only propext, Classical.choice and Quot.sound. Exact copied sources and hashes are retained here.

The root reconstruction does not invert u or t. Its only reciprocal difference denominator t²−u² is proved nonzero from the actual source guard, so the u=0 and t=0 identity-chart boundaries remain included. The reconstructed root-square ordinate factor satisfies its curve equation by a polynomial identity. Nonzero root and nonsingularity are proved rather than supplied. The four current raw patterns, including the half-scale CSE in the T root, are decoded directly.

The scalar Kummer factorization does not divide by h²−x(P). The unequal-abscissa alternatives are connected to actual Mathlib subtraction, including ordinate negation on the second branch. The coincident-abscissa branch identifies a=±1 using the already-proved infinite order of P, reconstructs x(2P), and chooses c=−2 with the correct signed orientation. It therefore does not manufacture an inverse guard or silently lose the tangent case. Source rows 270–273 are the actual inputs to this factorization.

No scope mismatch found. RawGroupAnchor318 explicitly retains only the inherited SquarePointGeneration assertion. Its definition is the genuine assertion that every square-abscissa point on the actual curve is an integer multiple of the displayed P; it is not proved by this packet. The following source/anchor consequences are honestly conditional on that assertion.
