# Genuine tangent metric and exact Petersson operator norm

For the actual Γ1(N) complex quotient with N ≥ 5, this packet constructs a nondegenerate complex seminorm on each genuine Mathlib tangent fiber and proves continuity on the genuine tangent bundle total space. Its formula is invariant under every actual quotient chart change, using the actual derivative and its actual imaginary-part transformation.

Normalization is explicit: the source cotangent basis norm is 2/sqrt(h)=2 Imτ for h=1/(Imτ)^2. Its dual complex tangent length is therefore |u|/(2 Imτ). The ordinary real hyperbolic line element |u|/Imτ is twice this length. This packet does not claim curvature −1 for a rescaled real metric.

For the genuine bilinear form corresponding to an actual orbit fiber, `ActualOperatorNorm318.evaluation_norm` proves exact norm evaluation on any two actual tangent vectors. An explicit actual unit vector attains the bound. `operator_bound_iff` and `unit_ball_bound_iff` characterize the optimal bound; `MetricOperatorSupremum318.operator_norm_eq` proves the literal supremum over the actual metric unit balls equals the original descended Petersson norm. Thus the norm is exactly |q|(2 Imτ)^2, including factor4, not just an arbitrary coordinate weight or an upper estimate.

All constructions use the already proved global holomorphic bundle equivalence with the standard tangent bilinear-form Hom bundle. Analytic/algebraic Kähler-sheaf comparison, cusp extension and the specified arithmetic source/model remain separate. The chosen-frame construction is not a global trivialization: the seminorm is proved chart-invariant and continuous.

Replay `bash build-all.sh`; every declaration is kernel checked with `-Ddebug.skipKernelTC=false` and only the three standard allowed roots.
