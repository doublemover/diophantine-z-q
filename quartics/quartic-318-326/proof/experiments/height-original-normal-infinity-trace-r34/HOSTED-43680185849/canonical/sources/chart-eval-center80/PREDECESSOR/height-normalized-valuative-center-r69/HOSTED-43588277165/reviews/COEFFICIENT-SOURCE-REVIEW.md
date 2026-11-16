# Independent rational differential coefficient source review

Verdict: no source-preservation blocker found in the two exact candidates. Branch is an observed-frontier repair; Infinity is PREVENTIVE_UNOBSERVED and must remain separately labeled. Neither candidate has been run through Lean by this reviewer. New successor application contracts and propagation remain separate.

## Observed Branch candidate

IntegralRationalBranchCoefficients318 after c742f9860e5df2d0dfe1d7f982403496aea4f2783e0c40e74287a9c494146656 changes only the differential proof after its unchanged statement. Actual run43588277165 at83851e60, artifact14111707743, shows full IntegralRationalGlobalComparison PASS5.784s, then Branch FAIL49.311s. The sole logged error is the coordinate rewrite failing after map_D under the coerced AlgHom application and original branch carrier aliases. This does not establish a general instance-cause diagnosis.

The candidate first applies the same universal-differential map_D, explicitly changes to D on the actual ContactIntrinsicFrames.BranchRing applied to the SAME branchEquiv and original signed sourceCoordinate, then applies congrArg of that exact D to coordinate c i. This is the native proof route used in the already compiled IntegralRationalFiniteAtlas.differential, rather than a replacement comparison. Every original c:Fin4→Q-units and branch index i remains. The whole branch localization including ramification points, root sign and exact coordinate identity are unchanged.

## Preventive Infinity candidate

IntegralRationalInfinityCoefficients318 after 56592972920c55425f53ee16024e67bfdefe83a391363d72312b9fae171e7cbc makes only the literal corresponding differential proof change. No own Infinity error or pass is claimed. It uses the original rationalOrderEquiv, full IntegralInfinityChart.Order, original reciprocal coordinate and actual InfinityOpenChart.OpenOrder. congrArg D consumes exactly coordinate c. It introduces no chosen differential, generic field equality or smaller chart.

## Exact application and scalar preservation

Both public statements, imports, resource/trust options, all coefficient and inverse-denominator identities, and every other source byte remain unchanged. The factor4, inverse twist, J-squared scaling, both bicanonical coefficients, and infinity c0^-5/c0^-4 conventions are untouched. AlgHomDifferential318.map is the original universal differential map restricted to the original base scalars; map_D uses the same f.toRingHom.toAlgebra/tower, not an assumed derivative formula.

The direct actual consumers are IntegralOriginalBicanonicalRestrictions318.branch_restriction and infinity_restriction. Each invokes the corresponding scaled_coefficient and differential after weightedSquare_restrict_to, then identifies both original global sections on their entire original opens. Those exact consumer passages, the compiled FiniteAtlas route and original coordinate producers were inspected and snapshotted. FiveChartGeometry provides surrounding chart context, not a falsely claimed direct differential call.

The independent checker verified both precise before/after deltas against published83851e60 Git objects, the complete own ZIP digest/RESULT/intake/log identities and relevant primary producer/consumer source bytes. Global full-module success is authentic evidence about Global only. The concrete new change steps, complete candidate modules, downstream kernels, recursive axioms and packet acceptance still require hosted checking. No production source or acceptance metadata was modified during this review.
