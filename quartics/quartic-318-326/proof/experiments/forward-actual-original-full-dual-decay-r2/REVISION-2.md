# Hosted223 arithmetic dependency repair

The earlier explicit Fin4+Fin4 decomposition now elaborates; the remaining chart continuity failures are partial-application eta simplification, not incorrect branch coverage. Each branch now explicitly changes the target to its lambda-applied Fin.append expression before Fin.append_left/right. The orbit proof branches already passed and are unchanged. The exact D identity reaches numeral re/im projections: the pinned QuadraticAlgebra API marks re_ofNat/im_ofNat as scoped simp, so they are named explicitly. Continuity composition and all four orbit rewrites passed and remain unchanged.

Only RealDetectorRatios318 changes among564 sources. All full-dual decay, local Fourier series, undamped integral and normalized weight bytes remain identical. HOSTED223-FAILURE.log is exact evidence. This is a source repair candidate requiring distinct review and hosted Lean, not a claim that downstream564 has compiled. No local Lean or profiling.
