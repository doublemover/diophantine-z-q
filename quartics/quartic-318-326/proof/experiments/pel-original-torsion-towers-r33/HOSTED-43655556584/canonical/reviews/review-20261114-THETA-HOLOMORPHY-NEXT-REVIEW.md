# Independent exact theta holomorphy repair review

Verdict: source/application review PASS for future hosted checking only. No local Lean was run. This is not a compiler acceptance or lane-success claim.

Reviewed manifest SHA256 14a4af77e7fafe3acac1c97f8e447c4e46c4250c5dbc590938a6674c99a2328f and APPLICATION.md 2254721203ce63f8c16f189982ebedfe2bea7b630786b9075298b340c4782afb in pel-20261115/theta-43655556584. All 11 listed file bindings verify. Both before sources exactly match published torsion27 at commit 6b664f8406d512c50432425e3bd616447ff8ad8e.

After-source hashes:
- PELOriginalThetaHolomorphy318: db5fd1a4c5c4b151c9b37c1d48f8538800fa20058bd54fe71afb7f5b59800be4.
- PELOriginalScaledThetaHolomorphy318: 781f4f5c6a631605491723119c42185a4b1bafd02433fbbc8b2d3a1ab3026a16.

Read both full candidate modules, exact diffs, current nine-obligation application, actual torsion27 failure, native operator-norm and SmoothSeries declarations, and actual exposed unscaled/scaled term definitions.

1. The native opNorm_le_bound explicitly takes the continuous linear map first. Supplying (linearMap n), then the typed nonnegative slope and the unchanged full-space pointwise bound addresses the actual wrong-argument application without increasing resources. Both integer coordinates and the native sup norm remain intact.
2. The actual term definitions are exp(constant quadratic part + (2*pi*I)*linear n z), including the scaled constant part. Existing const_mul, const_add and exponential chain rule therefore have the function and derivative identified by the new change statement. smul_smul matches precisely the unchanged derivative (term*(2*pi*I)) • linearMap. There is no sign, scalar, variable, or derivative substitution. Lean must still verify the proposed definitional equality.
3. Pinned SmoothSeries genuinely declares hasFDerivAt_tsum_of_isPreconnected with the eight arguments used here. Adding its public import supplies the missing API rather than renaming or inventing a theorem. The argument remains full complex Frechet differentiation on C² using summable derivative bounds on the same open, preconnected unit ball and actual pointwise theta summability.
4. Unscaled changes target the three authentic current failures: line15 definitional-equality timeout, line29 derivative carrier/equality elaboration, and line96 missing theorem. The unchanged convergence modules genuinely passed before this frontier. Scaled differentiation is explicitly preventive and was not reached. Its parameter a affects only the constant-in-z part; elementary differentiation needs neither positivity premise. All existing hτ/ha binders for the bounds and full sums are retained. The fixed frequency predicate remains chosen independently of z.
5. Exact diff introduces no changed declaration telescope, weakened conclusion, surrogate sum, omitted frequency, extra premise, trust escape, or resource option. No downstream module or complete lane is asserted to compile. Production propagation must separately bind every intended copy and its own current predecessor evidence.

Authentic result binding: cea32cda58e8a0ce1b12f8d025cd8163c6658dd95e9b511325eb3a7ddac51813 from run43655556584. ThetaConvergence passed1.618s, ScaledThetaConvergence passed1.768s, ThetaHolomorphy failed11.938s. These observations are historical evidence for this repair, not validation of its after sources.
