# Independent source review: scalar pole denominator association

Internal source/application comparison only, no local Lean/Lake/compiler or proof build, no kernel or full arithmetic acceptance.

Exact base b3d76fb41c03f9194b0613eac0a9b4cb04b2576c; run 43564923898. The before source matches both published forward packets byte-for-byte. Own descent RESULT matches the published predecessor intake and records ScalarForwardWitness passing 4.173s, then ScalarPoleRealDomain failing 3.525s. Weighted own replay evidence was not part of this review and must be bound before propagation.

Before a8a209c8e90bb8176305d780faabcdbf2b8468dd4716a73f767a4a89736d7124; candidate dfc9dd54cb166016652b74d665a1240770e6af6bcc23644f3746dce93e5d14bd. Contract reviewed e3e90e4366c8d6b2c610108ca8ecfa7204c8d348b414720bbbae970d03a9463f. Exact own RESULT a401d4a9e37fa7f6c88486668ee4df5bf5200d77813074709840f6b828e85d0e; log 5973f3b288cb159fdcb6a9de507cb84f8dc38d0e681732734fdc203d6aaf9b39.

Exactly one edit reverses mul_div_assoc after div_pow. The hosted rewrite failure explicitly states it sought a*b/c, while the actual goal is A*(W^2/d^2)<17 with A=114444*inputR(w 0) and d=1+A. The reverse direction exposes (A*W^2)/d^2, exactly the left quotient required by the unchanged div_lt_iff₀ application. This is the same rational-ring equality, with no added nonzero premise; positivity of d^2 is already derived from the original input hypothesis.

The required domain remains every rational assignment w and integer n with the same r>10, detector33 bounds, detector37 absolute-value bounds, and original inverseNorm bound. packed_bound and the positivity half of pole_domain are unchanged. The original W, quotient and poleInput definitions retain their coefficients, powers and normalization. Full conclusion remains 0<poleInput w n and poleInput w n<17 for the same input, not an existential scalar or subdomain.

After denominator clearing, W^2<100 and A>10 give A*W^2<100*A. The unchanged final arithmetic is valid: A*(A-10)>0 implies A^2>10*A, hence 17*(1+A)^2-100*A=17*A^2-66*A+17>104*A+17>0. No omitted sign or scalar factor appears. This source reasoning does not claim the final nlinarith tactic has yet run successfully.

I read the copied original ScalarForwardWitness definitions and PreparedIntegerSource.scalarB/scalar_domain. The latter consumes exactly pole_domain at the original detector witness and labels1, using witness_input/integer_inputR_large, detector33/common_bounds, detector37/hscalar and inverseNorm_bound. Its scalarB is literally this poleInput. The input maps and all consumer files remain unchanged. There are no transition/norm-map changes; no relevant index or exceptional case is discarded.

All public signatures/imports/options are byte-unchanged (existing maxHeartbeats0 was not introduced). No source-level blocker found. Exact successor source propagation and own weighted evidence still require review; hosted elaboration remains pending.
