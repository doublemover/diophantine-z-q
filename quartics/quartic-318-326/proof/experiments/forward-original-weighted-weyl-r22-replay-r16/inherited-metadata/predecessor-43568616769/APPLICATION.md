# Scalar pole domain multiplication/division normalization (source-only)

Basis: hosted run 43564923898 at b3d76fb41c03f9194b0613eac0a9b4cb04b2576c. The descent predecessor is forward-actual-two-descent-root-divisor-orders-r7, artifact 14102381067, ZIP SHA-256 394c809cd2a235060d8d71b3d5090ffdd2cb7a6183aa8c5359a5de87ed6e1f27. Its ScalarForwardWitness318 passes 4.173 s; ScalarPoleRealDomain318 fails 3.525 s. Exact RESULT/log and source-before bytes are retained. Weighted predecessor source bytes match exactly; its own hosted result must be bound separately before propagation.

The only error is pole_domain line 64. After div_pow, the displayed goal contains A * (W^2 / d^2), where A = 114444 * inputR (w 0) and d = 1 + A. The forward mul_div_assoc rewrite searches for A * W^2 / d^2 and does not match. The candidate changes only `rw [div_pow,mul_div_assoc]` to `rw [div_pow,← mul_div_assoc]`. This is the equality A*(W^2/d^2) = (A*W^2)/d^2 in the required direction. It exposes the exact quotient consumed by the unchanged `(div_lt_iff₀ (sq_pos_of_pos hd)).mpr`.

## Required inputs, actual object, and full domain

The public packed_bound and pole_domain binders and statements are byte-identical: every w : Assignment and n : ℤ with rational 10 < inputR (w 0), 0 ≤ w 33 ≤ 1, 1/100 < |w 37| ≤ 1 and |ActualScalarRoot318.inverseNorm n| < 1. No endpoint, exceptional case, section subset or index restriction changes. The original packed_bound proof and positivity half of pole_domain are unchanged. The only changed application is a denominator-association identity in the upper-bound half.

ScalarForwardWitness318 still defines W = N^2 + inputR(w 0)*Q^2, quotient = W/(1 + 114444*inputR(w 0)), and poleInput = 114444*inputR(w 0)*quotient^2. The return value remains exactly 0 < poleInput w n ∧ poleInput w n < 17, not an existential or replacement pole. The scalar denominator remains the same positive d^2; hd already proves 0 < d from the original hypothesis. No coefficient, normalization, comparison map, norm, power, field or ring changes. This scalar algebraic equality applies universally in ℚ without adding a nonzero assumption.

After rewriting and clearing the positive denominator, the existing inequalities hW0 and hW10 give W^2 < 100. The unchanged hp multiplies by A > 0; the unchanged final nlinarith uses A*(A-10)>0 to bound A*W^2 by 17*(1+A)^2. Those downstream tactics are not locally compiled by this repair and remain hosted-pending.

## Exact downstream consumer

PreparedIntegerSource318.scalar_domain applies pole_domain to DetectorGateWitness318.witness (a:ℚ) labels h and n = labels 1. witness_input plus integer_inputR_large supplies the input bound; detector33 and common_bounds supply both half-trace bounds; detector37 and hscalar/common_bounds supply the norm bounds; inverseNorm_bound consumes hn(1) and hn1. The consumer returns the original scalarB bounds, since scalarB is this exact poleInput. Those files and all their definitions are unchanged.

## Scope and verification

The before hash is a8a209c8e90bb8176305d780faabcdbf2b8468dd4716a73f767a4a89736d7124; candidate hash is dfc9dd54cb166016652b74d665a1240770e6af6bcc23644f3746dce93e5d14bd. Exactly one proof-line direction edit is included. No resource setting, import, public statement, other source or speculative downstream repair changes. Prior reviews remain historical evidence, not acceptance of this change. Internal independent source review and later exact successor propagation review are required. No local Lean/Lake build, kernel acceptance or full arithmetic theorem verification is claimed.
