# Actual integral quaternionic period-map proof normalization

Own trace24, exact HEAD eeb2a2fb55e45c09bde7e013bef8f98d2f00be51, run43667489535. No local Lean.

1. Inputs: arbitrary Ring B, original ring representation rho:B→+*RealMatrices, subring O, element n:O, complex tau and exact nonzero Mobius denominator hd. No invertibility/unit assumption on n, no new complex algebra or multiplicativity of the period map.
2. Object: same denominator complex-linear periodScalar, actual translated-parameter original period map and descended quotient additive map. Only proof normalization changes.
3. Domain: full original B, original O-period subgroup and every vector/class of the quotient; not a selected chart or finite sample. Genuine nonunit n remains allowed and quotient map is not turned into a lattice equivalence.
4. Maps: explicit map_mul rho x (n:B) rewrites only the actual representation of x*n BEFORE the linear period map is exposed. The linear real period map is never treated as multiplicative. Exact right matrix product rho(x)*rho(n), not left order action, remains.
5. Scalars: map_smul proof explicitly simplifies RingHom.id Complex before smul_smul/ring. Native period_mobius supplies the same inverse denominator, canceled only with hd. No sign, tau translation, order or scaling factor changed.
6. Consumer: scalar_period feeds the same subgroup inclusion using O.mul_mem, exact QuotientAddGroup.map, mk formula, scalar-inverse surjectivity and commutation with original left order endomorphism. All downstream proofs byte-identical.
7. Exceptions: zero denominator remains excluded only by existing hd; no finite-kernel result inferred from surjectivity. Neither nonunit right-lattice inclusion nor original lattice index is strengthened into equality.
8. Own evidence: current trace24 RESULT packet hash equals actual predecessor intake; exact log reports RingHom.id scalar residual and a generic map_mul wrongly targeting the linear period map. Original residue_lift/cokernel now pass upstream; no new candidate or downstream pass claimed. Exact native period_mobius and ring representation source included.
9. Boundary: two proof-line edits, public definitions/types/hypotheses/imports/options unchanged. No additional trust/resource or input premise. Independent source and future per-lane propagation/hosted verification remain separate from source correctness.
