# Actual inert completion, logarithm and scalar divisibility

This packet closes the genuine inert scalar-contact local-field/logarithm seam. It constructs the field and its analytic elliptic subgroup, and composes them with the literal source and the actual global point labels. It does not claim the full `sourceArithmetic` or global detector-height theorem.

## Actual field

For every prime p with no square root of 2 in ZMod p:

- `InertCompletion318.Field p nonsquare` is a complete, ultrametric, nontrivially normed characteristic-zero field. The actual K=Q(sqrt(2)) embeds injectively, with norm exactly p^(-v(x)). The normalization is v(p)=1, not2.
- `InertPadicEmbedding318.padicEmbedding` is an injective isometric Qp ring homomorphism, fixing rational scalars.
- `InertQuadratic318.coordinateEquiv` identifies every completed element uniquely with a+b sqrt(2), a,b in Qp. The norm is exactly max(norm a,norm b), with actual quadratic multiplication.
- `InertIntegers318.Integers` is the complete norm-at-most-one integral subring, with injective isometric Zp and ambient-field embeddings.

## Actual elliptic logarithm

For p≥19 and every D in that actual integral ring, including the literal source D=11−6 sqrt(2):

- `InertChart318.chart_add` identifies the full convergent reciprocal parameter law with actual Mathlib elliptic addition, including identity, inverse and tangent cases, for every u=p*t with integral t. Depth one is included.
- `InertLogHom318.formalSubgroup` is an actual AddSubgroup of E(D).Point. Its `logHom` is constructed from the entire convergent H series and proved additive, injective and norm preserving. No logarithm axiom is supplied.
- `InertMembership318.affine_mem` proves an actual finite point belongs to this subgroup whenever norm(1/x)≤norm(p)^2. It constructs the positive square root by the actual B series at an arbitrary integral argument. A square root, reciprocal sign, and nonzero ordinate are not added assumptions.
- `InertLogHom318.affine_norm_square` and `reciprocal_gain` identify the precise logarithm norm with the reciprocal abscissa, including the factor-of-two conversion of depth.

The generic series/evaluation/branch estimates are proved in sibling scaled-series-bridge and padic-tail packets. They are instantiated at arbitrary inert integral D, not just D in the Qp subfield.

## Literal scalar conclusion

`InertScalarSource318.source_norm_bounds` derives actual formality and relative reciprocal-abscissa norm gain16 directly from the literal scalar rows and positive odd scalar-contact valuation.

`RawInertScalar318.source_scalar_index` then proves p^8 divides the signed scalar index c. Its inputs are:

1. the literal stage0 source constraints;
2. p≥19, inert nonsquare residue condition, and the consumed positive odd scalar-contact valuation;
3. the exact global H=nP+tau and ScalarLabel(w,c), with tau either O or T0.

The third item is precisely the actual global-label output supplied by the separately proved global generator packet. This local theorem proves the coordinate/group base change, membership, logarithm, norm gain and torsion-safe cancellation itself. P need not lie in the formal subgroup. No sourceArithmetic, local log, formality, square-root or precision premise remains.

## Modules and replay

The eleven modules are DiscreteCompletion318, InertCompletion318, InertPadicEmbedding318, InertQuadratic318, InertIntegers318, InertChart318, InertLogHom318, InertMembership318, InertScalarSource318, InertScalarIndex318 and RawInertScalar318.

Run `bash run.sh` against the existing pinned Lean4.35.0/Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679 cache. Kernel checking is explicitly enabled. The audit recursively checks all originating declarations in these eleven modules, allowing only propext, Classical.choice and Quot.sound. `receipt.json` binds module, dependency and verification-log hashes.

This packet uses the actual normed-ring evaluator, so no separate IsLocalRing/IsAdic/maximal-ideal or residue-field presentation is asserted or needed. Global detector height separation, final assembly and completeness remain separate tasks.

## Frozen dependency-closed replay

This frozen packet includes all 133 project dependency modules. Run `bash replay.sh` with `WORKSPACE_ROOT` pointing to the workspace containing the pinned Lean and Mathlib cache. No sibling project modules are used in replay. All 133 modules were rebuilt with kernel checking enabled, followed by recursive auditing of all 3,546 originating declarations; only the three standard axioms were present. `verification.json` records this expanded audit and hashes. The original eleven-module receipt is retained as `source-receipt.json`.
