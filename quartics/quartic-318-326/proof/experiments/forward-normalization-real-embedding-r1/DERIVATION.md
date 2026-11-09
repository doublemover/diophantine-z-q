# Positive real realization of both normalized source generators

Status: source-policy and dependency-closure checks passed; hosted Lean and distinct review pending. No local Lean compilation was run. Four predecessor sources are unchanged from forward-normalization-injection-r1; NormalizationRealEmbedding318 is the only new source.

## Actual field embedding and root signs

extendRoot uses QuadraticAlgebra.lift with the supplied base ring homomorphism made into its explicit algebra structure. Its evaluated coordinate formula and its equality on the literal algebraMap are proved. This is a genuine ring homomorphism from the quadratic algebra, not a substitution on selected polynomials.

The original positiveEmbedding sends delta=3-sqrt(2) and deltaBar=3+sqrt(2) to positive real numbers. alpha and beta are their positive square roots. firstEmbedding sends First to the reals, extending positiveEmbedding and sending its quadratic generator to alpha. realEmbedding then sends Both to the reals, extending firstEmbedding and sending the second quadratic generator to beta. Both is the actual field already constructed by the nonsquare tower, so this ring homomorphism is injective.

The compatibility equations are literal:

- realEmbedding(base(x)) = ActualQuadraticEmbeddings318.positiveEmbedding(x).
- realEmbedding(conjugateBase(x)) = ActualQuadraticEmbeddings318.negativeEmbedding(x).
- realEmbedding(firstRoot) = alpha > 0.
- realEmbedding(secondRoot) = beta > 0.

The conjugate compatibility is checked on arbitrary quadratic coordinates using the original SourceContact318.conj and both original real embedding formulas. No second embedding is chosen independently of the first, and no sign is left unspecified.

## Actual real elliptic points

realPoint is the existing injective pointMap under realEmbedding, followed by coefficient transport along realEmbedding(1)=1. It is an injective additive map on the actual coefficient-one elliptic group. firstRealGenerator and secondRealGenerator are the images of the exact normalized algebraic generators, each originally constructed from the same literal LocalGenerator318.P.

Applying injectivity and map_zsmul transfers the predecessor's unconditional integer-relation theorem to these actual real E_1 points. Their exact finite coordinates are also proved:

- firstRealGenerator: x=alpha^-2*positiveEmbedding(xP), y=alpha^-3*positiveEmbedding(yP).
- secondRealGenerator: x=beta^-2*negativeEmbedding(xP), y=beta^-3*negativeEmbedding(yP).

These coordinate statements include the actual nonsingularity proofs and equality in the Mathlib point type. They do not substitute coordinates for the additive point-map identity.

## Remaining real/topological comparison

The real field and sign comparison is now supplied by this packet, subject to hosted checking. The normalized source points still need to be joined to the actual real quartic oval orbit, including the precise finite-kernel behavior of the quartic-to-reciprocal elliptic map at both u=0 points and the v=0 endpoints. A character, circle, or compact-Lie argument is still required before integer independence yields the needed orbit-closure/component statement. No full-product density, finite component modulus, m=1, or scalar/guard-good intersection is asserted here.

The historical component argument in quartics/quartic-318-326/docs/arithmetic.md and docs/sources/quartic_v10.tex, lines10632-10694, retains its prior-justification-found status. This is formal progress toward a concrete alternative comparison, not a claim that the historical argument had a new gap. No accepted manuscript, source polynomial, first51 assignment, fixed signs, CRT conditions or scalar threshold is changed.

SOURCE-COPIES.json binds the four unchanged producers; DEPENDENCY-PINS.json binds all91 required baseline modules. Source policy is not Lean elaboration or mathematical acceptance. The recursive audit is prepared for hosted CI. No browser tabs were opened.
