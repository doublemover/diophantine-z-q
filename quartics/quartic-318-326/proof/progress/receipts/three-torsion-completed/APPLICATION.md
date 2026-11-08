# Constructed objects and exact application

Required input: the literal rank-eight equation algebra, its actual affine coordinate map, a proved unit 2y and tangent diagonal, the actual global completed addition and its finite-input restriction, actual global negation involutivity, and the actual global anti-diagonal inverse law.

Available inputs: ThreeTorsionTangentScheme318.double_neg and diagonal_intoProduct; FiniteAdditionGluing318.restriction at chart 1; CompletedAdditionRestrictions318.inputChart_addition at (0,0); CompletedIteratedAddition318.doubling/tripling; GluedNegation318.negation_twice/negation_over_base; CompletedAdditionInverse318.antiDiagonal_addition. The last two new source families are bound by the exact predecessor receipts below.

Match: the completed inclusion is explicitly the original affine inclusion composed with finiteChart. The pair map is checked through both actual pullback projections. The tangent addition is compared with the actual completed law, rather than merely sharing coordinate values at field points. The triple pair is (-P,P), obtained by applying antiDiagonal to -P and the proved involution. This avoids assuming any unproved group axioms.

Quantifiers and bases: all commutative base rings of the stated Lean universe, invertible 3 and unit discriminant; no reducedness, integrality or characteristic-zero hypothesis. The generic tangent restriction quantifies over arbitrary Scheme tests. The final fiber is an actual Scheme pullback, so its universal property is categorical. No topological count or degree is used to claim an isomorphism.

Normalization and kernel scope: the existing normalized third-division equation and its actual x/y maps are retained unchanged. The current conclusion is a factorization into the actual tripling zero-fiber. The converse/kernel identification, nonzero-component equality, and packaged group object remain separate tasks.

Verification: bounded strict checks of each new module, then recursive axiom audit of all declarations in the four modules. Predecessor code and compiler caches are reused. The source author does not claim independent acceptance; hosted integration and separate review remain pending.
