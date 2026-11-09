# Actual rational level-three moduli isomorphism

Status: uncompiled hosted-CI candidate. Structural checks and non-author source
review are not kernel validation. No local Lean build was run.

This larger continuation constructs both directions of the Q-algebra isomorphism
between the actual rational base change Q tensor_Z Fixed3 of the original
arithmetic diamond quotient and the original rational parameter open. Explicit
Bezout certificates make all inverse denominators units in the whole ring,
including potentially nonreduced rings. The inverse is constructed using both
localization universal properties. Tensor/localization/root extensionality prove
both compositions are identities, preserving the original j and x generators.
The previous complex-point bijection is not used as an isomorphism criterion.

Applying Spec gives the actual scheme isomorphism and an open immersion of the
rational arithmetic model into the original projective source. Its composition
with rationalization is the exact preceding arithmetic scheme map. Its global
j square uses the existing finite projective j morphism. The actual Γ1(3)
sourcePoint comparison lifts through the isomorphism and agrees both with the
original arithmetic schemePoint and compact analytic/projective comparison.

This is an isomorphism after actual rational tensor base change, never an
isomorphism to the unchanged integral target. No extension through3 or filling
of the original affine x chart at excluded elliptic values is claimed. Density,
actual projective generic-stalk degree, global flat rank, full divisor/PEL inputs
and full318/326 arithmetic completion remain distinct obligations.

## Exact application contract

1. Rational base change of the exact arithmetic model. Required: The rational source cannot be declared isomorphic to the unchanged integral arithmetic quotient. Constructed: ThreeRationalFixed318.Ring is literally Q tensor_Z LiteralThreeXComparison318.Fixed3, with the original includeFixed map, original base j and original xGenerator. Application: All target coordinates and its normalized quartic relation come from the original sign quotient and division polynomial after this actual tensor base change. No alternate quartic or arbitrary roots replace the original algebra.

2. Unit certificates over rings. Required: The rational inverse must work in the entire coordinate ring, not merely in a fraction field or after complex evaluation. Constructed: ThreeNormalizedInverse318 gives explicit Bezout identities for x, x^2-k and9k-x^2 modulo the original normalized quartic. Application: The required k and k-1 are units, and all positive rational constants used are units through the Q algebra. The identities produce actual units in any commutative Q-algebra, without reducedness, field or domain assumptions.

3. Constructed inverse parameter and exact formulas. Required: The inverse parameter must have verified denominators and recover both original j and x. Constructed: The parameter is243*(x^2-k)/(9k-x^2) using the constructed unit inverse. Exact homogeneous identities reconstruct D, x and j. Application: The same certificates show the parameter and D are units. The original base relation k*(j-1728)=j and invertibility of k-1 recover N(parameter)=j*parameter^3 inside the rational fixed algebra.

4. Both localization maps constructed. Required: An inverse written as a rational expression does not supply the required map of coordinate rings. Constructed: backwardLaurent is the actual localization lift at T using the proved parameter unit. Its image of original jLaurent equals the original rational fixed j. backward then lifts at jLaurent*(jLaurent-1728) using the original base units. Application: The inverse lands in the actual rational fixed ring and preserves j and x exactly. No pointwise argument or generic extension is used to construct it.

5. Forward tensor map preserves original arithmetic map. Required: The forward map after rationalization must be the extension of the preceding constructed integral-algebra map. Constructed: forward is the tensor-product universal map from Q tensor_Z Fixed3 to the original rational parameter ring, extending fixedMap and the Q algebra map. Application: forward_fixed is exact agreement on every original fixed-algebra element. Its j, x and normalized k formulas use the original fixedMap_base and fixedMap_x, retaining the earlier scheme map.

6. Two-sided inverse in coordinate rings. Required: A bijection on complex points alone cannot establish the requested algebraic isomorphism. Constructed: forward_parameter is proved by cancellation of the constructed denominator unit and a ring identity. forward_backward uses both localization extensionality principles and the polynomial generator. backward_forward uses tensor extensionality and original j/x generator separation for maps into arbitrary commutative rings. Application: The complete Q-algebra equivalence is built from these two proved compositions. No complex-point bijection, normality shortcut or assumed degree comparison enters the proof.

7. Actual scheme isomorphism and factorization. Required: The resulting scheme equivalence must preserve the original integral target and its arithmetic map. Constructed: schemeIso is Spec of the explicit Q-algebra equivalence. rationalization is Spec of includeFixed. arithmeticMap_factor identifies their composition with the earlier actual arithmeticMap. Application: This is the correctly rational-base-changed target, not an isomorphism to the integral target. Every original algebra element is respected by equivalence_fixed, proving exact scheme factorization.

8. Original projective and compact analytic consumers. Required: The algebraic identification must connect back to the actual projective j morphism and actual modular source. Constructed: rationalEmbedding is the inverse schemeIso followed by the original open projective embedding and is an open immersion. Its j square is the exact original global map. The existing sourcePoint comparison lifts through schemeIso and returns to the same arithmetic schemePoint and compactPointHomeomorph. Application: The actual marked-period and full-domain arithmetic comparison from71 are inherited unchanged. The global finite map, cusp/elliptic holomorphy and orders remain those of the same original projective source, not a replacement of the model. Density/proper compactification is not inferred solely from an open immersion.

9. Validation and remaining full-theorem obligations. Required: The larger model-identification stride still requires hosted kernel checks and non-author source review. Constructed: Five new modules extend70 unchanged sources and one narrowly repaired cusp comparison. Exact polynomial/Bezout identities were also checked by symbolic expansion as diagnostics. The candidate supplies actual rational arithmetic-open isomorphism and its scheme and analytic consumers. Application: No Lean ran locally. Actual projective generic-stalk degree, global flat rank, complete divisor/PEL universal-family inputs and the full318/326 arithmetic theorem remain separate. This packet does not extend the original integral family through3 or the deleted elliptic values.

