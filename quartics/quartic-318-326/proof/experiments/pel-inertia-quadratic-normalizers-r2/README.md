# Original inertia normalizers and quadratic fixed points

Construct five actual integral normalizer involutions and imaginary quadratic field embeddings in the original quaternion algebra, with norms exactly the five original inertia-label divisors and explicit upper-half-plane fixed points under the same faithful real representation.

In original basis coordinates, the five signed representatives are (−6,4,12,−5), (0,1,0,−1), (−14,5,28,−5), (−21,9,42,−10), (0,1,0,0). The signs give positive lower-left split-real matrix entries.

## Application obligations

1. **Original objects.** Required: Keep the original quaternion algebra, maximal-order lattice and real representation. Constructed: All40 predecessors are exact normalizer-r2 copies, including authoritative derivative repair2b98. New elements are literal integer vectors in that original order. Their signs are specified, not identified up to an unspecified square. Evidence: verification/SOURCE-COPIES.json; PELInertiaNormalizerData318.coefficients.

2. **Full original inertia indexing.** Required: Cover every original five-label index and its actual divisor. Constructed: The index is Fin5. label_identity consumes accepted InertiaLabels318.five_literal_divisors at the same index, giving exactly30,42,70,105,210. This matches algebraic labels, not geometric branch positions. Evidence: PELInertiaNormalizerData318.label_identity; InertiaLabels318.five_literal_divisors.

3. **Actual rational elements.** Required: A norm label alone is not an involution representative. Constructed: Five specified original-order elements have trace0, positive normd, and exact square−d in the original quaternion algebra. Each is nonzero with its actual reduced-norm inverse, giving a rational unit. Evidence: PELInertiaNormalizerData318.element_mem; element_trace; element_norm; element_square; rationalUnit.

4. **Whole order normalization.** Required: Do not extrapolate from generator checks or equal discriminants. Constructed: Each displayed integer conjugation matrix acts on every original integer vector, squares to identity, preserves addition and the full original product. actual_conjugation identifies it with n*x*n⁻¹ for every vector. The resulting original-order ring equivalence is involutive and preserves the whole order. Evidence: PELInertiaOrderInvolutions318.conjugation_product; actual_conjugation; orderInvolution; orderInvolution_value; normalizes_order.

5. **Actual quadratic carrier.** Required: A quadratic label is not an embedded imaginary field. Constructed: QuadraticAlgebra Q (−d)0 is mapped by its literal generator to the same normalizer. The generator equation and nonscalar imaginary coordinate prove a genuine injective algebra hom. Positivity ofd rules out rational roots, so the actual carrier has Field structure. Evidence: PELInertiaQuadraticEmbeddings318.realization; realization_injective; noRoot; quadraticField; original_label_generator.

6. **Real action and signs.** Required: Fixed-point construction must use the same real splitting and upper-half-plane component. Constructed: Matrix entries are evaluated from the existing faithful representation of those exact elements. Trace0 and determinantd are proved. The chosen signs give a positive lower-left entryC; no replacement conjugate representation is used. Evidence: PELInertiaRealFixedPoints318.A; Bentry; C; matrix_trace_zero; determinant_identity; lower_left_positive.

7. **Fixed-point equation.** Required: An alleged CM fixed point must satisfy the actual fractional-linear equation with a nonzero denominator. Constructed: The point is (A+i√d)/C with positive imaginary part. Its actual denominator is i√d and nonzero, and fixedPoint_equation proves the original matrix fractional-linear expression equals the point. Evidence: PELInertiaRealFixedPoints318.fixedPoint; fixedPoint_im_positive; denominator_value; denominator_ne_zero; fixedPoint_equation.

8. **Historical and downstream scope.** Required: Matching five labels and quadratic stabilizers is not an identification of the contact curve with a PEL moduli curve. Constructed: The classical canonical-model/local-reduction history and original finite inertia table are retained. This packet constructs concrete representatives and analytic fixed points, but does not identify branch positions/cross-ratios, full normalizer quotient/exhaustion, a moduli map, algebraic abelian scheme, or a contact Jacobian with the dimension2 period surface. Those remain separate joins. Evidence: verification/historical-source-pins.json; README.md.

9. **Validation.** Required: Distinguish exact independent symbolic checks from kernel or whole-proof validation. Constructed: check_inertia_normalizers.py binds literal source vectors/matrices, verifies all five labels/norms/traces/squares, full original polynomial conjugation/product/involutions, quadratic maps, and exact real fixed points/positive component. Static44 with actual baseline closure and audit controls pass. No local Lean. Evidence: verification/check_inertia_normalizers.py.

## Remaining identification

The five exact inertia-divisor labels now have actual integral quaternionic normalizer representatives, imaginary quadratic embeddings and upper-half-plane fixed points. This does not locate their images in the original contact coordinate or establish the original algebraic PEL moduli map. No normalizer quotient cardinality, ideal-lattice isogeny, polarization transport for these nonunit normalizers, or contact-Jacobian/PEL-surface identification is claimed.

## Validation

No local Lean compilation or build. Hosted strict-module recursive audit and independent acceptance are pending.
