# Application contract: Identify actual quotient-family pullbacks

1. **source_requirements.** Required: A quotient base-change square requires the exact image ideal.

Constructed: Generic f:B→C, ideals I,J and h:Ideal.map f I=J.

Justification and boundary: The universal quotient map is built from map_le_iff_le_comap; its action on every original source element is unchanged.

2. **constructed_objects.** Required: Construct an actual categorical pushout rather than a point bijection.

Constructed: For any PushoutCocone, descend is the actual Ideal.Quotient.lift of its C-leg.

Justification and boundary: The cocone square kills images of I, hence the whole extended ideal J; quotient surjectivity proves both factorization and uniqueness.

3. **index_coverage.** Required: Allow all original elements and coefficient maps.

Constructed: Generic arbitrary commutative rings, then every R-algebra map S→T and normalized source point d.

Justification and boundary: No injectivity, surjectivity, flatness, field or reducedness requirement is imposed.

4. **transition_maps.** Required: The geometric square must have the correct contravariant directions.

Constructed: Spec of quotient targetMap and induced arrow form the two pullback projections.

Justification and boundary: isPullback_SpecMap_of_isPushout transfers the exact proved ring square; comparison_fst/snd retain both original maps.

5. **hypothesis_checks.** Required: The normalized-family application must supply h for its exact source map.

Constructed: ideal_map applies to Algebra.TensorProduct.map f id_A and the actual framed annihilator ideals.

Justification and boundary: There is no replacement ideal or quotient; quotientMap_mk explicitly computes every original tensor element image.

6. **consumer_identity.** Required: The consumer must be the original finite-flat quotient family.

Constructed: cartesian uses CyclicQuotientFiniteFlat.scheme/into for d and mapPoint f d.

Justification and boundary: The output comparison is the actual categorical pullback isomorphism of these literal family/source maps.

7. **normalizations.** Required: Preserve coefficient and source conventions.

Constructed: Only coefficient entries change; the A factor is mapped by id.

Justification and boundary: Scheme direction is from the T-family to the S-family, and the ambient source map is the same original tensor coefficient map.

8. **downstream_boundary.** Required: Do not infer global descent or coefficient-base pullback without further comparison.

Constructed: Actual pullback along the ambient-source coefficient morphism is established.

Justification and boundary: Ambient-source coefficient-base comparison, global family gluing and globally-free-image classifier remain explicit next steps.

9. **evidence_acceptance.** Required: Keep immutable repairs and source/kernel acceptance distinct.

Constructed: Exact633r2 sources including both exact240 elaboration repairs, plus two new modules.

Justification and boundary: Static bindings/audit, independent source/API review and hosted kernel/axiom validation remain separate. No local Lean/profiler.

