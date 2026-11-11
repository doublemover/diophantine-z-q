# Application contract: Identify coefficient-family pullback squares

1. **source_requirements.** Required: Coefficient-family base change requires a Cartesian ambient source square.

Constructed: tensor_cartesian identifies Spec(S tensor_R A) with the actual Spec S/Spec A pullback.

Justification and boundary: Both projection equations are taken from the pinned pullbackSpecIso, including the actual tensor includeRight map.

2. **constructed_objects.** Required: Construct the original coefficient-change map rather than an abstract comparison.

Constructed: sourceChange is Spec of Algebra.TensorProduct.map f id_A; coefficientChange is Spec f.

Justification and boundary: source_original, source_projection and coefficient_base compute its exact three compatibilities.

3. **index_coverage.** Required: Retain arbitrary base rings and coefficient homomorphisms.

Constructed: All commutative R-algebras S,T and every f:S→T.

Justification and boundary: No flatness, surjectivity, injectivity, reducedness or field restriction. Actual nonreduced schemes remain.

4. **transition_maps.** Required: Pasting cancellation must have the correct horizontal and vertical directions.

Constructed: IsPullback.of_right cancels the old source tensor pullback from the full new one.

Justification and boundary: The family closed-quotient pullback is then flipped and pasted vertically with this exact ambient coefficient square.

5. **hypothesis_checks.** Required: The pasted projection must equal the real finite-flat family projection.

Constructed: into_projection proves intoSource followed by ambient coefficient projection equals the literal quotient algebraMap projection.

Justification and boundary: Uses the same scalar tower S→S tensor_R A→quotient, not a guessed map or related finite module.

6. **consumer_identity.** Required: The consumer must be the original quotientMap/family.

Constructed: cartesian uses the prior actual quotientMap and CyclicQuotientFiniteFlat.projection for d and mapPoint f d.

Justification and boundary: comparison is its actual categorical pullback isomorphism; comparison_projection checks the genuine projection.

7. **normalizations.** Required: Preserve Spec contravariance and tensor order.

Constructed: Tensor order is S tensor_R A, with coefficients on the left and id_A on the right.

Justification and boundary: The geometric family map goes from the T-family to the S-family; the base map goes from Spec T to Spec S.

8. **downstream_boundary.** Required: Local Cartesian compatibility is not yet global family descent.

Constructed: Coefficient-base pullback compatibility is now explicit.

Justification and boundary: Global family gluing over the word-chart scheme and the correct-image global quotient classifier remain open.

9. **evidence_acceptance.** Required: Keep review and kernel scope separate.

Constructed: Exact635 predecessor sources plus two new source bodies with current hashes.

Justification and boundary: Static bindings/audit and independent source/API review are separate from hosted Lean/axiom acceptance. No local Lean/profiler.

