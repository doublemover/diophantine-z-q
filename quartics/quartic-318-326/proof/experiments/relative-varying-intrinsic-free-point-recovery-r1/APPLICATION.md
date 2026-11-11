# Application contract: Extract intrinsic quotient ideals from actual points

1. **source_requirements.** Required: Actual R-point structure, universal finite-flat family, original ambient closed immersion and affine closed quotient theorem.

Constructed: Point records only its scheme morphism and original R-structure; family is the literal categorical pullback.

Justification and boundary: No existence of a preimage ideal or classifying frame is assumed in the point definition.

2. **constructed_objects.** Required: Recover a whole ideal of the original tensor source for every point.

Constructed: A tensor Cartesian lift constructs the original-source map, actual ambient pasting proves it closed, and Spec_iff extracts its full ideal.

Justification and boundary: Nilpotent information is retained; this is not an ideal of pointwise support or radicalized kernel.

3. **index_coverage.** Required: Coverage and hypothesis checks must be global and actual.

Constructed: The source family is the entire categorical pullback, not a chart sample. The predecessor677 recovery used its whole determinant cover.

Justification and boundary: No new local coverage assumption or implicit global word basis is introduced.

4. **transition_maps.** Required: Coefficient maps must preserve both family and original source.

Constructed: PointFamilyBaseChange constructs the actual pullback lift and proves both family/base projection identities and original tensor-source compatibility.

Justification and boundary: Pullback cancellation yields the actual source Cartesian square, then ideal extension for arbitrary coefficient maps.

5. **hypothesis_checks.** Required: Intrinsic freeness must not be assumed for all scheme points.

Constructed: FreePoint asks Nonempty Basis of the independently extracted quotient over the test ring.

Justification and boundary: This geometric quotient condition is not defined as the classifying-map range. Nonfree locally free points remain outside this interface.

6. **consumer_identity.** Required: Recovery must consume the same original free ideal and family.

Constructed: ClassifiedIdealRecovery compares the actual677 universal-family isomorphism into Spec(S tensor A), then applies full-ideal uniqueness.

Justification and boundary: recover_classify returns the literal input ideal; no unrelated framed quotient or dimension proxy is used.

7. **normalizations.** Required: Variance, quotient choice and algebra structures must be checked.

Constructed: Spec_iff quotient comparison is source-preserving; opposite ideal inclusions prove uniqueness. Tensor source and coefficient projections keep the original R/S structure.

Justification and boundary: No chosen algebra on global sections or unidentified coefficient ring is substituted.

8. **downstream_boundary.** Required: Keep the unresolved inverse and Jacobian boundary visible.

Constructed: Natural recovery on the intrinsic free locus and a proved left inverse are provided.

Justification and boundary: The right inverse is not asserted and no Equiv is declared; arbitrary-point uniqueness, locally free functor representation and Jacobian still require proof.

9. **evidence_acceptance.** Required: Fresh review and hosted validation for every new application.

Constructed: Nine new bodies over exact677 files, with pinned Spec_iff, IsPullback, tensor and whole-ideal producers in existing primary evidence.

Justification and boundary: Static checks are not Lean/kernel acceptance. No local Lean/profiler or budget/acceptance change.

