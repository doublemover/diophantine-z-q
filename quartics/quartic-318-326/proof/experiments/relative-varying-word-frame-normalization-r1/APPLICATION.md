# Application contract: Canonical word-frame normalization

1. **source_requirements.** Required: The starting data must be cyclic and frame changes invertible.

Constructed: changeFrame uses LinearEquiv.conjAlgEquiv and transports cyclicity through the exact intertwiner.

Justification and boundary: No arbitrary matrix is declared invertible or cyclic.

2. **constructed_objects.** Required: The normalizing matrix must be the actual source evaluation columns.

Constructed: columns i j evaluates the unchanged action/vector at the supplied source element w j. columnEquiv uses its actual nonsingular inverse.

Justification and boundary: The determinant-unit hypothesis is on that identical matrix.

3. **index_coverage.** Required: Normalization must fix every chosen source column and act on the full module.

Constructed: columnEquiv_basis identifies all Pi.single basis vectors with those exact evaluations. normalize_is_normalized handles every index.

Justification and boundary: No subset of basis vectors or rank comparison is used.

4. **transition_maps.** Required: Frame transport must preserve actual source multiplication and marked vector.

Constructed: intertwines and evaluation_change explicitly identify the conjugated action, and ideal_change applies the full cyclic ideal comparison.

Justification and boundary: The change is made by one invertible linear equivalence, not a fibrewise identification.

5. **hypothesis_checks.** Required: Matrix.toLin'OfInv requires both left and right inverse identities.

Constructed: Both Matrix.nonsing_inv_mul and mul_nonsing_inv are supplied with the same unit determinant.

Justification and boundary: No determinant nonzero/unit conflation or field assumption occurs.

6. **consumer_identity.** Required: Normalized coordinates must represent the same original ideal quotient.

Constructed: normalize_ideal is exact equality in the FreeIdeal subtype; normalization does not alter the source ideal.

Justification and boundary: Equality is scheme-theoretic, not radical equality.

7. **normalizations.** Required: There must be no residual frame ambiguity after normalization.

Constructed: The canonical equal-ideal intertwiner fixes each standard vector, then Basis.ext proves it is identity.

Justification and boundary: Its all-source intertwining and marked-vector law force equality of the full framed records.

8. **downstream_boundary.** Required: Frame-independent coordinates alone do not construct a scheme quotient.

Constructed: normalize_eq identifies normalized representatives of the same ideal orbit.

Justification and boundary: Represented normalized charts, regular overlap maps/cocycles, scheme gluing and Picard remain open.

9. **evidence_acceptance.** Required: Every changed theorem application needs exact source evidence.

Constructed: Pinned matrix inverse, ToLin, conjugation and quotient APIs are retained;608 ordered sources are hashed.

Justification and boundary: Static checks do not establish Lean validity; fresh independent review and hosted/kernel checks remain pending.

