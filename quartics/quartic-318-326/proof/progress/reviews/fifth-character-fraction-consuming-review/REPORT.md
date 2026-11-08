# Bounded consuming review of the actual fifth fraction-field join

## Scope and authorship

The reviewer read all four frozen source modules, their application/dependency contract, the actual exported coordinate maps, and the stated consumer. This is a non-author review of the new localization descent and fraction-field/map identities. The reviewer authored the preceding short-model normalization and the new downstream branch/source-infinity consumers, and earlier reviewed field/order7. Those predecessors are retained, not independently reaccepted here. No Lean dependency replay was performed.

## Actual construction checked

- The generic descent composes the specified localization R→S with S→F at non-zero-divisors, then uses the localization's actual numerator/denominator representation to prove IsFractionRing R F. FaithfulSMul R F is explicit and supplies the needed injectivity; a bare field-degree equality is not used.
- The quartic localization is the already checked actual Laurent tensor, with the image of t proved a unit in the specified fifth character field. quarticEmbedding extends the original whole quartic embedding exactly, and the induced Algebra/IsScalarTower instances have the right maps.
- cubicEmbedding is quarticEmbedding after the inverse of the actual localized reciprocal equivalence. The direction is correct: reciprocal v goes to t⁻² times the original quartic root. Its entire cubic-order embedding is the actual tensor inclusion, and injectivity uses the proved Laurent base injection/free quadratic presentation, not an unproved normal-model identification.
- Descent establishes the whole reciprocal order's fraction field, not an isomorphism of the two entire affine orders. In particular, the missing t=0 branch is not silently covered by the localized reciprocal map.
- The parameter identities use the actual T(1), T(-1), T(-2) coordinates, the explicit inverse maps, and the original full-support root. The scalar and root maps are both retained; there is no change to an arbitrary quadratic subfield.
- FifthShortFraction318 uses the inverse of the exact short affine coordinate equivalence to place the literal short ring in the same original fifth field. Its actual fraction-field theorem and original x/y formulas keep xScale, shift and yScale, including their signs. The consumer is exactly that specified embedding, not an abstract genus-one isomorphism class.
- The application boundary is accurate: these four sources alone do not extend a rational map to a completion. The subsequent branch and source-infinity packets construct such regular maps independently and consume these exact identities.

## Result

No discrepancy found in this bounded source/application read. All exact artifact and predecessor bindings in checks.json pass. The exact four-source application is accepted within the stated predecessor-relative scope. This decision does not approve a hypothetical future revision or a whole global quotient/Jacobian/PEL claim. The source-infinity consumer hashes are bound as the exact application inspected, not independently reaccepted because the reviewer authored that consumer.

## Required-versus-constructed obligations

1. **Hypotheses:** the existing quartic fraction field and the two exact principal localizations are present; the whole-order descent does not assume an unsupported completion theorem.
2. **Objects:** all four modules retain the literal full-support fifth intermediate field, original quartic order, actual Laurent scalar extensions, entire reciprocal cubic order and literal short ring.
3. **Coverage:** localization is only D(t)/D(u); whole fraction-field coverage is supplied by the explicit composition-of-localizations theorem. It is not used as whole-affine coverage.
4. **Maps:** the original quartic embedding extends through localization; the inverse tensor equivalence transports in the correct reciprocal-to-quartic direction; the final short embedding uses coordinateEquiv.symm.
5. **Coefficients:** each Algebra instance is induced by the stated map, and each scalar tower is tied to an explicit on-order identity. The rational coefficient changes in x/y retain their actual scales and shifts.
6. **Identities:** the checked root, parameter and inverse-parameter formulas identify the same original full-root object used by the source-infinity consumer, including its actual intermediate-field inclusion.
7. **Local/global distinction:** the entire fraction-field conclusion follows by descent with injectivity; regularity at the omitted branch and source infinity is constructed in separate packets.
8. **Evidence:** all exact source/artifact/predecessor bindings pass; the reviewer read proof bodies and the application instead of inferring acceptance from the audit. No replay or broad transitive review is claimed.
9. **Boundary:** original field identity is accepted; completed quotient, finite-flat rank, differential norm/Jacobian, polarization/PEL and final arithmetic remain outside this record. Existing dated approvals remain unchanged.
