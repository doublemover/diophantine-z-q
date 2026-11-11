# Application contract: Represented normalized source-word charts

1. **source_requirements.** Required: Normalization must be imposed on the actual source-relation parameter.

Constructed: The base ring is VaryingSourceActionParameter318.ring; relations are every entry of its universal actual word-column matrix minus identity.

Justification and boundary: Commutation alone is not substituted for original source equations.

2. **constructed_objects.** Required: The chart ring must represent the exact normalized equations on all rings.

Constructed: ring is the ideal quotient by all identity-column relations. points gives explicit forward and inverse maps.

Justification and boundary: No field-valued-point argument, reduced structure or abstract group quotient is used.

3. **index_coverage.** Required: Every word-column entry must be imposed.

Constructed: The relation index is the full pairι×ι, and Point requires equality of the whole matrix with1.

Justification and boundary: Off-diagonal entries and all coefficient nilpotents remain constrained.

4. **transition_maps.** Required: Coefficient evaluation of equations must match the same original word vectors.

Constructed: word_forward uses exact source-point naturality; evaluate_relation maps each entry and the identity matrix.

Justification and boundary: The inverse quotient map kills these very relations using the original source-point inverse identity.

5. **hypothesis_checks.** Required: Cyclicity must be discharged rather than included as a further premise.

Constructed: columns=1 yields determinant1 and IsUnit; the existing actual tensor-action cyclicity theorem is applied.

Justification and boundary: No unsupported rank or spanning premise is hidden in Point.

6. **consumer_identity.** Required: The normalized action must evaluate the literal source words to the standard basis.

Constructed: normalized uses word_evaluation at1⊗word-product, source_point identity and the same entrywise matrix equation.

Justification and boundary: The actual tensor source and marked vector are unchanged.

7. **normalizations.** Required: Eliminating frame freedom must not change the full ideal quotient.

Constructed: The normalized chart yields the same kind of actual cyclic action used by the existing full-ideal classifier and uniqueness theorem.

Justification and boundary: An ideal classification theorem for these charts is not asserted until both directions are established.

8. **downstream_boundary.** Required: An affine normalized parameter is not already a glued quotient scheme.

Constructed: The construction represents fixed-word normalized source actions.

Justification and boundary: Word-ideal inverse classifier, regular overlap maps/cocycle, gluing, family descent and Picard remain open.

9. **evidence_acceptance.** Required: New quotient/evaluation applications need exact bindings and review.

Constructed: All610 files and existing polynomial, ideal quotient, tensor and matrix sources are bound.

Justification and boundary: Static checks do not establish Lean validity. Independent review and hosted/kernel/axiom checks remain pending.

