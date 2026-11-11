# Application contract: global framed-action word coverage

1. **source_requirements.** Required: Full cyclicity of the actual S⊗A action must survive the residue-field coefficient map.

Constructed: evaluation_map proves exact tensor evaluation transport for every coefficient homomorphism. cyclic_of_surjective additionally requires and uses its surjectivity.

Justification and boundary: No arbitrary base-change flatness or unsupported fibrewise inference is assumed.

2. **constructed_objects.** Required: The transported matrices and marked vector must be the images of the same original source action.

Constructed: mapAction is action(mapPoint(point a)); matrix and marked-coordinate formulas are definitional.

Justification and boundary: The action classifier inverse supplies the exact source-point identity used for determinant naturality.

3. **index_coverage.** Required: Cyclicity must cover every target vector and all original tensor elements.

Constructed: Each target coordinate is lifted through the surjective coefficient map. Tensor induction checks zero, all s⊗a and addition for evaluation transport.

Justification and boundary: No finite generating subset, rank-only condition or reduced test restriction replaces these inputs.

4. **transition_maps.** Required: Determinant coefficients must transform under the same map as the action.

Constructed: The exact word determinant naturality theorem is applied after the actionPoints inverse identity.

Justification and boundary: The maximal quotient map is Ideal.Quotient.mkₐ R m and tensor map is map f (AlgHom.id R A).

5. **hypothesis_checks.** Required: The local completeness theorem requires a nonzero local coefficient ring.

Constructed: Ideal.exists_le_maximal is used only under an explicit proper-ideal contradiction. Ideal.Quotient.field m supplies the actual nonzero residue field with its local-ring instance.

Justification and boundary: The same quotient map is surjective by mk_surjective, so all local inputs are constructed.

6. **consumer_identity.** Required: The determinant ideal and covering opens must use exactly the existing word charts.

Constructed: The ideal is span(range(determinant(point a).val)), and the final basic opens use that identical function on all tuples ι→List A.

Justification and boundary: The local witness word w is substituted into this same original range before mapping to the residue field.

7. **normalizations.** Required: A fibre argument must not discard nilpotents or claim a reduced classifier.

Constructed: Residue fields are used solely to contradict properness of an ideal in the original S. The conclusion is the unit ideal in S and a cover of Spec S itself.

Justification and boundary: All source equations, full-ring point equivalences and universal quotient families remain exact predecessor bytes.

8. **downstream_boundary.** Required: A cover of framed cyclic actions is not the quotient by frame change.

Constructed: basic_open_cover covers every coefficient spectrum for an actual cyclic action.

Justification and boundary: Normalization to a chosen word basis, frame overlap/cocycle, gluing and Picard remain unproved here.

9. **evidence_acceptance.** Required: New coefficient and maximal-ideal applications need exact primary sources and fresh review.

Constructed: Pinned tensor maps, maximal ideal existence, quotient field and prime-spectrum cover APIs are bound with602 ordered sources.

Justification and boundary: Static checks do not prove Lean validity. Independent review and hosted/kernel/axiom checks remain pending.

