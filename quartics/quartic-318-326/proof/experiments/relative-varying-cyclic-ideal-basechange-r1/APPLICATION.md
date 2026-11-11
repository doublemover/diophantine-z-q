# Application contract: Transport the full cyclic quotient under coefficients

1. **source_requirements.** Required: Before choosing a local word chart, quotient ideals must extend under arbitrary coefficient maps.

Constructed: ideal_map is proved for every Cyclic R A iota S and every R-algebra map S to T.

Justification and boundary: Neither source nor target has a global word basis hypothesis; coefficient map flatness or surjectivity is not assumed.

2. **constructed_objects.** Required: Construct a real evaluation section from existing data.

Constructed: preimage chooses source tensors mapping to every standard basis vector using the original cyclicity proof.

Justification and boundary: sectionMap is the standard basis linear extension; evaluation_section proves it is a right inverse.

3. **index_coverage.** Required: All coefficient rings and basis indices must be covered.

Constructed: Every finite index iota, arbitrary coefficient ring T and arbitrary R-algebra map f.

Justification and boundary: mappedSection uses the images of every selected basis preimage; basis_image verifies coefficient transport of every standard basis vector, including empty-index cases.

4. **transition_maps.** Required: The mapped action and all source maps must be the actual earlier constructions.

Constructed: Uses the literal matrix coefficient mapAction, linearAction, sourceMap=tensor map f id, and existing evaluation_map.

Justification and boundary: The evaluation section identity proves actual coefficient cyclicity; no surrogate action or changed algebra is introduced.

5. **hypothesis_checks.** Required: A kernel map identity needs full ideal generation, not only inclusion or pointwise zero sets.

Constructed: VaryingSplitIdealGenerators proves the full evaluation ideal equals the span of all original source-element defects for any genuine section.

Justification and boundary: Tensor induction handles every source element; section/evaluation identity proves both ideal inclusions with no reducedness.

6. **consumer_identity.** Required: The intrinsic ideal must be the one consumed by original free quotients and normalized charts.

Constructed: ideal_map compares CyclicQuotientEvaluation318.ideal for the original and coefficient-changed actual source actions.

Justification and boundary: Mapped chosen sections are natural on every vector, so the actual generator sets correspond under sourceMap and Ideal.map_span gives exact equality.

7. **normalizations.** Required: Preserve original scalar actions and scheme-theoretic multiplicities.

Constructed: All652 predecessor sources exact, including actual global original-source quotient and local normalized theorem.

Justification and boundary: source_smul explicitly uses the same tensor coefficient map on scalar multiplication; no radicalization or field reduction is used.

8. **downstream_boundary.** Required: This bridge is not itself the global quotient classifier.

Constructed: All-ring cyclicity and exact full-ideal base change are supplied before local word normalization.

Justification and boundary: Next work constructs normalized maps on the determinant cover, their compatibility and global correct-scope classification. No Picard/Jacobian conclusion.

9. **evidence_acceptance.** Required: Review the changed generalization and exact applications freshly.

Constructed: Three full new source bodies and exact652r2 predecessor, existing pinned linear-basis/tensor/ideal APIs and static checks.

Justification and boundary: Independent bounded source/application review and hosted Lean/kernel acceptance remain separate; no local build or profiler.

