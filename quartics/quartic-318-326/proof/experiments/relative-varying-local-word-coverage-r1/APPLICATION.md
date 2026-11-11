# Application contract: local original-source word completeness

1. **source_requirements.** Required: A cyclic genuine S⊗A action must be available; local basis extraction needs nonzero local S and a finitely presented flat target module.

Constructed: The action and marked vector are the existing constructed ones on finite free S^ι. IsLocalRing and Nontrivial are explicit in exists_word_chart.

Justification and boundary: No field assumption or abstract source generator completeness is substituted.

2. **constructed_objects.** Required: The span must consist of actual pure original-element images.

Constructed: generator a equals the literal source matrix applied to the marked vector, identified with evaluation at1⊗a by the existing tmul formula.

Justification and boundary: The proof does not select arbitrary tensor elements and call them original words.

3. **index_coverage.** Required: Cyclicity means every target vector is an image of the full tensor source.

Constructed: Surjectivity supplies a tensor preimage; tensor induction handles zero, every s⊗a and all sums.

Justification and boundary: The selected family ranges over all A; no finite generator or word cutoff is assumed.

4. **transition_maps.** Required: The extracted basis must be compared to the same fixed finite coordinate frame.

Constructed: Basis.indexEquiv compares the extracted κ-basis with standardBasis on S^ι; reindex produces an ι-basis of that identical module.

Justification and boundary: Only an index equivalence is used, not a change of source or coefficient ring.

5. **hypothesis_checks.** Required: Module.exists_basis_of_span_of_flat requires actual span-top and finite presentation/flatness.

Constructed: span_eq_top supplies its exact family; the target S^ι is finite free over S.

Justification and boundary: The theorem is invoked only under explicit local-ring hypotheses, with Nontrivial available for invariant basis number.

6. **consumer_identity.** Required: The unit determinant must be the actual existing word-chart determinant.

Constructed: The word tuple consists of the selected single-element lists; column equality identifies it with the standard-to-extracted basis-change matrix.

Justification and boundary: No unrelated invertible matrix or determinant is consumed by the chart condition.

7. **normalizations.** Required: Basis-change invertibility must hold over the whole local ring, including nilpotents.

Constructed: Basis.invertibleToMatrix provides actual inverse matrices; Matrix.isUnit_det_of_invertible yields a ring-unit determinant.

Justification and boundary: No residue-field nonvanishing conclusion is used without the local basis lift.

8. **downstream_boundary.** Required: Local chart completeness is not a global quotient classifier.

Constructed: The result gives an existential word chart for every cyclic action over nonzero local S.

Justification and boundary: Global localization cover, free-quotient reconstruction, frame normalization/gluing and Picard remain separate.

9. **evidence_acceptance.** Required: Fresh theorem applications require pinned primary APIs and exact consumers.

Constructed: The local-ring basis extraction, basis index equivalence and matrix-basis APIs are copied and bound alongside600 ordered sources.

Justification and boundary: Static checks are not Lean validity. Independent source review and hosted verification remain pending.

