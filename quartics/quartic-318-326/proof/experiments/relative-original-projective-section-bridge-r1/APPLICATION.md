# Application contract: Connect projective quotients to actual divisors

1. **source_requirements.** Required: Use the actual original projective source and correct whole-family properties.

Constructed: The new quotient projects through the original Contact relative curve; the original curve is proper and its quotient inclusion is closed.

Justification and boundary: Composition gives global properness. Local flatness and local quasi-finiteness are tested over the complete quotient cover; proper plus locally quasi-finite gives finiteness.

2. **constructed_objects.** Required: Compare the general arbitrary-ideal quotient with the actual old section-zero model.

Constructed: OriginalSectionZeros full finite and infinity ideals and same_overlap supply Datum.

Justification and boundary: No point support, radical or substitute polynomial is used; the two local quotient schemes are exactly the old section-zero chart schemes.

3. **index_coverage.** Required: Both comparisons must cover the whole models.

Constructed: New Bool pushout cover and old Fin2 ContactGlobalResidueFlat cover are used in opposite directions.

Justification and boundary: SchemeMonoLocalLift glues every local chart map through the actual closed source embeddings. Composing with those monomorphisms proves both inverse laws.

4. **transition_maps.** Required: Retain source embedding, structural map and whole ideals under comparison.

Constructed: The comparison hom composed with old into equals new into. Kernel of iso-composition gives equality of full ideal sheaves; postcomposition gives projection equality.

Justification and boundary: The recovered zero model includes multiplicities and nilpotents. Property transfer composes with the actual isomorphism, not a fiberwise bijection.

5. **hypothesis_checks.** Required: Regularity, flatness and finiteness have distinct hypotheses.

Constructed: Generic local regular-ideal covers give Cartier charts. ResidueNonzero gives actual section regularity and flatness. Field and nonzero section give existing global finiteness.

Justification and boundary: No total-family Cartier argument is used to infer every specialization regular or flat. No local finite chart assumption is imposed over arbitrary coefficient rings.

6. **consumer_identity.** Required: Cartier output must be the actual closed kernel line.

Constructed: ActualCartierIdealLine consumes new global regular charts. Its object is definitionally ActualClosedIdealModule.object of the new original-source closed immersion.

Justification and boundary: The inclusion lands in the unchanged original structure sheaf. This is O(-D); no incorrect sign conversion or asserted O(D) identification is made.

7. **normalizations.** Required: Historical scope and mathematical normalization must remain honest.

Constructed: Prior ContactGlobalSectionZero, ContactGlobalZeroClosed, ContactGlobalResidueFlat and ContactResidueCartierCharts arguments were read and reused explicitly.

Justification and boundary: New work supplies the bridge and generic full-ideal consumer rather than claiming to discover the historical zero gluing. Original rational coefficients and arbitrary Q-algebra base are unchanged.

8. **downstream_boundary.** Required: Identify remaining projective and Jacobian gaps.

Constructed: The actual projective closed quotient, section recovery and invertible kernel are connected.

Justification and boundary: Projective moduli classification, locally free varying-rank representation, degree, dual O(D), Abel/Picard and Jacobian identification remain unproved here.

9. **evidence_acceptance.** Required: Fresh independent source/API/consumer and hosted validation.

Constructed: Six complete bodies over exact frozen702, with actual old section consumers and pinned proper/quasi-finite APIs.

Justification and boundary: Static tests do not establish Lean compilation. No local Lean/profiler, workflow changes, cap increase or inferred acceptance.

