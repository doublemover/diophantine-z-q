# Application contract: Classify all locally free affine quotients

1. **source_requirements.** Required: Whole quotient coefficient change must be Cartesian for arbitrary ideals.

Constructed: VaryingWholeIdealFamily constructs literal quotient ring arrows and pastes the actual quotient pushout square with the original source tensor coefficient square.

Justification and boundary: No cyclicity, finite/free basis, reducedness or flatness of the coefficient map is assumed for this descent producer.

2. **constructed_objects.** Required: The quotient cover must cover every point of the original entire quotient.

Constructed: The complete affine coefficient cover is pulled back through the actual whole quotient projection.

Justification and boundary: Actual Cartesian comparison isomorphisms identify those canonical pullbacks with the extended quotient schemes, giving a genuine full cover.

3. **index_coverage.** Required: Equal local ideals must imply equal original FULL ideals.

Constructed: Literal local quotient equality isomorphisms give maps over the original source. MonoLocalLift glues them on the whole quotient cover.

Justification and boundary: Spec-preimage factor rigidity yields reverse ideal inclusion; applying both directions yields equality without support/radical or faithful-flat-single-chart shortcuts.

4. **transition_maps.** Required: Arbitrary input ideal recovery and cover independence must be proved.

Constructed: Local classifying formulas and existing ideal naturality identify every local extension of the recovered ideal with the input extension.

Justification and boundary: The new full-ideal descent theorem gives exact global recovery. All-point ideal injectivity then proves choice-of-cover independence.

5. **hypothesis_checks.** Required: The represented domain must not be defined as the map range.

Constructed: LocalIdeal is a literal full ideal with Nonempty genuine affine coefficient free-cover data.

Justification and boundary: Its definition contains no parameter point or classifier. Both classification and recovery are constructed and both inverse laws are proved.

6. **consumer_identity.** Required: Naturality must use the actual original source coefficient map.

Constructed: mapIdeal is literal Ideal.map under the original sourceMap, with its local-free witness supplied by actual point base change and the proved equivalence.

Justification and boundary: Exact ideal naturality and recovery identities prove both directions commute with arbitrary R-algebra maps, including nonflat maps.

7. **normalizations.** Required: Universal-family recovery must preserve the original quotient and projection.

Constructed: The intrinsic point-family comparison is composed with exact ideal equality and inverted to identify the literal original quotient with the universal pullback.

Justification and boundary: The source embedding, coefficient projection and actual Cartesian square are proved, yielding finite/flatness. The global-free specialization recovers the old actual classifier.

8. **downstream_boundary.** Required: Separate affine representation from projective and Jacobian endpoints.

Constructed: The affine geometric locally-free quotient functor is now genuinely represented on all affine tests by the existing scheme.

Justification and boundary: Module-theoretic rank characterization, finite-type bounds, bounded projective quotient representation, Picard quotient and Jacobian identification are not established by this batch.

9. **evidence_acceptance.** Required: Fresh actual source/API/consumer review and honest validation.

Constructed: Eight complete bodies over exact742 with actual whole quotient, cover, tensor-square, full ideal rigidity and universal-family consumers.

Justification and boundary: Static/audit only locally, no Lean/profiler or cap changes. Independent source acceptance and hosted kernel/axiom checks remain distinct.

