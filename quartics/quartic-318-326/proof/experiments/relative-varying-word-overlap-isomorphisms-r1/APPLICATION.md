# Application contract: Prove regular word-overlap inverses

1. **source_requirements.** Required: Conjugating a cyclic frame must change actual action and vector by the same inverse word matrix.

Constructed: action_matrix and marked_vector compute precisely the existing normalize definition.

Justification and boundary: The action is evaluated on the standard basis and converted using the pinned toMatrix/mulVec APIs; no new replacement frame is postulated.

2. **constructed_objects.** Required: Coefficient transport of inversion must hold on the exact invertibility locus.

Constructed: inverse_map maps the left inverse identity and uses the resulting unit determinant and right inverse identity.

Justification and boundary: Valid for arbitrary ring homomorphisms, including noninjective maps and nilpotents; no division by arbitrary nonzero values.

3. **index_coverage.** Required: Every original source element and coefficient algebra must be included.

Constructed: transition_matrix holds for all a:A; transition_natural for every S→T algebra homomorphism.

Justification and boundary: The original scalar-extension inverse evaluates at 1 tensor a, and frame_columns identifies the original word matrix. All source relations are retained.

4. **transition_maps.** Required: Objectwise inverse points alone do not imply inverse regular maps.

Constructed: transitionRing_evaluate proves compatibility of the actual universal ring map with every test AlgHom.

Justification and boundary: Uses coefficient naturality and universal point identity, then pointsOnOpen injectivity to prove both actual ring-map composites equal id.

5. **hypothesis_checks.** Required: Overlap isomorphism must use the same principal open rings and their maps.

Constructed: ringEquiv and overlapIso use the existing transitionRing and Spec transition without replacement.

Justification and boundary: Both inverse equalities are transferred contravariantly using Spec.map_comp/map_id and CommRingCat hom extensionality.

6. **consumer_identity.** Required: The consumer must be the previously constructed universal regular transition.

Constructed: transitionRing_inverse checks that exact map; overlapIso hom is exactly the old transition definition.

Justification and boundary: There is no set-level surrogate or field-point-only assertion. The base-preserving property from the previous packet continues to apply.

7. **normalizations.** Required: Matrix orientation and basis order must agree.

Constructed: W consists of selected word evaluation columns; normalize acts by W inverse.

Justification and boundary: The formula is W inverse*M*W and inverse*marked, while the contravariant ring direction is H_vw→H_wv.

8. **downstream_boundary.** Required: Do not claim a scheme gluing datum before triple compatibility.

Constructed: This packet establishes pairwise regular isomorphisms only.

Justification and boundary: Triple-overlap restrictions, cyclic cocycle, actual glued scheme and global family/classifier remain explicit next work.

9. **evidence_acceptance.** Required: Review source changes and keep hosted scope distinct.

Constructed: Exact619 predecessor modules plus three new sources with all bindings refreshed.

Justification and boundary: No local Lean or profiler. Independent source review and hosted kernel/axiom validation remain separate and pending.

