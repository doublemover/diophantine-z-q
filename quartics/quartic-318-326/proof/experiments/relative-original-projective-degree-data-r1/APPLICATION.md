# Application contract: Construct actual bounded divisor degree data

1. **source_requirements.** Required: Finite presentation must follow from actual equations over the entire target.

Constructed: RegularClosedFinitePresentation uses every original regular quotient chart and builds a complete open cover indexed by target points.

Justification and boundary: Each principal ideal has an explicit singleton finite generating set; literal quotient Spec maps are finitely presented, and actual pullback comparison transfers this property to the canonical local maps.

2. **constructed_objects.** Required: Global function algebra must be the same WHOLE family.

Constructed: FiniteAffineAlgebra uses canonical Z.isoSpec and the actual Spec preimage of its inverse followed by the original projection.

Justification and boundary: The iso_projection equation preserves the original coefficient map. No individual finite/infinity chart restriction is substituted.

3. **index_coverage.** Required: Finite flatness is insufficient by itself over arbitrary rings.

Constructed: The original finite morphism supplies a finite algebra; actual finite presentation supplies finite algebra presentation; their combination supplies finite module presentation.

Justification and boundary: Only then is the prior flat finitely-presented projectivity theorem applied. No Noetherian or globally free hypothesis is added.

4. **transition_maps.** Required: The finite free control must be an actual retract, not an invented basis.

Constructed: The same whole function module has actual surjection from and injection into a finite free module, with composition its identity.

Justification and boundary: This follows from finite projectivity. It does not assert global freeness or force a constant rank over disconnected bases.

5. **hypothesis_checks.** Required: Degree must cover every coefficient prime and exceptional base.

Constructed: Degree is the actual rankAtStalk of the whole function module; finite presentation and flatness make it locally constant.

Justification and boundary: Compactness of the full coefficient spectrum makes its range finite. Taking the supremum of its finite range bounds every prime, including vacuously the zero ring case.

6. **consumer_identity.** Required: Local free neighborhoods must be genuine and sufficient.

Constructed: At every coefficient prime, finite flatness gives a free local stalk; the pinned finite-presentation localization theorem extends this to a principal neighborhood.

Justification and boundary: The localized module is the actual whole function module, not the arbitrary source-chart open quotient. No uniform free basis is silently chosen.

7. **normalizations.** Required: Consume these inputs on the original projective quotient.

Constructed: Actual Cartier closed-map finite presentation composes with the original smooth ambient projection.

Justification and boundary: The original finite-flat whole family then receives finite projectivity and actual bounded rank. EffectiveDatum and degree subtypes retain precisely these original source and projection conditions.

8. **downstream_boundary.** Required: Keep representation and arithmetic boundaries explicit.

Constructed: True bounded degree and local free function-module inputs are now constructed for effective original projective data.

Justification and boundary: No finite-type representing quotient atlas, represented Picard scheme, Jacobian identification, degree formula or Arakelov identity is inferred.

9. **evidence_acceptance.** Required: Fresh independent source/API/consumer validation.

Constructed: Six new bodies over exact724r2, actual canonical affine/Cartier producers and pinned finite-presentation, projectivity, localization and rank APIs.

Justification and boundary: Static/audit only locally; no Lean/profiler or budget change. Source acceptance and hosted kernel acceptance remain separate.

