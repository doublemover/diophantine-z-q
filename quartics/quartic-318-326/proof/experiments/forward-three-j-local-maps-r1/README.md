# Actual localization maps and whole affine j morphisms

Status: uncompiled inactive hosted-CI candidate. No local Lean build or proof
acceptance is claimed. The preceding submitted analytic packets are unchanged.

This packet constructs actual scheme maps on numerator and denominator principal
opens, proves their equality on the actual categorical intersection, and glues
them into a morphism from each entire rational affine source chart. It then
specializes the generic construction to the original level-three j polynomials.
These are genuine scheme morphisms, not functions only on complex-valued points.

The common ring is an iterated localization representing D(f) intersect D(g);
it is not silently identified by notation with Localization.Away(f*g).

## Exact application contract

1. Exact source localizations. Required: Actual source rings and maps for numerator and denominator domains, retaining the Q coefficient map. Constructed: NumeratorRing=Q[T][1/f], DenominatorRing=Q[T][1/g], and Common is the latter localized at the image of f; numeratorBase and denominatorBase are actual Spec maps of their algebra maps. Application: These are the original principal-open inclusions in Spec Q[T]. No field-of-fractions replacement or set of complex points is used. The f and g variables are arbitrary rational polynomials until coprimality is required for coverage.

2. Localization universal-property comparison. Required: A genuine morphism from the common localization to the numerator chart, with exact common base map. Constructed: toNumerator is liftAlgHom from Q[T][1/f] to Common; numeratorInclusion is its contravariant Spec map, while denominatorInclusion is the second localization inclusion. Application: The image of f is a unit in Common by its defining localization. toNumerator_on_base proves its exact base-ring action. base_square equates the two Spec composites by ring-hom extensionality, preserving the contravariant direction.

3. Actual common intersection. Required: Compatibility must hold on the categorical pullback, not an assumed overlap ring. Constructed: actual_pullback identifies Common with the pullback of numeratorBase and denominatorBase. Application: The common denominator inclusion is an open immersion. The numerator chart range is D(f), whose preimage in the denominator localization is exactly the basic open used to define Common. IsOpenImmersion.isPullback receives both the proved base square and this exact opens-range equality.

4. Exact inverse coordinate pair. Required: The finite and reciprocal target coordinates must multiply to one on the full common localization. Constructed: x,y are the two polynomial images; ix,iy are their actual localization inverses. x_ix, y_iy and toNumerator_inv identify the exact inverse images. Application: forward=x*iy and inverse=y*ix satisfy forward*inverse=1 by commutativity and the actual localization identities. No domain, cancellation or nonzero argument is needed. This produces a genuine unit, including over non-field localizations.

5. Actual target maps and scalar preservation. Required: Each domain needs a morphism to the same original projective scheme, not merely a rational function. Constructed: numeratorMap evaluates g/f into JLineAtlas318.chart Q 0; denominatorMap evaluates f/g into chart Q 1. Application: Both use literal polynomial evaluation followed by the original algebraic chart. The evaluation_over_Q lemma checks their exact composite with ProjectiveJLine318.structureMap; global over_Q is later proved by the covering hom-ext theorem.

6. Overlap equality of scheme morphisms. Required: The two actual local maps must agree on the entire common localization. Constructed: projection_compatibility computes the composites of the actual evaluation ring maps with toNumerator and the common algebra map. Application: Polynomial.ringHom_ext checks constants and the coordinate. The resulting two maps are related by the exact unit forward with inverse inverse; JLineOverlap318.unit_chart_overlap applies to that unit and the same original target chart maps. The equality is of scheme morphisms, not equality on points.

7. Coverage and all gluing pairs. Required: The chosen local maps must cover all source points and agree for every ordered pair of cover indices. Constructed: cover is an actual Bool-indexed Scheme.OpenCover of Spec Q[T], supplied by IsCoprime f g and exact localization ranges. compatible handles four ordered pairs. Application: The two mixed cases use the proved actual pullback and its flip, transferred to Mathlib canonical pullbacks via isoPullback. Both diagonal cases use monomorphism cancellation. Thus no missing index, diagonal or reverse compatibility is left to inference.

8. Whole affine morphisms and original j pairs. Required: The glued result must be a map on each entire original affine source chart with exact local restrictions and rational scalar map. Constructed: RationalPairGluing318.map uses cover.glueMorphisms; numerator_restriction and denominator_restriction identify its original local maps. ThreeAffineJMaps318 specializes this to both actual degree-four j coordinate pairs. Application: The two rational Bezout certificates discharge the complete source coverage assumptions. The four concrete restriction identities bind the resulting maps to the exact numerator/denominator charts. Both finite_over_Q and reciprocal_over_Q retain the original coefficient map. The source infinity/zero points lie in these full affine charts, not a deleted dense locus.

9. Verification, prior evidence and remaining global overlap. Required: New applications require hosted kernel checking and distinct review; affine gluing must not be described as the completed projective map. Constructed: Six unchanged predecessor modules and three new local-map/gluing modules are hashed and ordered for a separate inactive CI candidate. Application: No local Lean run, kernel pass or independent proof acceptance is claimed. The two entire affine maps have been constructed in source code; their mutual agreement on the original projective source overlap and final gluing on ProjectiveJLine318.scheme Q remain to be proved. The characteristic-three obstruction remains explicit; no integral Z-model, degree theorem, PEL realization or final arithmetic theorem is asserted.

## Remaining projective-source gluing

The remaining step is to prove that finiteMap and reciprocalMap agree after
restriction along the actual original projective-line overlap maps. The scalar
identity chart_pair_overlap retains their common T^4 factor under TS=1, but that
identity still needs to be consumed through the exact localization/scheme maps.
Only after this agreement is proved can the two whole affine maps be glued on
the actual projective source. The packet does not claim that final map exists.

Afterward, bind the final scheme morphism to the original compact analytic
comparison and the two cusp values, without silently replacing the arithmetic
source, extending the same model through characteristic 3, or claiming PEL
realization. Hosted elaboration and recursive axiom checking remain mandatory.
