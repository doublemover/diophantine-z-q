# Actual generic-stalk degree and rational proper completion

Status: uncompiled hosted-CI candidate. Structural validation and bounded
non-author review do not constitute kernel proof acceptance. No local Lean ran.

This packet proves density of the actual Laurent source using all original
projective chart overlaps and all scheme points. It derives integrality of the
original projective scheme, dominance and surjectivity of its exact j morphism,
and identifies the entire actual generic-stalk pullback with the compatible
fraction-field map by the original scheme square. Its degree-four theorem uses
that literal pullback scalar action, closing the earlier gap between the
explicit Laurent fraction degree and the actual projective generic degree.

The actual rational base change of the original arithmetic diamond quotient,
already identified with the parameter open, is now a proved dense open of the
original proper integral projective source. The global finite surjective j map
and its actual generic degree4 are retained, together with the inherited exact
arithmetic and compact analytic comparison squares.

Global flat rank, complete divisor data, general quotient/PEL universal-family
inputs and full318/326 arithmetic completion remain separate obligations. This
rational completion makes no claim of an everywhere-defined integral model
through3 or an extension of the old affine x chart at deleted elliptic values.

## Exact application contract

1. Actual Laurent source is dense. Required: The projective source must be identified at every scheme point, not by complex-point density or an assumed irreducibility instance. Constructed: laurent_dense takes any nonempty scheme open, pulls it back along the actual chart containing a point, and intersects with nonempty D(T) in the irreducible affine prime spectrum. Application: The original Fin2 cover supplies every point. The checked chart_mem_laurent identifies the intersection with the actual Laurent open, using both original chart overlaps. No omitted origin or nonclosed point remains.

2. Original projective source is integral. Required: Generic function fields require integrality of the actual scheme consumed downstream. Constructed: The Laurent ring is a domain. Its dense continuous image has irreducible closure equal to the original projective source. Reducedness follows from the actual polynomial affine open cover. Application: The exact scheme is therefore integral. The proof uses scheme topology and all chart sections, not transport from an analytic sphere or complex points.

3. Exact j-algebra dominance. Required: Dominance must concern the original coefficient j map, not the unrelated T scalar action on the same ring. Constructed: baseMap_injective uses the actual monic-root coefficient injection and coordinateEquiv preserving baseMap. The affine Spec map is dominant by its zero kernel. Application: The original whole-Laurent scheme square and dominant target chart imply dominance of the original global projective j map. Its actual properness upgrades this to scheme-point surjectivity.

4. Actual open generic-stalk coefficient embeddings. Required: The field identifications must be induced by the original open immersions and actual coefficient germs. Constructed: sourceAlgebra is ActualOpenFractionField318.sourceAlgebra of the original Laurent embedding. targetAlgebra uses the original finite j chart. sourceEquiv and targetEquiv are their coefficient-preserving fraction-field equivalences. Application: Both open maps are proved dominant and the schemes integral. These are the actual open generic-stalk maps, not independently selected abstract field isomorphisms.

5. Complete generic-stalk map identity. Required: Matching a j generator or degree count is insufficient to identify the whole generic pullback. Constructed: pullback is literal DominantFunctionField318.map of ThreeProjectiveJMap318.map. pullback_on_base consumes the exact original scheme square through OpenFunctionFieldSquare318.on_coefficient. Application: actual_field_square extends equality from every base polynomial to the whole actual target field by the fraction-ring universal property. It identifies sourceEquiv composed with actual pullback with the exact lifted j coefficient inclusion composed with targetEquiv.

6. Compatible fraction degree and exact scalar tower. Required: The finrank calculation must retain the exact j action on Laurent, with all tower hypotheses verified. Constructed: The local Base-algebra on Laurent is explicitly jAlgebra. FaithfulSMul is supplied by the proved baseMap injection. Canonical FractionRing.liftAlgebra and its compatible tower are used. Application: IsFractionRing.finrank_eq identifies the fraction degree with the proved finite-free Laurent rank4. This is the same scalar action appearing in the whole actual-field square.

7. Actual global generic degree four. Required: The degree theorem must be for the actual projective morphism and its actual generic-stalk pullback, not merely a compatible abstract fraction extension. Constructed: pullbackAlgebra is pullback.hom.toAlgebra on the actual source and target function fields. actual_generic_degree_four transports dimension using both field equivalences and the proved whole-map equality. Application: The same underlying projective function-field type occurs twice, but its scalar action is explicitly the nonidentity j pullback. Algebra.finrank_eq_of_equiv_equiv receives the exact commuting ring-map equation.

8. Actual rational arithmetic proper completion. Required: The algebraic model identified previously must be a dense open of the original proper projective source, with its exact j map retained. Constructed: A concrete admissible parameter evaluation proves the source open nonempty; schemeIso gives nonempty rational arithmetic target. Its actual open embedding is dense in the integral projective source. Application: actual_proper_completion combines this dense open immersion with original projective integrality/properness and the same finite surjective j map. completed_generic_degree_four records its actual degree4. The original arithmetic, compact analytic and marked-point squares remain inherited unchanged.

9. Validation and remaining completion inputs. Required: The new density and actual-degree applications require hosted kernel checking and independent source review. Constructed: Four new modules extend76 unchanged sources. Structural/hash/application checks are separate from Lean elaboration, and no Lean runs locally. Application: This candidate closes the stated actual generic-stalk identification and rational dense proper completion gaps in source. Global flat-rank, complete divisor data, general quotient/PEL universal-family inputs and full318/326 arithmetic completion remain separate. No false integral extension through3 or the old exceptional affine fibers is asserted.

