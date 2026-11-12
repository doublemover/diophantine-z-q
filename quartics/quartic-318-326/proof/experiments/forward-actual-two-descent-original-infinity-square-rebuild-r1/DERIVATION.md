# Fresh original infinity field compatibility

## 1. Entire original generic carrier

Required: Coefficients must live in the actual original scheme function field, not an unrelated rational model.

Constructed and justification: coefficient j is the inverse native open-immersion generic-stalk isomorphism applied to the native Spec coefficient. Its fraction_comparison and stalk_square fix all coefficients.

## 2. Native transition direction

Required: Affine refinement Spec(S) to Spec(R) is contravariant on coordinates.

Constructed and justification: Borrowed DominantFunctionField.map_comp and AffineFunctionFieldMap.on_coefficient give the whole generic square, after actual dense open immersions supply dominance.

## 3. Complete overlap

Required: The comparison must use the whole original D(y)=D(v) overlap.

Constructed and justification: commonChart is the literal intoInfinity followed by infinityChart. pushout.condition and actual_into_affine give both exact scheme-factor squares.

## 4. Original constants and x

Required: Constants and x must agree with the old named affine generic functions.

Constructed and justification: All affine and infinity coefficients pass through overlapCoefficientMap. The actual quotient map sends x to u/v and constants to the same constant; v times its inverse is the actual localization identity.

## 5. Every root parameter

Required: The root formula must hold for every a, not just test points or the three roots.

Constructed and justification: root_square proves named root(n,a)*native(v)=native(u-a*v) for all K-valued a, by the exact same generic maps.

## 6. Denominator nonzero

Required: Division by native v must be justified.

Constructed and justification: The native chart coefficient is injective by its exact affine fraction comparison. Existing original chart_v_nonzero then gives v_nonzero, without n nonzero.

## 7. Actual marked infinity stalk

Required: The local field comparison must extend the canonical original stalk equivalence.

Constructed and justification: comparison extends infinityEquiv through native fraction-ring structures, on_stalk retains its algebraMap square, and on_chart follows the newly rebuilt exact germ/coefficient square.

## 8. Pole and unit normalization

Required: The named original function must consume the old actual local unit calculation.

Constructed and justification: named_root identifies the original generic root with infinityAffineX minus the old local constant. normalization then retains the exact e,d units, u cube for v, and nonzero d/e multiplying the double pole.

## 9. Historical and verification boundary

Required: Fresh source must not inherit lost approval or imply global divisor/theta results.

Constructed and justification: All 1312 predecessor sources are unchanged, including the separately reviewed ThreePole repair. Two borrowed baseline modules are credited byte-exact. Six fresh modules require independent review and hosted kernel replay. All-point support, associated sheaf, translations and theta/Weil identification are not concluded.
