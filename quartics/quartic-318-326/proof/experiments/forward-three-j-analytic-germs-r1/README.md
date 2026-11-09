# Exact j action: analytic charts and cusp orders

Status: uncompiled inactive hosted-CI candidate. Non-author source review and
hosted Lean checking remain pending. No local Lean build was run.

The two new modules construct analytic local representatives for the exact
scheme-induced j action in the original two source and target evaluation
charts. Coverage is exhaustive on every source chart and every actual complex
scheme point. At the finite and reciprocal source origins, respectively,
the reciprocal target coordinates have analytic zero orders3 and1. Exact
neighborhood identities tie these scalar germs to the actual scheme map.

This is an exhaustive chart-local holomorphy certificate, not yet a bundled
ContMDiff theorem. The existing compact parameter comparison identifies the
origins with zeroEnd and infinityEnd; explicit q-disc composition formulas
and a full ramification divisor remain separate. The elliptic-value1728
factorization is retained as an exact algebraic identity without claiming
those further conclusions.

## Exact application contract

1. Exact same scheme-point action. Required: The local expressions must belong to the previously constructed actual rational projective j morphism. Constructed: All formulas have mapPoints(chartPoint i z) on their left, with mapPoints defined by literal composition of scheme maps. Application: The54 predecessor modules are unchanged, preserving global scheme gluing, the compact source comparison and every original/cusp value law.

2. Exact finite-source reciprocal expression. Required: Near the finite source origin, the target must use its actual reciprocal chart. Constructed: finite_numerator_formula identifies the map with chartPoint 0 (t^3/((t+27)*(t+243)^3)) when the numerator is nonzero. Application: It consumes the same global finite_restriction and numerator localization factorization, with explicit inverse of the exact numerator evaluation. The target coordinate is not a totalized finite quotient.

3. Exact reciprocal-source expressions. Required: Both target chart choices must be available from the reciprocal source chart. Constructed: reciprocal_numerator_formula gives s/((1+27*s)*(1+243*s)^3) in target chart0, and reciprocal_denominator_formula gives its inverse expression in chart1 when s is nonzero. Application: Each proof applies the exact reciprocal_restriction and the matching actual localization evaluation theorem; coefficient maps and original chart indices are retained.

4. Whole-neighborhood analytic meaning. Required: An expression at one point is insufficient: it must equal the scheme map on a whole neighborhood and be analytic at the center. Constructed: HasAnalyticChartExpression records an original target index, a scalar analytic germ, and an eventual equality of actual scheme-valued points on the source coordinate neighborhood. Application: Analyticity of both polynomial numerators and continuity give eventual numerator nonvanishing at each source origin. At nonzero source coordinates, eventual nonvanishing supplies the denominator expression.

5. All source coordinates and all genuine points. Required: Coverage must include both original chart indices and all their coordinates, including numerator zeroes and the two origins. Constructed: finite_chart_analytic and reciprocal_chart_analytic split only on coordinate zero; all_chart_analytic checks both Fin2 indices; every_point_analytic uses every_point_in_chart. Application: No generic-locus restriction survives: numerator zeroes use a nonzero denominator, and source origins use a nonzero numerator. The actual scheme-point factorization theorem supplies genuine point coverage.

6. Orders of the exact analytic cusp germs. Required: The reciprocal-target local expressions must have their actual zero orders, with no hidden pole or totalization artifact. Constructed: finite_cusp_germ gives analytic finitePole with value0 and meromorphic order3; reciprocal_cusp_germ gives analytic reciprocalPole with value0 and order1. Application: The identity function has order1 by its zero value and nonzero derivative. Numerator factors have order0 because their values are3^18 and1. The precise meromorphic division and power theorems then give orders3 and1; analyticity is separately established.

7. Bind local orders to actual map and compact cusp labels. Required: The order calculations must describe the same scheme action and the same compactification cusp coordinates. Constructed: exact_cusp_germs packages both neighborhood equality formulas with the analytic order statements. The unchanged compact point comparison sends zeroEnd to finite origin and infinityEnd to reciprocal origin. Application: Therefore order3 belongs to the finite source origin corresponding to zeroEnd, and order1 to the reciprocal source origin corresponding to infinityEnd. No equality of unrelated rational functions is used; the existing compact parameter biholomorphism supplies the source chart identification.

8. Explicit finite elliptic-value algebra. Required: Any branch-polynomial factorization must retain its exact normalization and cannot be treated as a full divisor computation. Constructed: numerator_minus_1728 proves finiteN(t)-1728*t^3=(t^2-486*t-19683)^2 over C by ring normalization. Application: This records the exact classical elliptic-value factorization only. It does not yet prove simple roots of the quadratic, an exhaustive ramification divisor, degree, or finiteness of the scheme map.

9. Verification and remaining analytic bundling. Required: Hosted Lean and distinct review must precede proof acceptance, and local certificates must not be mislabeled as a bundled manifold theorem. Constructed: Two new modules are added to the unchanged54-source closure; the56-source packet has pending hosted status and a recursive audit source. Application: Structural and hash checks are not kernel validation. A ContMDiff statement for mapPoints/compactJ, q-disc composition order statements, full finite ramification and degree/finiteness remain next steps. No integral model through characteristic3, PEL/universal family or full318/326 theorem follows from this packet.

