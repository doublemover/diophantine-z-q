# Holomorphic exact j map and canonical cusp q-germs

Status: uncompiled inactive hosted-CI candidate. Distinct non-author source
review and hosted Lean checking remain pending. No local Lean build was run.

The first new module converts the existing exhaustive local analytic
representatives into ContMDiff at complex regularity omega, for the exact
scheme j action on genuine complex points with their original atlas. Its
composition with the original compact point biholomorphism proves the same
for compactJ. All chart transitions and local inverse identities are explicit.

The second module identifies the map on each actual selected q-disc, including
its origin, with the exact reciprocal target germ. It proves analyticity and
orders1 and3 at infinityEnd and zeroEnd respectively, through the independently
proved order-one endCoordinate. The output is the actual target chart applied
to compactJ(sourceDisc c q), not an unrelated auxiliary expression.

## Exact application contract

1. Existing complex-point structure. Required: Manifold holomorphy must use the independently defined original complex point topology and proved two-chart atlas. Constructed: ThreeJManifoldHolomorphy318 uses complexPointTopology, pointChartedSpace and point_isManifold unchanged; evaluationChart merely indexes those same original charts by Fin2. Application: evaluationChart_symm is exactly chartPoint i, its target is all C, and evaluationChart_maximal proves actual atlas membership. No arbitrary transported target structure replaces the prior algebraic evaluation atlas.

2. Exact local expression to manifold regularity. Required: A local expression must yield ContMDiffAt for the same map, at the same genuine scheme point. Constructed: contMDiffAt_of_expression consumes HasAnalyticChartExpression, composes the analytic scalar germ with the proved smooth target inverse chart, and uses eventual equality. Application: Both chart inverse directions are controlled: the source chart is smooth at the actual point, its value is exactly t, and its local inverse identity on the source neighborhood recovers mapPoints. Continuity is provided by these smooth compositions, not inferred from scheme construction.

3. All complex points and compact source identity. Required: The bundled theorem must cover the full actual point set and retain the exact compact source comparison. Constructed: mapPoints_contMDiff applies every_point_analytic; compactJ_contMDiff composes it with compactPointBiholomorph.contMDiff. Application: The latter has exactly compactPointHomeomorph as its underlying function and compactJ is the existing scheme-induced map. The prior source atlas has its independently established orbit and q-disc meaning. No replacement source or arbitrary homeomorphism is introduced.

4. Actual selected q-disc comparison. Required: The cusp formula must use each original selected q-disc, including its origin, not just the target sphere coordinate. Constructed: source_point_expression uses the total sourceDisc with its exact germ near0, actual filledParameter_disc and sphereChart_eq_inverse, then identifies pointHomeomorph of that inverse sphere chart with chartPoint(sourceIndex c). Application: The neighborhood is the original open disc containing0. For infinityEnd sourceIndex is0, for zeroEnd it is1. Pointwise equality includes the origin and retains the same actual End3 index and endCoordinate.

5. Composition analyticity and exact source orders. Required: Changing coordinates must preserve analytic meaning and have its order proved. Constructed: qGerm composes reciprocalPole or finitePole with the existing endCoordinate; qGerm_analytic uses its proved analytic germ and zero value. Application: endCoordinate_order is independently1 for every actual end. Polynomial numerators after composition remain analytic and nonzero at0. Meromorphic power and division theorems compute qGerm_order as1 or3 without assuming a general order-composition theorem.

6. Equality with exact scheme action on whole neighborhoods. Required: Analytic scalar formulas must be linked to the actual compact map on genuine q-disc neighborhoods. Constructed: qDisc_map_expression combines source_point_expression with exact finite/reciprocal numerator localization formulas. Application: Continuity of the analytic composed numerators gives nonvanishing on a whole neighborhood. Thus compactJ(sourceDisc c q) equals the actual chartPoint0(qGerm c q), including q=0; this is not only agreement on a punctured or generic subset.

7. Actual reciprocal target coordinate and order transfer. Required: The reported order must be that of the actual target-chart expression of the compact modular map. Constructed: actualQExpression applies evaluationChart0 to compactJ on sourceDisc. actualQExpression_eq uses the true inverse-chart identity to identify its germ with qGerm. Application: actual_q_germ transfers analyticity by neighborhood equality and meromorphic order by its punctured restriction. It is therefore a theorem about the actual coordinate expression, not merely an auxiliary rational function.

8. Cusp index coverage and named normalization. Required: Every actual cusp index must be covered and the named order conventions must match source and target coordinates. Constructed: actual_q_germ quantifies over all End3; source_point_expression consumes end_exhaustion; named_q_orders gives1 at infinityEnd and3 at zeroEnd. Application: Target coordinate0 is reciprocal j. Source infinityEnd uses reciprocal T and source zeroEnd uses T. All zero values and inverse-coordinate identifications are explicit, so no cusp labels or order signs are silently swapped.

9. Verification and remaining arithmetic boundary. Required: New bundled applications need primary API review, hosted Lean and distinct author review before acceptance. Constructed: Two new modules extend the unchanged56-source candidate. Primary ContMDiff atlas, composition/congruence and Diffeomorph definitions were read at the pinned commit. Application: Structural hashes and application checks are not kernel validation. Full finite elliptic ramification/divisor, degree/finiteness, PEL/universal-family realization, arithmetic descent and the full318/326 theorem remain separate. The retained characteristic-three base point still prevents claiming the same coordinate pair gives an everywhere-defined Z model.


## Hosted-failure revision

Hosted run42574563881 at2cdec4e passed ThreeProjectiveJCertificates318, then failed three ActualThreeJChartConsumer318 evaluations because aeval did not simplify numeral coefficients27 and243. Add explicit map_ofNat in those finite/reciprocal and boundary simplifications. Apply the same explicit rewrite to the two new ThreeJAnalyticGerms318 evaluations, which have the identical syntactic issue. The remaining56 sources are byte-identical to the prior58-source candidate; no new mathematical assumptions or conclusions are added. Neither repaired consumer nor the new holomorphy modules have been checked by Lean locally.

Exact failed RESULT and log are retained under previous-failure; every older
packet remains unchanged. Hosted checking and non-author review are pending.

## Point-factorization CI revision

Hosted run42574563881 at2cdec4e passed the first38 point-comparison modules, then exposed two exact ProjectiveLineFieldPoints318 errors: a docstring immediately preceding set_option was parsed as a malformed declaration, and the last Polynomial.aeval ring map lacked an explicit coefficient ring. Move the scoped4000000-heartbeat option before the theorem docstring and specify (R:=R) in the two aeval occurrences of every_point_in_chart. The budget remains bounded and theorem statements/mathematical arguments are unchanged. Other57 source modules remain byte-identical to holomorphic-r2, including its numeral-evaluation repairs.

Exact failed44-source evidence is retained under previous-points-failure.
The prior numeral-evaluation failure evidence is preserved as well. No Lean
was run locally. Hosted checking and non-author review remain pending.
