# Preserve complete original bicanonical chart restrictions

Successor of `height-normalized-valuative-center-r68` at `57227e167abe49436d651b932ff75d5bdf9b5898`. Own hosted run43603177874 verifies FiveChartGeometry PASS13.899s and then BicanonicalRestrictions FAIL9.386s. The new failure consists of dependent open-image rewrite motives and missing IsOpenImmersion instances for the exact algebra-equivalence spectrum maps.

Two abstract helper theorems are added: route substitution before the original imageLE, and the native open-immersion instance for Spec.map of an algebra equivalence. They are specialized only inside the existing complete branch/infinity restriction proofs. All old statements, definitions, maps, full chart domains, coefficients, differentials, J² scaling, imports and options remain unchanged.

Exactly1 of96 modules changes,95 reused. Source review is not hosted compilation or whole-packet acceptance. No local Lean. Common observer tooling is separate and makes no production-source change.

## Nine application obligations
1. **required_inputs.** Required: Open-immersion instances attached to exact morphisms and complete chart route equalities. Constructed: Abstract imageLE_of_route substitutes the route target before applying original imageLE; spec_algEquiv_open supplies the exact native Spec.map instance. Justification: Handles proof dependency without replacing the morphism or adding geometry assumptions.

2. **constructed_objects.** Required: The same original tensor sheaf and J²-scaled global pair, actual integral branch and infinity formulas. Constructed: branchQ, infinityQ, originalQ, branch_route and infinity_route remain unchanged. Justification: Two exported abstract helper theorems added; no old theorem statement modified.

3. **index_and_domain_coverage.** Required: Every c, all four branch indices, both sections and the entire infinity chart. Constructed: Original full open-image inequalities and restriction conclusions preserved. Justification: No generic-point, smaller dense-open, selected root or reduced index family substituted.

4. **transition_maps.** Required: Exact algebra equivalences and their contravariant Spec maps; true presheaf restriction of differential tensor sections. Constructed: Each restriction installs the same map instance and calls unchanged weightedSquare_restrict_to with original route. Justification: No alternate scalar structure, chart isomorphism or normalization map.

5. **scalars_and_signs.** Required: Original J² and exact branch/infinity coefficients and universal differentials. Constructed: All coefficient and differential rewrites and section identities remain byte-identical. Justification: No unit assumption, factor cancellation or resource/limit change.

6. **consumer_identity.** Required: IntegralOriginalGlobalPair consumes these same weighted original restrictions. Constructed: Actual branch and infinity restriction statements unchanged, on their whole original chart domains. Justification: A helper proof transport is not replacement with coefficient equality alone.

7. **exceptional_cases.** Required: All original unit parameters and chart hypotheses, including both n cases. Constructed: No additional excluded point, denominator or genericity condition. Justification: No new axiom, admission, unchecked shortcut or scratch endpoint promoted.

8. **downstream_and_history.** Required: Own r68 run43603177874/head57227e and exact96-root predecessor. Constructed: FiveChartGeometry passes13.899s; BicanonicalRestrictions fails9.386s on exact dependent rewrite/instance errors. Justification: One of96 source files changes,95 exact reused; earlier passes are corroboration, not this candidate acceptance.

9. **verification_boundary.** Required: Independent source, current contract/propagation review and hosted kernel replay. Constructed: Exact own artifact/RESULT/log/before, primaries and independent source review retained; static checks only. Justification: No local Lean; full module, packet and arithmetic theorem unproved. Common diagnostic-only tooling stays separate.
