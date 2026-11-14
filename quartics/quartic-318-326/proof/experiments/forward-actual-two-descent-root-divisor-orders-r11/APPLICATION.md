# ScalarCompleteSource318: terminal singleton normalization in the full literal row assembly

## Observed scope and own evidence

Hosted run 43575728180 at d97d209a1666cdcb0d7ae2488523fbfa7d46fae6 verifies the prior ScalarActualInputs318 repair in both forward packets. Weighted r10 artifact14106736675 first fails ScalarCompleteSource318 (42.884s). The two hard errors at the final row tuple are exactly the terminal tails for r262 and r281: each still has type forall a : Row, a = r_i S implies a finalAssignment = 0, but the tuple needs the particular r_i S equation. The earlier warnings are not separately repaired. Descent r10 has its own artifact14107470193 and requires exact own RESULT/intake/digest comparison, not substitution of weighted evidence.

## Changed application and required input

CircuitReplay.Constraints is the original predicate requiring every row in the original list to vanish on one assignment. The existing simplification unfolds list membership into a right-associated conjunction using forall_eq_or_imp but leaves the terminal singleton universal for each block. The sole candidate change adds forall_eq to the final simp only list at hw', hs', hp and the goal. It specializes that terminal equality-bound universal, preserving logical equivalence and the same row equation; it does not assert, omit or weaken that equation. No earlier scalar proof, definition, statement or tuple projection changes.

## Full index coverage and exact constructed object

The full literal stage0 S has 288 ordered rows r0 through r287. The unchanged tuple assembles exactly263 projections from hw' (r0-r262), then19 from hs' (r263-r281), then6 from hp (r282-r287). A Python structural check compared every one of these288 existing projection terms against those exact complete block counts; this is coverage evidence, not arithmetic proof. Adding forall_eq makes the final terminal equations on all four sides explicit, including r287 on both hp and the full goal. The original ordering and all288 tuple terms remain byte-identical.

The assignment remains exactly finish S (ScalarForwardWitness318.fill w n) C A. The original finish updates its certificate/anchor slots and scalar auxiliary products exactly as before. hw' still transports the original first263 source rows through the same fill/finish preservation computation; hs' still comes from the existing scalar_rows using the same signed fixed root and nonzero hypotheses; hp still uses the same actual certificate and ternary-norm anchor. No row, gate polynomial, denominator, source assignment, projection or coefficient is changed.

## Hypotheses, scalars and exceptional cases

The theorem still quantifies over every rational S, original assignment w, integer n with n≠0 and n≠1, exact first263 constraints, square slot118, fixed signed root, original nonzero inputR/H/denominator conditions, Certificate at the original poleInput and Anchor with the same rational norm coefficients. Rational scalar conventions, the coefficient3 and ternary form x²+6y²−2z², input preservation, certificate signs and all exceptional exclusions remain unchanged. No extra satisfiability, chosen-row or omitted-gate assumption is introduced. All imports and inherited resource/transparency options are unchanged.

## Exact consumers

The same module's hasSolution_of_point directly consumes full_rows after constructing the original certificate from PointPair P and hb, and retains the same input-preserving finish/fill assignment. PreparedIntegerSource318.complete_at_index then directly consumes hasSolution_of_point at its line82 with the actual previously built assignment w, integer labels1, original point pair P₃', anchor A', guard-derived bounds and root identity. It concludes the same literal source system via the original input equality. These actual applications and their complete hypotheses are preserved as primary sources; no merely importing module is cited as the consumer.

## Review boundary

Before SHA256 a0f74e00bdd0be89dee1cac08d935908bb225610dba88d9564d9c99916a03323; candidate63fbd43e070d56cb63bdb73451602bb568c8ef175a577f0fa7fff87bfeb9781f. Each own ordered closure (1299/1304) is unchanged and only this one source changes in each. Distinct application/source and full propagation reviews are required; no local Lean/Lake run, candidate kernel acceptance, recursive-axiom audit, complete-source pass or full arithmetic theorem claim is made. Hosted elaboration remains pending.
