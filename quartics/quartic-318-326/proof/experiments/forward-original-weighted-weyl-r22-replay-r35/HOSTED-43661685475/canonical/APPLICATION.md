# Actual half-trace norm/valuation proof repair

Own weighted20 run43661685475 at58f3c3ea56040e8776debb9d9b7a6d12db76ac23. Isolated proof candidate, no active source edited and no local Lean/Lake. Native valuation API pinned to mathlib56a005855ea17e0b0958f73ec801ae140b0a1679.

1. Inputs: same arbitrary original quadratic element u:K and existing hn:normCoefficient u≠0. No new rational coefficient, nonzero coordinate, valuation or sign hypothesis.
2. Objects: the same original half-trace (u²).re and original normCoefficient/AnchorNorm.norm. A typed valuation-of-two equality and exact pair u.re u.im=u eta identity are produced locally, not assumed.
3. Coverage: full original quadratic field K=QuadraticAlgebra ℚ 2 0, same ramified2 equality and inert3 inequality. Existing branches u.re=0 and u.im=0 remain byte-identical and are not excluded.
4. Maps: unchanged original coordinate projections, original norm and actual half-trace. Native add_eq_min is explicitly instantiated at p=2,q=u.re²,r=2*u.im² so existing prime Fact2 resolves before elaborating the parity proof.
5. Factors: exact2 coefficient, odd1+2v2(im) versus even2v2(re), min norm formula, and exact inert3 factor2 are retained. Typed hself invokes native self at prime2 with the original numeral2 as a rational; no normalizing coefficient changes.
6. Consumer identity: both original norm_two_value and norm_three_value still apply to the actual rational coordinates. Local pair eta proves their literal pair is the same u, then the existing norm_coefficient equality identifies precisely the consumed norm, not an abstract isometric replacement.
7. Exceptional cases: zero coordinates, possible half-trace cancellation at3 and ramified opposite parity at2 follow the same original branches and nonvanishing proof. No restriction, alternative desired conclusion or extra local-global input.
8. Own evidence: current weighted20 RESULT/intake/log verified. TranslatedIndex now passes1.717s and IndexValuations1.467s; HalfTraceDepth fails1.517s after104 successful commands at uninstantiated self prime/cast, unresolved prime Fact and pair eta mismatches. Descent20 own current artifact is not yet bound here; any propagated sibling must bind its own receipt separately.
9. Verification boundary: public theorem types, imports, resource options and existing local Fact2/Fact3 instances remain unchanged. Only proof terms are made explicit. Source review, exact all-copy propagation and hosted acceptance are separate; no full arithmetic theorem, norm formula weakening, additional trust setting or local Lean is claimed.
