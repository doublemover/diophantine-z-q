# Genuine original normalized minor decay on an explicit polynomial scale

All 1278 predecessor Lean sources are exact. Five new sources, 297 lines, give 1283 total. No local Lean/profiling or resource increases. Distinct source review and hosted kernel validation remain pending.

For every smooth compact original W and nonzero kappa, a fixed K>=0 is produced such that for every integer n>=2:

N=n^8, B=n^32, delta=1/64, Q=ceil(B²/N)=n^56,
||minorArcIntegral(kappa,N,B,W) / B³|| <= K/n².

The exponent audit is explicit: H<=A n^32; expanded kernel <=D n^58; its square root <=sqrt(D)n^29; genuine fourth moment <=E n^65; actual full nonseparable weighted minor integral <=K n^94; B³=n^96. The divisor exponent is FIXED, chosen before n. The logarithm is bounded by log(n^56)=56log n<=56(n-1), not ignored. The same actual cutoff/scale satisfy (N+1)^3<=B and both tend to infinity. Shift n to n+2 and squeeze against K/(n+2)^2 to obtain the literal complex normalized minor integral tending to zero.

IMPORTANT LIMIT: this is a genuine minor-only decay sequence, not yet a simultaneous major+minor theorem. The old major-arc theorem selects an arbitrary-fast stageScale from its finite mass and derivative exponent. That sequence has NOT been identified with this polynomial one. Need quantitative finiteArcMass growth and a larger parameterized polynomial exponent, or an equivalent common-scale argument, before combining the two limits. No final prime/ray/order/Anchor/rank or quartic theorem follows here.
